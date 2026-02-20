/-
  Tutorial 2: Deterministic and Non-Deterministic Finite Automata
  Course: Language and Computation (COMP2012)
  TA: Aref Mohammadzadeh
  Date: 12 February 2026
-/


import Proofs.Lang
import Proofs.Autom
import Mathlib.Data.Fintype.Basic

open Lang Dfa DFA Nfa NFA Lang.Examples SigmaABC

namespace Recap_dfa
/-!
    ## SECTION 1: RECAP

    A **Deterministic Finite Automaton (DFA)** over an alphabet `Sigma` is defined by:
    - `Q` : A set of States.
    - `s` : The Initial state (`s : Q`).
    - `F` : A set of Final states (`F : Finset Q`).
    - `δ` : The Transition function (`Q → Sigma → Q`).


    To process a word, we extend the single-step transition `δ` to
    a multi-step function `δ_star`.
  -/

  variable {Sigma : Type}[Alphabet Sigma]
  variable (A : DFA Sigma)

  -- The extended transition function processes a word.
  def δ_star : A.Q → Word Sigma → A.Q
  | q , [] => q
  | q , (x :: w) => δ_star (A.δ q x) w

  /-
    The **Language** accepted by an automaton `A` is simply the set of all words
    that lead from the start state `s` to one of the final states in `F`:

    `{ w | δ_star A A.s w ∈ A.F }`
  -/

end Recap_dfa


namespace Tutorial2

/-!
  ## SECTION 2: DFA EXERCISES
-/

-- Q1:
-- Define a DFA that accepts words ending in "ab".
namespace DFA_Ex1
  inductive Q : Type | q0 | q1 | q2
  deriving Fintype, DecidableEq
  open Q

  abbrev A_end_ab_dfa : DFA SigmaABC :=
    {
      Q := Q
      s := q0
      F := { q2 }
      δ := λ
        | q0, a => q1  -- Saw 'a', start hope
        | q0, _ => q0  -- Saw 'b' or 'c', stay at start
        | q1, b => q2  -- Saw 'ab', success!
        | q1, a => q1  -- Saw 'aa', still have hope
        | q1, c => q0  -- Saw 'ac', failed, reset
        | q2, a => q1  -- Saw 'aba', we have an 'a' at the end now
        | q2, _ => q0  -- Saw 'abb' or 'abc', reset
    }

  example : [c, a, b] ∈ L A_end_ab_dfa := by simp [Dfa.L, Dfa.δ_star]
  example : [a, b, a] ∉ L A_end_ab_dfa := by simp [Dfa.L, Dfa.δ_star]
end DFA_Ex1


-- Q2:
-- Define a DFA that accepts binary words with an ODD number of '1's.
namespace DFA_Ex2
  inductive Q : Type | even | odd
  deriving Fintype, DecidableEq
  open Q

  abbrev A_parity : DFA SigmaBin :=
    {
      Q := Q
      s := even
      F := { odd }
      δ := λ
        | even, 0 => even
        | even, 1 => odd
        | odd, 0  => odd
        | odd, 1  => even
        | _, _ => even
    }

  example : [1, 0, 0] ∈ L A_parity := by simp [Dfa.L, Dfa.δ_star]
end DFA_Ex2


-- Q3:
-- Define a DFA that accepts words that DO NOT contain "00".
namespace DFA_Ex3
  inductive Q : Type | safe | seen0 | dead
  deriving Fintype, DecidableEq
  open Q

  abbrev A_no00 : DFA SigmaBin :=
    {
      Q := Q
      s := safe
      F := { safe, seen0 }
      δ := λ
        | safe, 0 => seen0
        | safe, 1 => safe
        | seen0, 0 => dead
        | seen0, 1 => safe
        | dead, _ => dead
    }

  example : [1, 0, 1] ∈ L A_no00 := by simp [Dfa.L, Dfa.δ_star]
  example : [0, 0] ∉ L A_no00 := by simp [Dfa.L, Dfa.δ_star]
end DFA_Ex3


-- Q4:
-- Define a DFA that accepts words containing the substring "ac".
namespace DFA_Ex4
  inductive Q : Type | q0 | q1 | q2
  deriving Fintype, DecidableEq
  open Q

  abbrev A_has_ac : DFA SigmaABC :=
    {
      Q := Q
      s := q0
      F := { q2 }
      δ := λ
        | q0, a => q1
        | q0, _ => q0
        | q1, c => q2 -- Found it!
        | q1, a => q1 -- 'aa' -> still have 'a'
        | q1, b => q0 -- 'ab' -> reset
        | q2, _ => q2 -- Trap state (success)
    }

  example : [b, a, c, b] ∈ L A_has_ac := by simp [Dfa.L, Dfa.δ_star]
end DFA_Ex4


/-!
  ## SECTION 3: NFA EXERCISES
  -/
namespace recap_nfa
 /-
    A **Nondeterministic Finite Automaton (NFA)** extends the DFA concept by
    allowing multiple (or zero) transitions for the same symbol. An NFA consists of:

    - `Q` : A set of States.
    - `S` : A *set* of Initial states (`S : Finset Q`).
    - `F` : A set of Final states.
    - `δ` : The Transition function (`Q → Sigma → Pow Q`).



    **Intuition:** While a DFA follows a single path, an NFA follows *all* possible
    transitions in `δ` concurrently. If *any* of those paths end in a final state,
    the word is accepted.
  -/
    variable {Sigma : Type}[Alphabet Sigma]

  variable (A : NFA Sigma)

  -- Helper: One step from a SET of states
  -- (The union of all states reachable from any state in S by reading x)
  def δ_step (S : Finset A.Q) (x : Sigma) : Finset A.Q :=
    S.biUnion (λ q => A.δ q x)

  -- We extend this to process a whole word:
  def δ_star_nfa : Finset A.Q → Word Sigma → Finset A.Q
  | S, [] => S
  | S, (x :: w) => δ_star_nfa (δ_step A S x) w

  -- The language of an NFA is the set of words where the final set of states
  -- overlaps with the accepting states F:
  def L_nfa := { w | (δ_star_nfa A A.S w ∩ A.F).Nonempty }

  --
end recap_nfa



-- Q1:
-- Define an NFA that accepts words ending in "ab".
/-
  *Comparison:* Notice how much simpler Q1 is here compared to the DFA version.
  We don't need to define transitions for every symbol, and we don't need
  to "reset" manually—the non-determinism handles the "guessing".

-/

namespace NFA_Ex1
  inductive Q : Type | q0 | q1 | q2
  deriving Fintype, DecidableEq
  open Q

  abbrev A_end_ab_nfa : NFA SigmaABC :=
    {
      Q := Q
      S := { q0 }
      F := { q2 }
      δ := λ
        | q0, a => { q0, q1 } -- Stay OR guess this 'a' is the start of 'ab'
        | q0, _ => { q0 }     -- Stay waiting
        | q1, b => { q2 }     -- Finish pattern
        | _, _ => {}          -- All other paths die
    }

    /-
  NOTE ON "DEAD" PATHS:
  You might wonder: "If we have a word like 'cabcab', does the machine die after the first 'ab'?"

  It is okay because the NFA runs multiple "threads" at once:
  1. Input "ab...": One path reaches q2 (success!), but the q0 path is ALSO still running.
  2. Input "...c...": The path at q2 dies (goes to empty set) because q2 has no moves for 'c'.
  3. However, the path at q0 survives (q0 --c--> q0).

  So, even though the "success" thread for the first 'ab' dies when it sees 'c',
  the "waiting" thread at q0 continues and successfully catches the second 'ab'.
-/

  example : [c, a, b] ∈ L A_end_ab_nfa := by simp [Nfa.L, Nfa.δ_star, δ_step]
  end NFA_Ex1



-- Q2:
-- Define an NFA accepting words that start with 'a' OR start with 'c'.
namespace NFA_Ex2
  inductive Q : Type | q0 | q1
  deriving Fintype, DecidableEq
  open Q

  abbrev A_union : NFA SigmaABC :=
    {
      Q := Q
      S := { q0 }
      F := { q1 }
      δ := λ
        | q0, a => { q1}
        | q0, c => { q1}
        | q0, b => {}         -- 'b' dies immediately
        | q1, _  => { q1 }    -- Accept anything after
    }

  example : [c, b, b] ∈ L A_union := by simp [Nfa.L, Nfa.δ_star, δ_step]
  example : [b, a, a] ∉ L A_union := by simp [Nfa.L, Nfa.δ_star, δ_step]
end NFA_Ex2


-- Q3:
-- Define an NFA accepting words containing "101".
namespace NFA_Ex3
  inductive Q : Type | q0 | q1 | q2 | q3
  deriving Fintype, DecidableEq
  open Q

  abbrev A_has101 : NFA SigmaBin :=
    {
      Q := Q
      S := { q0 }
      F := { q3 }
      δ := λ
        | q0, 0 => { q0 }
        | q0, 1 => { q0, q1 }
        | q1, 0 => { q2 }
        | q2, 1 => { q3 }
        | q3, _ => { q3 }
        | _, _ => {}
    }

  example : [0, 1, 0, 1, 0] ∈ L A_has101 := by simp [Nfa.L, Nfa.δ_star, δ_step]; decide
end NFA_Ex3



/- Challenge!
Thought Experiment:
  Is there any DFA or NFA for the following language?
  (The set of words with n 'a's followed by exactly n 'b's: ε, ab, aabb, aaabbb...)
-/
def L_anbn : Lang SigmaABC :=
  { w | ∃ n : ℕ, w = a ^ n ++ b ^ n }

/-
  **Answer:** No.

  Both DFAs and NFAs have a *finite* number of states (memory).
  To recognize $a^n b^n$, the machine would need to "count" how many 'a's it has seen
  to match them with the same number of 'b's. Since $n$ can be arbitrarily large,
  a machine with finite states cannot store this count.

-/

end Tutorial2
