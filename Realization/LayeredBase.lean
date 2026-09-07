/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Realization.Splice

set_option autoImplicit false
set_option linter.style.header false

namespace Brualdi.Ledger

variable {V : Type*} [DecidableEq V]

/-- Two layer indices are equal or consecutive in the chain. -/
def SameOrConsecutive {k : ℕ} (i j : Fin k) : Prop :=
  i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val

/--
The as-printed layered-base hypotheses, phrased for an abstract graph with a finite chain
of vertex blocks.  The matching field stores the size-five consecutive interface matching
in the same form consumed by `twoBlock_splice`.
-/
structure LayeredBaseHypotheses (G : SimpleGraph V) {k : ℕ} (L : Fin k → Set V) where
  two_le : 2 ≤ k
  cover : ∀ v : V, ∃ i : Fin k, v ∈ L i
  disjoint : ∀ {i j : Fin k}, i ≠ j → Disjoint (L i) (L j)
  edge_layered :
    ∀ {x y : V}, G.Adj x y →
      ∀ {i j : Fin k}, x ∈ L i → y ∈ L j → SameOrConsecutive i j
  hamConnected : ∀ i : Fin k, IsHamConnected (G.induce (L i))
  flexible2DPC3 : ∀ i : Fin k, FlexiblePaired2DPC3 (G.induce (L i))
  interface :
    ∀ i j : Fin k, i.val + 1 = j.val → ConnectorMatching5 G (L i) (L j)

/--
The target layered-base lemma as a proposition, intentionally not claimed below.
The checked facts in this file stop at the two-block case and the TS step, because the
left-to-right iteration would require a `FlexiblePaired2DPC3` proof for the already-spliced
prefix.
-/
def LayeredBaseLemmaStatement (G : SimpleGraph V) : Prop :=
  ∀ {k : ℕ} (L : Fin k → Set V), LayeredBaseHypotheses G L → IsHamConnected G

/-- The genuine two-layer instance is exactly `twoBlock_splice`. -/
theorem layeredBase_two_blocks {G : SimpleGraph V} {L : Fin 2 → Set V}
    (h : LayeredBaseHypotheses G L) : IsHamConnected G := by
  classical
  refine twoBlock_splice (G := G) (A := L 0) (B := L 1) ?_ ?_
    (h.hamConnected 0) (h.hamConnected 1)
    (h.flexible2DPC3 0) (h.flexible2DPC3 1)
    (h.interface 0 1 (by norm_num))
  · intro v
    rcases h.cover v with ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · exact h.disjoint (by decide)

/--
The TS iteration step.  In a left-to-right layered induction, `A` is the accumulated prefix
and `B` is the next layer.  The `hAP3` parameter is the missing invariant: `twoBlock_splice`
produces `IsHamConnected G`, but it does not produce `FlexiblePaired2DPC3 (G.induce A)`.
-/
theorem layeredBase_TS_step {G : SimpleGraph V} {A B : Set V}
    (hcover : ∀ v : V, v ∈ A ∨ v ∈ B) (hAB : Disjoint A B)
    (hA : IsHamConnected (G.induce A)) (hB : IsHamConnected (G.induce B))
    (hAP3 : FlexiblePaired2DPC3 (G.induce A))
    (hBP3 : FlexiblePaired2DPC3 (G.induce B))
    (M : ConnectorMatching5 G A B) :
    IsHamConnected G :=
  twoBlock_splice hcover hAB hA hB hAP3 hBP3 M

#print axioms layeredBase_two_blocks
#print axioms layeredBase_TS_step

end Brualdi.Ledger
