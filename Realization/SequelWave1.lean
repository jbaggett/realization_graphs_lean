/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import Realization.DodgeCore
import Realization.PathCriterion

/-!
# Sequel wave 1: exchange ports and honest open statements

This file separates proved exchange consequences from the statements that
still require the Ferrers-cycle, extreme-direction, or integrality arguments.
The latter are definitions of propositions, not axioms.
-/

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Brualdi.RealizationGraph.SequelWave1

open BoundedComposition

/-! ## Port saturation from symmetric exchange -/

/-- The exact two-sided exchange property used by the port-saturation proof.
It is a property of a finite set, not a global axiom. -/
def StrongUnitExchange {s : ℕ} (L : Finset (Fin s → ℕ)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∀ i, x i < y i →
    ∃ j x' y', x' ∈ L ∧ y' ∈ L ∧
      DirectedTransfer x x' i j ∧ DirectedTransfer y' y i j

def CoordinateMinimum {s : ℕ} (L : Finset (Fin s → ℕ))
    (i : Fin s) (x : Fin s → ℕ) : Prop :=
  x ∈ L ∧ ∀ y ∈ L, x i ≤ y i

def CoordinateMaximum {s : ℕ} (L : Finset (Fin s → ℕ))
    (i : Fin s) (x : Fin s → ℕ) : Prop :=
  x ∈ L ∧ ∀ y ∈ L, y i ≤ x i

def CoordinateActive {s : ℕ} (L : Finset (Fin s → ℕ)) (i : Fin s) : Prop :=
  ∃ x ∈ L, ∃ y ∈ L, x i ≠ y i

theorem minimum_port_saturation {s : ℕ} {L : Finset (Fin s → ℕ)}
    (hex : StrongUnitExchange L) {i : Fin s} {x : Fin s → ℕ}
    (hmin : CoordinateMinimum L i x) (hactive : CoordinateActive L i) :
    ∃ x' ∈ L, UnitTransfer x x' ∧ x' i = x i + 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := hactive
  have hxu := hmin.2 u hu
  have hxv := hmin.2 v hv
  have hlt : x i < u i ∨ x i < v i := by omega
  rcases hlt with hlt | hlt
  · obtain ⟨j, x', _, hx'L, _, hx', _⟩ := hex x hmin.1 u hu i hlt
    exact ⟨x', hx'L, Or.inl ⟨i, j, hx'⟩, hx'.2.1⟩
  · obtain ⟨j, x', _, hx'L, _, hx', _⟩ := hex x hmin.1 v hv i hlt
    exact ⟨x', hx'L, Or.inl ⟨i, j, hx'⟩, hx'.2.1⟩

theorem maximum_port_saturation {s : ℕ} {L : Finset (Fin s → ℕ)}
    (hex : StrongUnitExchange L) {i : Fin s} {x : Fin s → ℕ}
    (hmax : CoordinateMaximum L i x) (hactive : CoordinateActive L i) :
    ∃ x' ∈ L, UnitTransfer x x' ∧ x i = x' i + 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := hactive
  have hux := hmax.2 u hu
  have hvx := hmax.2 v hv
  have hlt : u i < x i ∨ v i < x i := by omega
  rcases hlt with hlt | hlt
  · obtain ⟨j, _, x', _, hx'L, _, hx'⟩ := hex u hu x hmax.1 i hlt
    exact ⟨x', hx'L, Or.inr ⟨i, j, hx'⟩, hx'.2.1⟩
  · obtain ⟨j, _, x', _, hx'L, _, hx'⟩ := hex v hv x hmax.1 i hlt
    exact ⟨x', hx'L, Or.inr ⟨i, j, hx'⟩, hx'.2.1⟩

/-! ## Concrete statements retained without axioms -/

/-- Transfer graph induced on one coordinate slice. -/
noncomputable def sliceTransferGraph {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) (i : Fin s) (t : ℕ) :
    SimpleGraph {x // x ∈ slice c r m i t} where
  Adj x y := UnitTransfer x.1 y.1
  symm := ⟨fun _ _ ↦ unitTransfer_symm⟩
  loopless := ⟨fun x ↦ unitTransfer_irrefl x.1⟩

def InternalInSlice {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m : Fin s → ℕ)
    (i : Fin s) (x : Fin s → ℕ) : Prop :=
  ∃ y ∈ slice c r m i (x i), ∃ z ∈ slice c r m i (x i),
    y ≠ z ∧ UnitTransfer x y ∧ UnitTransfer x z

/-- Definition 4.1 from `trace_conjecture.md`. -/
def ExtremePathBad {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m x : Fin s → ℕ)
    (i : Fin s) : Prop :=
  x ∈ filter c r m ∧ Active c r m i ∧
    (x i = lowerEndpoint c m i ∨ x i = upperEndpoint c m i) ∧
    IsPathGraph (sliceTransferGraph c r m i (x i)) ∧
    InternalInSlice c r m i x

/-- Exact formal statement of Theorem 4.3.  Wave 1 records it without
declaring a theorem or an axiom. -/
noncomputable def Theorem43Statement {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : Prop := by
  classical
  exact ∀ x, (Finset.univ.filter fun i ↦ ExtremePathBad c r m x i).card ≤ 1

/-- Both directions of the requested path criterion.  Wave 1 proves the
forward implication as `isPathGraph_of_effectiveDimension_le_two`; the
reverse implication remains represented here as part of the statement. -/
def PathCriterionStatement {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m : Fin s → ℕ) : Prop :=
  IsPathGraph (transferGraph c r m) ↔ effectiveDimension c r m ≤ 2

/-- A prefix-threshold predicate on the concrete filter. -/
abbrev Threshold {s : ℕ} := Fin (s + 1) × ℕ

def ThresholdHolds {s : ℕ} (T : Threshold (s := s)) (x : Fin s → ℕ) : Prop :=
  T.2 ≤ prefixSum x T.1

def ThresholdNontrivial {s : ℕ} (L : Finset (Fin s → ℕ))
    (T : Threshold (s := s)) : Prop :=
  (∃ x ∈ L, ThresholdHolds T x) ∧ ∃ y ∈ L, ¬ ThresholdHolds T y

def ThresholdImplies {s : ℕ} (L : Finset (Fin s → ℕ))
    (T U : Threshold (s := s)) : Prop :=
  ∀ x ∈ L, ThresholdHolds T x → ThresholdHolds U x

/-- The unfolded concrete replacement for “an antichain of three
join-irreducibles”: three nontrivial prefix thresholds, pairwise
incomparable by implication on the filter. -/
def HasThreeThresholdAntichain {s : ℕ} (L : Finset (Fin s → ℕ)) : Prop :=
  ∃ T₁ T₂ T₃, T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₂ ≠ T₃ ∧
    ThresholdNontrivial L T₁ ∧ ThresholdNontrivial L T₂ ∧ ThresholdNontrivial L T₃ ∧
    ¬ ThresholdImplies L T₁ T₂ ∧ ¬ ThresholdImplies L T₂ T₁ ∧
    ¬ ThresholdImplies L T₁ T₃ ∧ ¬ ThresholdImplies L T₃ T₁ ∧
    ¬ ThresholdImplies L T₂ T₃ ∧ ¬ ThresholdImplies L T₃ T₂

/-- Concrete width-three-to-four statement, retained as a proposition. -/
def WidthForcesFourStatement {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : Prop :=
  HasThreeThresholdAntichain (filter c r m) → 4 ≤ effectiveDimension c r m

def HasNonPathSlice {s : ℕ} (c : Fin s → ℕ) (r : ℕ) (m : Fin s → ℕ)
    (i : Fin s) : Prop :=
  ∃ t ∈ attainedRange c r m i, ¬ IsPathGraph (sliceTransferGraph c r m i t)

/-- Local interior-section hypothesis.  It is deliberately a theorem
parameter, not an axiom. -/
def InteriorSliceHypothesis {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : Prop :=
  ∀ i, Active c r m i → lowerEndpoint c m i + 1 < upperEndpoint c m i →
    ¬ IsPathGraph (sliceTransferGraph c r m i (lowerEndpoint c m i + 1))

/-- The remaining binary-face input, also explicit and local. -/
def BinarySliceHypothesis {s : ℕ} (c : Fin s → ℕ) (r : ℕ)
    (m : Fin s → ℕ) : Prop :=
  ∀ i, Active c r m i → lowerEndpoint c m i + 1 = upperEndpoint c m i →
    ¬ IsPathGraph (sliceTransferGraph c r m i (lowerEndpoint c m i)) ∨
      ¬ IsPathGraph (sliceTransferGraph c r m i (upperEndpoint c m i))

/-- Honest conditional assembly of the Buffer conclusion. -/
theorem hasNonPathSlice_of_local_hypotheses {s : ℕ} {c m : Fin s → ℕ} {r : ℕ}
    (hm : Feasible c r m m) (hint : InteriorSliceHypothesis c r m)
    (hbinary : BinarySliceHypothesis c r m) {i : Fin s}
    (hi : Active c r m i) : HasNonPathSlice c r m i := by
  have hlt := active_iff_endpoint_lt hm i |>.mp hi
  rcases lt_or_eq_of_le (by omega : lowerEndpoint c m i + 1 ≤ upperEndpoint c m i) with h | h
  · refine ⟨lowerEndpoint c m i + 1, ?_, hint i hi h⟩
    rw [attainedRange_eq_Icc hm i, Finset.mem_Icc]
    omega
  · rcases hbinary i hi h with hlo | hhi
    · refine ⟨lowerEndpoint c m i, ?_, hlo⟩
      rw [attainedRange_eq_Icc hm i, Finset.mem_Icc]
      omega
    · refine ⟨upperEndpoint c m i, ?_, hhi⟩
      rw [attainedRange_eq_Icc hm i, Finset.mem_Icc]
      omega

#print axioms minimum_port_saturation
#print axioms maximum_port_saturation
#print axioms hasNonPathSlice_of_local_hypotheses

end Brualdi.RealizationGraph.SequelWave1
