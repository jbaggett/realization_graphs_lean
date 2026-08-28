/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.RealizationGraph.QuotientAdjacency
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Hall

/-!
# The interface: witness counts, the signed identity, and the cross-degree theorem (§5.4)

This module mechanizes manuscript §5.4: the two cross-interface witness identities (Theorem 5.6),
their constant signed edge-degree corollary, the cross-degree theorem 5.7 with its chain 5.7a–5.7d,
and exact colour expansion (Theorem 5.8). These are what §9's `ord` and `obi` consume.

**On the file's name, and on the four declarations at the end of it.** It is called
`InterfaceSaturation` and its header said *"Interface saturation (E3-sat)"* until 2026-08-24, because
it was created for the **superseded** matroid/base route, whose obligation `E3-sat` was *every base
interface has a matching saturating its smaller side*. That route's modules were parked in
`ParkedBaseStructure` on 2026-08-20 and the manuscript does not take it.

What survives here from it is real, and **nothing on the main theorem's cone reaches any of it**:
`edge_component_biregular`, `edgeFreeComponent_support_eq_singleton` and `biregular_matching` — the
last being E3-sat's statement in general form, still carrying its old *"Item 5"* label — together with
`leftPart`/`rightPart`, which those three do consume internally. (An earlier draft of this paragraph
said the group is "consumed by nothing", which is false of `leftPart`/`rightPart`; corrected the same
day by an adversary reading it.) §5.4 of the
manuscript says so in as many words: *"A constant edge-difference makes the connector graph biregular
on every component carrying an edge. **We record that and do not use it**"* — the one-sided bounds §9
needs must cover a realization with no connector at all, which biregularity is silent about, and they
come from Theorem 5.6 one realization at a time.

⚠ `biregular_matching` **is** among the 115 audited declarations (`compute/AxiomBaseline.lean`), so the
audited surface contains at least one declaration that nothing on the main theorem's cone reaches.
That is the safe direction — an extra traced declaration, not a missing one — but it is worth knowing
before anyone reads the 115 as "the declarations Theorem 10.1 rests on". Compare §5.6 of the trust
surface, which records the opposite case: the prism declarations are load-bearing and are *not* among
the 115.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

open Function
open scoped BigOperators
open scoped symmDiff

namespace Brualdi.RealizationGraph

universe u v

/-! ## The two witness-count identities -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The cross-interface witnesses from `a` toward `b` in a graph `G`:
`N_G(a) \ (N_G(b) ∪ {b})`. -/
noncomputable def interfaceWitnessSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : Finset V :=
  G.neighborFinset a \ insert b (G.neighborFinset b)

/-- The number `w_ab(G)` of cross-interface witnesses. -/
noncomputable def interfaceWitnessCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : ℕ :=
  (interfaceWitnessSet G a b).card

private theorem interfaceWitnessSet_eq_erased_sdiff
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    interfaceWitnessSet G a b =
      (G.neighborFinset a).erase b \ (G.neighborFinset b).erase a := by
  ext x
  simp only [interfaceWitnessSet, Finset.mem_sdiff, Finset.mem_insert,
    SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨hax, hxnot⟩
    refine ⟨⟨?_, hax⟩, ?_⟩
    · exact fun h => hxnot (Or.inl h)
    · intro h
      exact hxnot (Or.inr h.2)
  · rintro ⟨⟨hxb, hax⟩, hx⟩
    refine ⟨hax, ?_⟩
    rintro (rfl | hbx)
    · exact hxb rfl
    · exact hx ⟨fun h => G.irrefl (h ▸ hax), hbx⟩

/-- Identity 1 for an arbitrary finite simple graph, before replacing its degrees by a
prescribed realization function. Differences are in `ℤ`, since their signs matter. -/
theorem interfaceWitness_difference (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    (interfaceWitnessCount G a b : ℤ) - interfaceWitnessCount G b a =
      (G.degree a : ℤ) - G.degree b := by
  classical
  let A := (G.neighborFinset a).erase b
  let B := (G.neighborFinset b).erase a
  have hAcard : A.card = G.degree a - if G.Adj a b then 1 else 0 := by
    dsimp [A]
    by_cases h : G.Adj a b
    · rw [Finset.card_erase_of_mem]
      · simp [SimpleGraph.card_neighborFinset_eq_degree, h]
      · simpa [SimpleGraph.mem_neighborFinset] using h
    · rw [Finset.erase_eq_of_notMem]
      · simp [SimpleGraph.card_neighborFinset_eq_degree, h]
      · simpa [SimpleGraph.mem_neighborFinset] using h
  have hBcard : B.card = G.degree b - if G.Adj a b then 1 else 0 := by
    dsimp [B]
    by_cases h : G.Adj a b
    · rw [Finset.card_erase_of_mem]
      · simp [SimpleGraph.card_neighborFinset_eq_degree, h]
      · simpa [SimpleGraph.mem_neighborFinset] using h.symm
    · rw [Finset.erase_eq_of_notMem]
      · simp [SimpleGraph.card_neighborFinset_eq_degree, h]
      · simpa [SimpleGraph.mem_neighborFinset] using fun hba => h hba.symm
  have hleft := Finset.card_sdiff_add_card_inter A B
  have hright := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at hright
  simp only [interfaceWitnessCount, interfaceWitnessSet_eq_erased_sdiff]
  change ((A \ B).card : ℤ) - (B \ A).card = _
  by_cases h : G.Adj a b
  · have ha : 0 < G.degree a := h.degree_pos_left
    have hb : 0 < G.degree b := h.symm.degree_pos_left
    simp [h] at hAcard hBcard
    omega
  · simp [h] at hAcard hBcard
    omega

/-- Identity 1 in the paper's realization notation:
`w_ab(F) - w_ba(F) = f(a) - f(b)`. -/
theorem interface_identity_one {f : V → ℕ} (F : Realization f) (a b : V) :
    (interfaceWitnessCount F.graph a b : ℤ) - interfaceWitnessCount F.graph b a =
      (f a : ℤ) - f b := by
  have h := interfaceWitness_difference F.graph a b
  rw [F.degree_eq a, F.degree_eq b] at h
  exact h

/-- Under the transfer `ca → cb`, the reverse witness set is obtained by adjoining the
new witness `c`. This is the set-level form of Identity 2. -/
theorem interface_transfer_witnessSet (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c : V} (hca : G.Adj c a) (hcb : ¬ G.Adj c b) (hab : a ≠ b) (hbc : b ≠ c) :
    interfaceWitnessSet (transferGraph G a b c) b a =
      insert c (interfaceWitnessSet G b a) := by
  classical
  have hac : G.Adj a c := hca.symm
  have hbcAdj : ¬ G.Adj b c := fun h => hcb h.symm
  rw [interfaceWitnessSet, transferGraph_neighborFinset_y
    (G := G) (x := a) hbcAdj hab hbc,
    transferGraph_neighborFinset_x (G := G) (y := b) hac hbcAdj hab]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
    SimpleGraph.mem_neighborFinset]
  by_cases hxc : x = c
  · subst x
    simp [hca.ne]
  · simp [interfaceWitnessSet, hxc]

/-- Identity 2: for `H = F - ca + cb`, `w_ba(H) = w_ba(F) + 1`. -/
theorem interface_identity_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c : V} (hca : G.Adj c a) (hcb : ¬ G.Adj c b) (hab : a ≠ b) (hbc : b ≠ c) :
    interfaceWitnessCount (transferGraph G a b c) b a =
      interfaceWitnessCount G b a + 1 := by
  classical
  have hcnot : c ∉ interfaceWitnessSet G b a := by
    intro hc
    have hbc' : G.Adj b c := by
      simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp hc).1
    exact hcb hbc'.symm
  simp [interfaceWitnessCount, interface_transfer_witnessSet G hca hcb hab hbc, hcnot]

/-- The interface-edge degree corollary:
`w_ab(F) - w_ba(H) = f(a) - f(b) - 1`. -/
theorem interface_edge_degree_difference {f : V → ℕ} (F : Realization f)
    {a b c : V} (hca : F.graph.Adj c a) (hcb : ¬ F.graph.Adj c b)
    (hab : a ≠ b) (hbc : b ≠ c) :
    (interfaceWitnessCount F.graph a b : ℤ) -
        interfaceWitnessCount (transferGraph F.graph a b c) b a =
      (f a : ℤ) - f b - 1 := by
  have h1 := interface_identity_one F a b
  have h2 := interface_identity_two F.graph hca hcb hab hbc
  omega

/-! ## Components of a finite bipartite incidence graph -/

namespace BipartiteInterface

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable (R : A → B → Prop)
variable [∀ a b, Decidable (R a b)]

/-- The simple graph associated to a bipartite incidence relation. Using `A ⊕ B` makes the
two parts exhaustive even in the presence of isolates. -/
def graph : SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inr b => R a b
    | Sum.inr b, Sum.inl a => R a b
    | _, _ => False
  symm := by
    constructor
    rintro (a | b) (a' | b') h <;> simp_all
  loopless := by
    constructor
    rintro (a | b) h <;> simp_all

/-- Degree on the `A` side of a finite bipartite incidence graph. -/
noncomputable def leftDegree (a : A) : ℕ := by
  classical
  exact (Finset.univ.filter (R a)).card

/-- Degree on the `B` side of a finite bipartite incidence graph. -/
noncomputable def rightDegree (b : B) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a => R a b)).card

/-- The `A`-part of a connected component. -/
noncomputable def leftPart (C : (graph R).ConnectedComponent) : Finset A := by
  classical
  exact Finset.univ.filter fun a => Sum.inl a ∈ C.supp

/-- The `B`-part of a connected component. -/
noncomputable def rightPart (C : (graph R).ConnectedComponent) : Finset B := by
  classical
  exact Finset.univ.filter fun b => Sum.inr b ∈ C.supp

private noncomputable def potential (delta : ℤ) : A ⊕ B → ℤ
  | Sum.inl a => leftDegree R a
  | Sum.inr b => rightDegree R b + delta

private theorem potential_eq_of_adj {delta : ℤ}
    (hedge : ∀ a b, R a b → (leftDegree R a : ℤ) - rightDegree R b = delta)
    {x y : A ⊕ B} (hxy : (graph R).Adj x y) :
    potential R delta x = potential R delta y := by
  rcases x with a | b
  · rcases y with a' | b'
    · simp [graph] at hxy
    · simp only [potential]
      have h := hedge a b' hxy
      omega
  · rcases y with a' | b'
    · simp only [potential]
      have h := hedge a' b hxy
      omega
    · simp [graph] at hxy

private theorem potential_eq_of_reachable {delta : ℤ}
    (hedge : ∀ a b, R a b → (leftDegree R a : ℤ) - rightDegree R b = delta)
    {x y : A ⊕ B} (hxy : (graph R).Reachable x y) :
    potential R delta x = potential R delta y := by
  rw [SimpleGraph.reachable_eq_reflTransGen] at hxy
  induction hxy with
  | refl => rfl
  | tail _hreach hadj ih => exact ih.trans (potential_eq_of_adj R hedge hadj)

private theorem left_restricted_degree (C : (graph R).ConnectedComponent) {a : A}
    (ha : a ∈ leftPart R C) :
    ((rightPart R C).bipartiteAbove R a).card = leftDegree R a := by
  classical
  apply congrArg Finset.card
  ext b
  simp only [Finset.mem_bipartiteAbove, rightPart, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · exact fun h => h.2
  · intro hab
    refine ⟨?_, hab⟩
    have hain : Sum.inl a ∈ C.supp := by simpa [leftPart] using ha
    exact ((SimpleGraph.ConnectedComponent.mem_supp_congr_adj C
      (show (graph R).Adj (Sum.inl a) (Sum.inr b) from hab))).mp hain

private theorem right_restricted_degree (C : (graph R).ConnectedComponent) {b : B}
    (hb : b ∈ rightPart R C) :
    ((leftPart R C).bipartiteBelow R b).card = rightDegree R b := by
  classical
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_bipartiteBelow, leftPart, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · exact fun h => h.2
  · intro hab
    refine ⟨?_, hab⟩
    have hbin : Sum.inr b ∈ C.supp := by simpa [rightPart] using hb
    exact ((SimpleGraph.ConnectedComponent.mem_supp_congr_adj C
      (show (graph R).Adj (Sum.inr b) (Sum.inl a) from hab))).mp hbin

/-- Corrected item 4. If every edge has the same oriented endpoint-degree difference, then
every connected component which contains an edge is biregular. Its side degrees have the
prescribed difference, are positive, and satisfy the incidence-count identity. -/
theorem edge_component_biregular (C : (graph R).ConnectedComponent) {delta : ℤ}
    (hedge : ∀ a b, R a b → (leftDegree R a : ℤ) - rightDegree R b = delta)
    (hCedge : ∃ a b, R a b ∧ Sum.inl a ∈ C.supp) :
    ∃ dA dB : ℕ,
      1 ≤ dA ∧ 1 ≤ dB ∧
      (∀ a ∈ leftPart R C, leftDegree R a = dA) ∧
      (∀ b ∈ rightPart R C, rightDegree R b = dB) ∧
      (dA : ℤ) - dB = delta ∧
      (leftPart R C).card * dA = (rightPart R C).card * dB := by
  classical
  obtain ⟨a₀, b₀, hab₀, ha₀C⟩ := hCedge
  let dA := leftDegree R a₀
  let dB := rightDegree R b₀
  have hb₀C : Sum.inr b₀ ∈ C.supp :=
    ((SimpleGraph.ConnectedComponent.mem_supp_congr_adj C
      (show (graph R).Adj (Sum.inl a₀) (Sum.inr b₀) from hab₀))).mp ha₀C
  have hdApos : 1 ≤ dA := by
    apply Finset.card_pos.mpr
    exact ⟨b₀, by simp [hab₀]⟩
  have hdBpos : 1 ≤ dB := by
    apply Finset.card_pos.mpr
    exact ⟨a₀, by simp [hab₀]⟩
  have hleft : ∀ a ∈ leftPart R C, leftDegree R a = dA := by
    intro a ha
    have haC : Sum.inl a ∈ C.supp := by simpa [leftPart] using ha
    have hreach := SimpleGraph.ConnectedComponent.reachable_of_mem_supp C ha₀C haC
    have hp := potential_eq_of_reachable R hedge hreach
    simpa [potential, dA] using hp.symm
  have hright : ∀ b ∈ rightPart R C, rightDegree R b = dB := by
    intro b hb
    have hbC : Sum.inr b ∈ C.supp := by simpa [rightPart] using hb
    have hreach := SimpleGraph.ConnectedComponent.reachable_of_mem_supp C hb₀C hbC
    have hp := potential_eq_of_reachable R hedge hreach
    simpa [potential, dB] using hp.symm
  have hdiff : (dA : ℤ) - dB = delta := by
    simpa [dA, dB] using hedge a₀ b₀ hab₀
  have hcount : (leftPart R C).card * dA = (rightPart R C).card * dB := by
    apply Finset.card_mul_eq_card_mul R
    · intro a ha
      rw [left_restricted_degree R C ha, hleft a ha]
    · intro b hb
      rw [right_restricted_degree R C hb, hright b hb]
  exact ⟨dA, dB, hdApos, hdBpos, hleft, hright, hdiff, hcount⟩

/-- The excluded case in corrected item 4: a component with no edge is a singleton. No
degree-difference conclusion involving `delta` is asserted for it. -/
theorem edgeFreeComponent_support_eq_singleton (C : (graph R).ConnectedComponent)
    (hno : ¬ ∃ a b, R a b ∧ Sum.inl a ∈ C.supp) {x : A ⊕ B} (hx : x ∈ C.supp) :
    C.supp = {x} := by
  ext y
  constructor
  · intro hy
    have hreach := SimpleGraph.ConnectedComponent.reachable_of_mem_supp C hx hy
    by_contra hne
    have hxyne : x ≠ y := by
      intro hxy
      subst y
      exact hne (by simp)
    obtain ⟨z, hxz⟩ := hreach.nonempty_neighborSet_left hxyne
    change (graph R).Adj x z at hxz
    rcases x with a | b <;> rcases z with a' | b'
    · simp [graph] at hxz
    · exact hno ⟨a, b', hxz, hx⟩
    · have hzC : Sum.inl a' ∈ C.supp :=
        ((SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hxz)).mp hx
      exact hno ⟨a', b, hxz, hzC⟩
    · simp [graph] at hxz
  · intro hy
    have hyx : y = x := by simpa using hy
    subst y
    exact hx

/-! ## Counting Hall for a biregular bipartite graph -/

/-- Item 5. A finite biregular bipartite incidence graph with `dA ≥ dB ≥ 1` has a
matching saturating its `A`-part. The function is obtained from mathlib's finite marriage
theorem after the standard incidence count establishes Hall's condition. -/
theorem biregular_matching (dA dB : ℕ)
    (hA : ∀ a, leftDegree R a = dA)
    (hB : ∀ b, rightDegree R b = dB)
    (hge : dB ≤ dA) (hpos : 1 ≤ dB) :
    ∃ f : A → B, Injective f ∧ ∀ a, R a (f a) := by
  classical
  have hA' : ∀ a, (Finset.univ.filter (R a)).card = dA := by
    intro a
    simpa [leftDegree] using hA a
  have hB' : ∀ b, (Finset.univ.filter (fun a => R a b)).card = dB := by
    intro b
    simpa [rightDegree] using hB b
  have hHall : ∀ s : Finset A,
      s.card ≤ (s.biUnion (fun a => Finset.univ.filter (R a))).card := by
    intro s
    let N := s.biUnion (fun a => Finset.univ.filter (R a))
    have hfilter (a : A) (ha : a ∈ s) :
        Finset.univ.filter (R a) = N.filter (R a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hab
        exact ⟨Finset.mem_biUnion.mpr
          ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab⟩⟩, hab⟩
      · exact fun h => h.2
    have hswap :
        ∑ a ∈ s, (Finset.univ.filter (R a)).card =
          ∑ b ∈ N, (s.filter (fun a => R a b)).card := by
      calc
        _ = ∑ a ∈ s, (N.filter (R a)).card := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hfilter a ha]
        _ = ∑ a ∈ s, ∑ b ∈ N, if R a b then 1 else 0 := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = ∑ b ∈ N, ∑ a ∈ s, if R a b then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = _ := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcount : s.card * dA ≤ N.card * dB := by
      rw [← Finset.sum_const_nat (fun a (_ : a ∈ s) => hA' a)]
      rw [hswap]
      rw [← Finset.sum_const_nat (s := N) (fun _ _ => rfl)]
      apply Finset.sum_le_sum
      intro b _hb
      have hsub : s.filter (fun a => R a b) ⊆ Finset.univ.filter (fun a => R a b) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.2
      rw [← hB' b]
      exact Finset.card_le_card hsub
    have hmul : s.card * dB ≤ N.card * dB :=
      (Nat.mul_le_mul_left s.card hge).trans hcount
    exact Nat.le_of_mul_le_mul_right hmul hpos
  obtain ⟨f, hf, hadj⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun a => Finset.univ.filter (R a))).mp hHall
  exact ⟨f, hf, fun a => by simpa using hadj a⟩

end BipartiteInterface

/-! ## Realization interfaces: Theorems 5.7 and 5.8 -/

/-- The fibre `Phi_S` over a fixed neighbourhood `S`, at the graph boundary. -/
def interfaceFibre (d : V → ℕ) (v : V) (S : Finset V) : Type u :=
  {G : Realization d // G.neighborFinset v = S}

/-- The realization graph induced on the fibre `Phi_S`. -/
noncomputable def interfaceFibreGraph (d : V → ℕ) (v : V) (S : Finset V) :
    SimpleGraph (interfaceFibre d v S) :=
  (RealizationGraph d).comap Subtype.val

/-- The connector neighbourhood of a finite set of source-fibre realizations. This is the union
of the literal target sets constructed in `QuotientAdjacency`. -/
noncomputable def connectorNeighborhood {d : V → ℕ} {S : Finset V} {v a b : V}
    (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    (A : Finset (interfaceFibre d v S)) : Finset (Realization d) := by
  classical
  exact A.biUnion fun G =>
    sSideConnectorTargets G.1 G.2 hbS haS hav hbv

/-- Lemma 5.7a. In a triangle-free realization graph, a reverse interface witness forces
the forward witness count to be at most one. -/
theorem lemma_5_7a {f : V → ℕ} (F : Realization f) {a b : V} (hab : a ≠ b)
    (htriangle : (RealizationGraph f).CliqueFree 3)
    (hreverse : 1 ≤ interfaceWitnessCount F.graph b a) :
    interfaceWitnessCount F.graph a b ≤ 1 := by
  classical
  by_contra hforward
  have hforward' : 1 < (interfaceWitnessSet F.graph a b).card := by
    simpa [interfaceWitnessCount] using (show 1 < interfaceWitnessCount F.graph a b by omega)
  have hreverse' : 0 < (interfaceWitnessSet F.graph b a).card := by
    simpa [interfaceWitnessCount] using (show 0 < interfaceWitnessCount F.graph b a by omega)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hreverse'
  obtain ⟨t, ht, t', ht', htt'⟩ := Finset.one_lt_card.mp hforward'
  simp only [interfaceWitnessSet, Finset.mem_sdiff, Finset.mem_insert,
    SimpleGraph.mem_neighborFinset] at hx ht ht'
  have hxb : F.graph.Adj x b := hx.1.symm
  have hxa : ¬ F.graph.Adj x a := fun h => hx.2 (Or.inr h.symm)
  have hta : F.graph.Adj t a := ht.1.symm
  have htb : ¬ F.graph.Adj t b := fun h => ht.2 (Or.inr h.symm)
  have ht'a : F.graph.Adj t' a := ht'.1.symm
  have ht'b : ¬ F.graph.Adj t' b := fun h => ht'.2 (Or.inr h.symm)
  have hax : a ≠ x := fun h => hx.2 (Or.inl h.symm)
  have hbx : b ≠ x := hxb.ne.symm
  have hat : a ≠ t := hta.ne.symm
  have hbt : b ≠ t := fun h => ht.2 (Or.inl h.symm)
  have hat' : a ≠ t' := ht'a.ne.symm
  have hbt' : b ≠ t' := fun h => ht'.2 (Or.inl h.symm)
  have hxt : x ≠ t := by
    intro h
    subst t
    exact hxa hta
  have hxt' : x ≠ t' := by
    intro h
    subst t'
    exact hxa ht'a
  let Fₜ := quotientSwitchRealization F hxb hxa hta htb hax hbx hab.symm hxt.symm hbt.symm
  let Fₜ' :=
    quotientSwitchRealization F hxb hxa ht'a ht'b hax hbx hab.symm hxt'.symm hbt'.symm
  have hDₜ : F.edgeFinset ∆ Fₜ.edgeFinset =
      {s(b, x), s(a, t), s(a, x), s(b, t)} := by
    simpa [Fₜ] using quotientSwitchRealization_symmDiff F hxb hxa hta htb
      hax hbx hab.symm hxt.symm hbt.symm
  have hDₜ' : F.edgeFinset ∆ Fₜ'.edgeFinset =
      {s(b, x), s(a, t'), s(a, x), s(b, t')} := by
    simpa [Fₜ'] using quotientSwitchRealization_symmDiff F hxb hxa ht'a ht'b
      hax hbx hab.symm hxt'.symm hbt'.symm
  let p : Sym2 V := s(b, x)
  let q : Sym2 V := s(a, x)
  let r : Sym2 V := s(a, t)
  let z : Sym2 V := s(b, t)
  let r' : Sym2 V := s(a, t')
  let z' : Sym2 V := s(b, t')
  have hpq : p ≠ q := by
    simp [p, q, Sym2.eq_iff, hab, hab.symm, hax, hax.symm, hbx, hbx.symm]
  have hpr : p ≠ r := by
    simp [p, r, Sym2.eq_iff, hab, hab.symm, hbx, hbx.symm, hbt, hbt.symm,
      hax, hax.symm, hat, hat.symm, hxt, hxt.symm]
  have hpz : p ≠ z := by
    simp [p, z, Sym2.eq_iff, hbx, hbx.symm, hbt, hbt.symm, hxt, hxt.symm]
  have hpr' : p ≠ r' := by
    simp [p, r', Sym2.eq_iff, hab, hab.symm, hbx, hbx.symm, hbt', hbt'.symm,
      hax, hax.symm, hat', hat'.symm, hxt', hxt'.symm]
  have hpz' : p ≠ z' := by
    simp [p, z', Sym2.eq_iff, hbx, hbx.symm, hbt', hbt'.symm, hxt', hxt'.symm]
  have hqr : q ≠ r := by
    simp [q, r, Sym2.eq_iff, hax, hax.symm, hat, hat.symm, hxt, hxt.symm]
  have hqz : q ≠ z := by
    simp [q, z, Sym2.eq_iff, hab, hab.symm, hax, hax.symm, hbx, hbx.symm,
      hat, hat.symm, hbt, hbt.symm, hxt, hxt.symm]
  have hqr' : q ≠ r' := by
    simp [q, r', Sym2.eq_iff, hax, hax.symm, hat', hat'.symm, hxt', hxt'.symm]
  have hqz' : q ≠ z' := by
    simp [q, z', Sym2.eq_iff, hab, hab.symm, hax, hax.symm, hbx, hbx.symm,
      hat', hat'.symm, hbt', hbt'.symm, hxt', hxt'.symm]
  have hrz : r ≠ z := by
    simp [r, z, Sym2.eq_iff, hab, hab.symm, hat, hat.symm, hbt, hbt.symm]
  have hrr' : r ≠ r' := by
    simp [r, r', Sym2.eq_iff, htt', htt'.symm, hat, hat.symm, hat', hat'.symm]
  have hrz' : r ≠ z' := by
    simp [r, z', Sym2.eq_iff, hab, hab.symm, htt', htt'.symm, hat, hat.symm,
      hbt, hbt.symm, hat', hat'.symm, hbt', hbt'.symm]
  have hzr' : z ≠ r' := by
    simp [z, r', Sym2.eq_iff, hab, hab.symm, htt', htt'.symm, hat, hat.symm,
      hbt, hbt.symm, hat', hat'.symm, hbt', hbt'.symm]
  have hzz' : z ≠ z' := by
    simp [z, z', Sym2.eq_iff, htt', htt'.symm, hbt, hbt.symm, hbt', hbt'.symm]
  have hr'z' : r' ≠ z' := by
    simp [r', z', Sym2.eq_iff, hab, hab.symm, hat', hat'.symm, hbt', hbt'.symm]
  have hxor : ({p, r, q, z} : Finset (Sym2 V)) ∆ {p, r', q, z'} =
      {r, z, r', z'} := by
    ext e
    by_cases hep : e = p
    · subst e
      simp [Finset.mem_symmDiff, hpr, hpz, hpr', hpz']
    · by_cases heq : e = q
      · subst e
        simp [Finset.mem_symmDiff, hpq, hqr, hqz, hqr', hqz']
      · by_cases her : e = r
        · subst e
          simp [Finset.mem_symmDiff, hep, hpr, hqr, hrr', hrz', hrz, heq]
        · by_cases hez : e = z
          · subst e
            simp [Finset.mem_symmDiff, hep, heq, hrz, hzr', hzz']
          · by_cases her' : e = r'
            · subst e
              simp [Finset.mem_symmDiff, hep, heq, her, hez, hrr', hzr', hr'z']
            · by_cases hez' : e = z'
              · subst e
                simp [Finset.mem_symmDiff, hep, heq, her, hez, her', hrz', hzz', hr'z']
              · simp [Finset.mem_symmDiff, hep, heq, her, hez, her', hez']
  have hDₜₜ' : Fₜ.edgeFinset ∆ Fₜ'.edgeFinset = {r, z, r', z'} := by
    calc
      Fₜ.edgeFinset ∆ Fₜ'.edgeFinset =
          (F.edgeFinset ∆ Fₜ.edgeFinset) ∆ (F.edgeFinset ∆ Fₜ'.edgeFinset) := by
            calc
              Fₜ.edgeFinset ∆ Fₜ'.edgeFinset =
                  (Fₜ.edgeFinset ∆ Fₜ'.edgeFinset) ∆
                    (F.edgeFinset ∆ F.edgeFinset) := by
                      rw [symmDiff_self, symmDiff_bot]
              _ = (F.edgeFinset ∆ Fₜ.edgeFinset) ∆
                  (F.edgeFinset ∆ Fₜ'.edgeFinset) := by ac_rfl
      _ = ({p, r, q, z} : Finset (Sym2 V)) ∆ {p, r', q, z'} := by
        simpa [p, q, r, z, r', z'] using congrArg₂ (· ∆ ·) hDₜ hDₜ'
      _ = {r, z, r', z'} := hxor
  have hFₜ : (RealizationGraph f).Adj F Fₜ := by
    change (F.edgeFinset ∆ Fₜ.edgeFinset).card = 4
    rw [hDₜ, Finset.card_eq_four]
    exact ⟨p, r, q, z, hpr, hpq, hpz, hqr.symm, hrz, hqz, by simp [p, q, r, z]⟩
  have hFₜ' : (RealizationGraph f).Adj F Fₜ' := by
    change (F.edgeFinset ∆ Fₜ'.edgeFinset).card = 4
    rw [hDₜ', Finset.card_eq_four]
    exact ⟨p, r', q, z', hpr', hpq, hpz', hqr'.symm, hr'z', hqz',
      by simp [p, q, r', z']⟩
  have hFₜFₜ' : (RealizationGraph f).Adj Fₜ Fₜ' := by
    change (Fₜ.edgeFinset ∆ Fₜ'.edgeFinset).card = 4
    rw [hDₜₜ', Finset.card_eq_four]
    exact ⟨r, z, r', z', hrz, hrr', hrz', hzr', hzz', hr'z', rfl⟩
  exact htriangle {F, Fₜ, Fₜ'}
    (SimpleGraph.is3Clique_iff.mpr ⟨F, Fₜ, Fₜ', hFₜ, hFₜ', hFₜFₜ', rfl⟩)

/-- The positive-degree regime of Theorem 5.7 in intrinsic realization notation. -/
theorem interfaceWitnessCount_eq_degree_sub_of_gt {f : V → ℕ} (F : Realization f)
    {a b : V} (hab : a ≠ b) (htriangle : (RealizationGraph f).CliqueFree 3)
    (hgt : f b < f a) :
    interfaceWitnessCount F.graph a b = f a - f b := by
  have hid := interface_identity_one F a b
  by_cases hreverse : 1 ≤ interfaceWitnessCount F.graph b a
  · have hle := lemma_5_7a F hab htriangle hreverse
    omega
  · have hzero : interfaceWitnessCount F.graph b a = 0 := by omega
    omega

/-- The equal-degree regime before its positivity input: both witness counts are at most one. -/
theorem interfaceWitnessCount_le_one_of_degree_eq {f : V → ℕ} (F : Realization f)
    {a b : V} (hab : a ≠ b) (htriangle : (RealizationGraph f).CliqueFree 3)
    (heq : f a = f b) :
    interfaceWitnessCount F.graph a b ≤ 1 := by
  have hid := interface_identity_one F a b
  by_cases hreverse : 1 ≤ interfaceWitnessCount F.graph b a
  · exact lemma_5_7a F hab htriangle hreverse
  · omega

/-- The negative-degree regime of the trichotomy: the forward witness set is empty. -/
theorem interfaceWitnessCount_eq_zero_of_lt {f : V → ℕ} (F : Realization f)
    {a b : V} (hab : a ≠ b) (htriangle : (RealizationGraph f).CliqueFree 3)
    (hlt : f a < f b) :
    interfaceWitnessCount F.graph a b = 0 := by
  have hid := interface_identity_one F a b
  by_cases hforward : 1 ≤ interfaceWitnessCount F.graph a b
  · have hle := lemma_5_7a F hab.symm htriangle hforward
    omega
  · omega

/-! ## Twins, and the constancy that closes the equal-degree regime (manuscript §5.4)

The three regimes above are the manuscript's **Lemma 5.7b (vicinal trichotomy)**, already proved
here under three names: `interfaceWitnessCount_eq_degree_sub_of_gt`,
`interfaceWitnessCount_le_one_of_degree_eq` and `interfaceWitnessCount_eq_zero_of_lt`. Do not
restate it. All three rest only on `interface_identity_one` and `lemma_5_7a`, which is what makes
their use below non-circular: neither Theorem 5.7 nor Theorem 5.9 is involved.

What the equal-degree regime still needs is that the witness count cannot be `0` throughout the
fibre, and that is the twin material written into `SEC_QUOTIENT.md` §5.4 on 2026-08-17, closing a
step that an earlier draft had closed by a FALSE assertion (that twins make `f'` non-graphical;
witness `F = {ab, cd}` realizing `(1,1,1,1)`). Statements first, per the lane's rule; the proofs are
the next wave.

Verified computationally before being stated: over every labelled degree function on at most seven
vertices with `RealizationGraph f` triangle-free, `compute/sec54_twin_sweep_n7.py` found no
violation of twin constancy, none of the obligation that no realization is twin when `f'` is
graphical, and none of `w_ab = 1`. -/

/-- `a` and `b` are **twins** in `F` when they have the same neighbours apart from each other.
Manuscript §5.4. By `interface_identity_one` this is exactly the vanishing of both witness counts,
which is why it is the obstruction the equal-degree regime has to rule out. -/
def Twins {f : V → ℕ} (F : Realization f) (a b : V) : Prop :=
  (F.graph.neighborFinset a).erase b = (F.graph.neighborFinset b).erase a

/-- Twins are exactly where the forward witness count vanishes, in the equal-degree regime.
Manuscript §5.4, the sentence "It is `0` exactly when ... `a` and `b` are twins in `F`". -/
theorem twins_iff_interfaceWitnessCount_eq_zero {f : V → ℕ} (F : Realization f) {a b : V}
    (hab : a ≠ b) (heq : f a = f b) :
    Twins F a b ↔ interfaceWitnessCount F.graph a b = 0 := by
  classical
  constructor
  · intro htwins
    simp only [interfaceWitnessCount, interfaceWitnessSet_eq_erased_sdiff]
    rw [htwins, Finset.sdiff_self]
    rfl
  · intro hzero
    have hreverse : interfaceWitnessCount F.graph b a = 0 := by
      have hid := interface_identity_one F a b
      rw [heq] at hid
      omega
    unfold Twins
    apply Finset.Subset.antisymm
    · apply Finset.sdiff_eq_empty_iff_subset.mp
      rw [← interfaceWitnessSet_eq_erased_sdiff]
      exact Finset.card_eq_zero.mp (by simpa [interfaceWitnessCount] using hzero)
    · apply Finset.sdiff_eq_empty_iff_subset.mp
      rw [← interfaceWitnessSet_eq_erased_sdiff]
      exact Finset.card_eq_zero.mp (by simpa [interfaceWitnessCount] using hreverse)

/-- **Lemma 5.7c.** No 2-switch joins a twin realization to a non-twin one, for an equal-degree
pair in a triangle-free realization graph. Manuscript §5.4.

**The proof is the SWAP, not a case enumeration.** Let `τ` be the transposition of `a` and `b`.
Twinhood in `F` says exactly that `τ` fixes `F`, so applying `τ` to an adjacency `F ~ H` gives
`F ~ H^τ`; and if `a, b` are not twins in `H` then the witness counts are one in each direction, so
`H` and `H^τ` differ in exactly one alternating four-cycle and are adjacent. `{F, H, H^τ}` is then a
triangle.

⚠ **Corrected 2026-08-24, completed 2026-08-25.** This docstring once described *"a two-case switch
enumeration"* that used a separate clique lemma — the argument the MANUSCRIPT printed, not the one
below it. There is no case split on `Adj a b` anywhere here. The manuscript took the swap instead,
650 words down to 203; and on 2026-08-25 that clique lemma was deleted from the paper AND from this
module, being consumed by no proof in either. Its own docstring's observation that it "is never
invoked" was the evidence for the cut. What was Lemma 5.7d is now **5.7c**, and 5.7e is now 5.7d. -/
theorem lemma_5_7c_twin_invariant_along_edge {f : V → ℕ} {a b : V}
    (hab : a ≠ b) (heq : f a = f b) (htriangle : (RealizationGraph f).CliqueFree 3)
    {F F' : Realization f} (hadj : (RealizationGraph f).Adj F F') :
    (Twins F a b ↔ Twins F' a b) := by
  classical
  let τ : Equiv.Perm V := Equiv.swap a b
  have hτa : τ a = b := by simp [τ]
  have hτb : τ b = a := by simp [τ]
  have hτfix {x : V} (hxa : x ≠ a) (hxb : x ≠ b) : τ x = x := by
    simp [τ, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hedgeFinset_comap (G : SimpleGraph V) [DecidableRel G.Adj] :
      (G.comap τ).edgeFinset =
        G.edgeFinset.map τ.symm.toEmbedding.sym2Map := by
    ext z
    induction z using Sym2.inductionOn with
    | _ x y =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.comap_adj, Finset.mem_map, Function.Embedding.sym2Map_apply]
        constructor
        · intro h
          exact ⟨s(τ x, τ y), h, by simp⟩
        · rintro ⟨e, he, hmap⟩
          change τ.symm.toEmbedding.sym2Map e = s(x, y) at hmap
          have heq : e = s(τ x, τ y) := by
            apply τ.symm.toEmbedding.sym2Map.injective
            rw [hmap]
            simp [Function.Embedding.sym2Map_apply]
          rw [heq] at he
          exact he
  have hforward : ∀ {G H : Realization f},
      (RealizationGraph f).Adj G H → Twins G a b → Twins H a b := by
    intro G H hGH hGtwins
    by_contra hHtwins
    have hwle := interfaceWitnessCount_le_one_of_degree_eq H hab htriangle heq
    have hwne : interfaceWitnessCount H.graph a b ≠ 0 := by
      intro hwzero
      exact hHtwins ((twins_iff_interfaceWitnessCount_eq_zero H hab heq).2 hwzero)
    have hw : interfaceWitnessCount H.graph a b = 1 := by omega
    have hid := interface_identity_one H a b
    rw [heq] at hid
    have hwrev : interfaceWitnessCount H.graph b a = 1 := by omega
    obtain ⟨x, hWx⟩ := Finset.card_eq_one.mp (by
      simpa [interfaceWitnessCount] using hw)
    obtain ⟨y, hWy⟩ := Finset.card_eq_one.mp (by
      simpa [interfaceWitnessCount] using hwrev)
    have hxmem : x ∈ interfaceWitnessSet H.graph a b := by simp [hWx]
    have hymem : y ∈ interfaceWitnessSet H.graph b a := by simp [hWy]
    simp only [interfaceWitnessSet, Finset.mem_sdiff, Finset.mem_insert,
      SimpleGraph.mem_neighborFinset] at hxmem hymem
    have hax : a ≠ x := hxmem.1.ne
    have hxb : x ≠ b := fun h => hxmem.2 (Or.inl h)
    have hHbx : ¬ H.graph.Adj b x := fun h => hxmem.2 (Or.inr h)
    have hby : b ≠ y := hymem.1.ne
    have hya : y ≠ a := fun h => hymem.2 (Or.inl h)
    have hHay : ¬ H.graph.Adj a y := fun h => hymem.2 (Or.inr h)
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hHay hxmem.1
    have hcrossH {z : V} (hza : z ≠ a) (hzb : z ≠ b)
        (hzx : z ≠ x) (hzy : z ≠ y) :
        (H.graph.Adj a z ↔ H.graph.Adj b z) := by
      constructor
      · intro haz
        by_contra hbz
        have hzmem : z ∈ interfaceWitnessSet H.graph a b := by
          simp [interfaceWitnessSet, SimpleGraph.mem_neighborFinset, haz, hbz, hzb]
        rw [hWx] at hzmem
        exact hzx (by simpa using hzmem)
      · intro hbz
        by_contra haz
        have hzmem : z ∈ interfaceWitnessSet H.graph b a := by
          simp [interfaceWitnessSet, SimpleGraph.mem_neighborFinset, hbz, haz, hza]
        rw [hWy] at hzmem
        exact hzy (by simpa using hzmem)
    let K := quotientSwitchRealization H hxmem.1.symm
      (fun h => hHbx h.symm) hymem.1.symm (fun h => hHay h.symm)
      hxb.symm hax hab hxy.symm hya
    have hD : H.edgeFinset ∆ K.edgeFinset =
        {s(a, x), s(b, y), s(b, x), s(a, y)} := by
      simpa [K] using quotientSwitchRealization_symmDiff H hxmem.1.symm
        (fun h => hHbx h.symm) hymem.1.symm (fun h => hHay h.symm)
        hxb.symm hax hab hxy.symm hya
    have hHK : (RealizationGraph f).Adj H K := by
      change (H.edgeFinset ∆ K.edgeFinset).card = 4
      rw [hD, Finset.card_eq_four]
      refine ⟨s(a, x), s(b, y), s(b, x), s(a, y), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
        simp [Sym2.eq_iff, hab, hab.symm, hax, hax.symm, hxb, hxb.symm,
          hby, hby.symm, hya, hya.symm, hxy, hxy.symm]
    have hdiff (p q : V) :
        ((H.graph.Adj p q ∧ ¬ K.graph.Adj p q) ∨
          (K.graph.Adj p q ∧ ¬ H.graph.Adj p q)) ↔
        s(p, q) ∈ ({s(a, x), s(b, y), s(b, x), s(a, y)} : Finset (Sym2 V)) := by
      have hm := congrArg (fun E : Finset (Sym2 V) => s(p, q) ∈ E) hD
      simpa [Realization.edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Finset.mem_symmDiff] using hm
    have hKsame {p q : V}
        (hn : s(p, q) ∉ ({s(a, x), s(b, y), s(b, x), s(a, y)} : Finset (Sym2 V))) :
        (K.graph.Adj p q ↔ H.graph.Adj p q) := by
      have hdnot : ¬ ((H.graph.Adj p q ∧ ¬ K.graph.Adj p q) ∨
          (K.graph.Adj p q ∧ ¬ H.graph.Adj p q)) := by
        intro hd
        exact hn ((hdiff p q).mp hd)
      constructor
      · intro hk
        by_contra hh
        exact hdnot (Or.inr ⟨hk, hh⟩)
      · intro hh
        by_contra hk
        exact hdnot (Or.inl ⟨hh, hk⟩)
    have hKax : ¬ K.graph.Adj a x := by
      have hd := (hdiff a x).mpr (by simp)
      intro hk
      rcases hd with hd | hd
      · exact hd.2 hk
      · exact hd.2 hxmem.1
    have hKbx : K.graph.Adj b x := by
      have hd := (hdiff b x).mpr (by simp)
      rcases hd with hd | hd
      · exact False.elim (hHbx hd.1)
      · exact hd.1
    have hKby : ¬ K.graph.Adj b y := by
      have hd := (hdiff b y).mpr (by simp)
      intro hk
      rcases hd with hd | hd
      · exact hd.2 hk
      · exact hd.2 hymem.1
    have hKay : K.graph.Adj a y := by
      have hd := (hdiff a y).mpr (by simp)
      rcases hd with hd | hd
      · exact False.elim (hHay hd.1)
      · exact hd.1
    have hKrowa (q : V) : K.graph.Adj a q ↔ H.graph.Adj b (τ q) := by
      by_cases hqa : q = a
      · subst q
        simp [hτa]
      · by_cases hqb : q = b
        · subst q
          rw [hτb]
          have hs : K.graph.Adj a b ↔ H.graph.Adj a b := hKsame (by
            simp [hab, hax, hxb, hxb.symm, hby, hya, hya.symm])
          exact hs.trans ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
        · by_cases hqx : q = x
          · subst q
            rw [hτfix hax.symm hxb]
            exact iff_of_false hKax hHbx
          · by_cases hqy : q = y
            · subst q
              rw [hτfix hya hby.symm]
              exact iff_of_true hKay hymem.1
            · rw [hτfix hqa hqb]
              have hs : K.graph.Adj a q ↔ H.graph.Adj a q := hKsame (by
                simp [Sym2.eq_iff, hab, hax, hxb, hby, hya, hqa, hqb, hqx, hqy])
              exact hs.trans (hcrossH hqa hqb hqx hqy)
    have hKrowb (q : V) : K.graph.Adj b q ↔ H.graph.Adj a (τ q) := by
      by_cases hqa : q = a
      · subst q
        rw [hτa]
        have hs : K.graph.Adj b a ↔ H.graph.Adj b a := hKsame (by
          simp [hab, hax, hxb, hxb.symm, hby, hya, hya.symm])
        exact hs.trans ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
      · by_cases hqb : q = b
        · subst q
          simp [hτb]
        · by_cases hqx : q = x
          · subst q
            rw [hτfix hax.symm hxb]
            exact iff_of_true hKbx hxmem.1
          · by_cases hqy : q = y
            · subst q
              rw [hτfix hya hby.symm]
              exact iff_of_false hKby hHay
            · rw [hτfix hqa hqb]
              have hs : K.graph.Adj b q ↔ H.graph.Adj b q := hKsame (by
                simp [Sym2.eq_iff, hab, hax, hxb, hby, hya, hqa, hqb, hqx, hqy])
              exact hs.trans (hcrossH hqa hqb hqx hqy).symm
    have hKswap : K.graph = H.graph.comap τ := by
      ext p q
      simp only [SimpleGraph.comap_adj]
      by_cases hpa : p = a
      · subst p
        rw [hτa]
        exact hKrowa q
      · by_cases hpb : p = b
        · subst p
          rw [hτb]
          exact hKrowb q
        · by_cases hqa : q = a
          · subst q
            rw [hτa]
            exact ⟨fun h => ((hKrowa p).mp h.symm).symm,
              fun h => ((hKrowa p).mpr h.symm).symm⟩
          · by_cases hqb : q = b
            · subst q
              rw [hτb]
              exact ⟨fun h => ((hKrowb p).mp h.symm).symm,
                fun h => ((hKrowb p).mpr h.symm).symm⟩
            · rw [hτfix hpa hpb, hτfix hqa hqb]
              exact hKsame (by
                simp [Sym2.eq_iff, hab, hax, hxb, hby, hya, hpa, hpb, hqa, hqb])
    have hcrossG {z : V} (hza : z ≠ a) (hzb : z ≠ b) :
        (G.graph.Adj a z ↔ G.graph.Adj b z) := by
      have hmem := congrArg (fun S : Finset V => z ∈ S) hGtwins
      simpa [Twins, Finset.mem_erase, SimpleGraph.mem_neighborFinset, hza, hzb] using hmem
    have hGswap : G.graph = G.graph.comap τ := by
      ext p q
      simp only [SimpleGraph.comap_adj]
      by_cases hpa : p = a
      · subst p
        by_cases hqa : q = a
        · subst q
          simp [τ]
        · by_cases hqb : q = b
          · subst q
            rw [hτa, hτb]
            exact ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
          · simpa [hτa, hτfix hqa hqb] using hcrossG hqa hqb
      · by_cases hpb : p = b
        · subst p
          by_cases hqa : q = a
          · subst q
            rw [hτb, hτa]
            exact ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
          · by_cases hqb : q = b
            · subst q
              simp [τ]
            · simpa [hτb, hτfix hqa hqb] using (hcrossG hqa hqb).symm
        · by_cases hqa : q = a
          · subst q
            rw [hτfix hpa hpb, hτa]
            exact ⟨fun h => ((hcrossG hpa hpb).mp h.symm).symm,
              fun h => ((hcrossG hpa hpb).mpr h.symm).symm⟩
          · by_cases hqb : q = b
            · subst q
              rw [hτfix hpa hpb, hτb]
              exact ⟨fun h => ((hcrossG hpa hpb).mpr h.symm).symm,
                fun h => ((hcrossG hpa hpb).mp h.symm).symm⟩
            · rw [hτfix hpa hpb, hτfix hqa hqb]
    have hGK : (RealizationGraph f).Adj G K := by
      change (G.edgeFinset ∆ K.edgeFinset).card = 4
      have hmapG : G.edgeFinset.map τ.symm.toEmbedding.sym2Map = G.edgeFinset := by
        change G.graph.edgeFinset.map τ.symm.toEmbedding.sym2Map = G.graph.edgeFinset
        rw [← hedgeFinset_comap]
        ext e
        induction e using Sym2.inductionOn with
        | _ u v =>
            simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact (congrFun (congrFun (SimpleGraph.ext_iff.mp hGswap) u) v).symm.to_iff
      have hmapH : H.edgeFinset.map τ.symm.toEmbedding.sym2Map = K.edgeFinset := by
        change H.graph.edgeFinset.map τ.symm.toEmbedding.sym2Map = K.graph.edgeFinset
        rw [← hedgeFinset_comap]
        ext e
        induction e using Sym2.inductionOn with
        | _ u v =>
            simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact (congrFun (congrFun (SimpleGraph.ext_iff.mp hKswap) u) v).symm.to_iff
      rw [← hmapG, ← hmapH]
      rw [Finset.map_eq_image, Finset.map_eq_image]
      rw [← Finset.image_symmDiff _ _ τ.symm.toEmbedding.sym2Map.injective]
      rw [← Finset.map_eq_image, Finset.card_map]
      exact hGH
    exact htriangle {G, H, K}
      (SimpleGraph.is3Clique_iff.mpr ⟨G, H, K, hGH, hGK, hHK, rfl⟩)
  exact ⟨hforward hadj, hforward hadj.symm⟩

/-- **Corollary 5.7d (twin constancy).** In a triangle-free realization graph, twinhood of an
equal-degree pair is the same at every realization. Manuscript §5.4.

Connectivity of the realization graph is a HYPOTHESIS rather than an axiom: it is classical, a
consequence of a theorem of Fulkerson, Hoffman and McAndrew as Barrus records, and the manuscript
cites it in §2 — but it is not proved in this development, and taking it as a hypothesis keeps that
visible in the signature instead of enlarging the axiom surface. -/
theorem corollary_5_7c_twins_constant {f : V → ℕ} {a b : V}
    (hab : a ≠ b) (heq : f a = f b) (htriangle : (RealizationGraph f).CliqueFree 3)
    (hconn : (RealizationGraph f).Preconnected) (F F' : Realization f) :
    (Twins F a b ↔ Twins F' a b) := by
  obtain ⟨p⟩ := hconn F F'
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      exact (lemma_5_7c_twin_invariant_along_edge hab heq htriangle hadj).trans ih

/-! ### The two bridges to the ground language (manuscript Lemma 5.1)

Everything in §5.4 above is proved on `Realization f` with counts given by `interfaceWitnessCount`.
That is the manuscript's own move -- *"it is convenient to drop the pivot first"* -- but
`theorem_5_7_cross_degree` below is stated in the pivot language, over `interfaceFibre d v S`. These
two statements are the bridge, and they are the manuscript's Lemma 5.1.

Reuse already found, do not re-derive: `deleteVertexGraph_realizes_residual` (Observation0) already
gives the degree half, so what is missing is only that deletion is an ISOMORPHISM of the two graphs,
and that the connector count is the ground witness count.

The counts are on the ground on both sides, which is the convention corrected on 2026-08-17: with the
pivot present `v ∈ N_G(b)` and `v ∉ N_G(a)`, so the pivot would be counted by `w_ba` alone and the
signed identity would read `δ − 1`. `interface_identity_one` already uses the ground reading, so these
bridges compose with it with no correction factor. -/

/-- **Manuscript Lemma 5.1.** Deleting the pivot is an isomorphism from the fibre over `S` onto the
realization graph of the residual degree function. Injectivity is that a fibre member is determined
by its deletion together with `N(v) = S` (reuse `realization_eq_of_edgeFinset_eq`); surjectivity is
the lifting direction of Observation 0, adding `v` back adjacent to exactly `S`; and a 2-switch
between fibre members cannot touch `v`, since that would move `N(v)`.

⚠ THE THREE HYPOTHESES ARE NOT DECORATION. This statement was written FALSE TWICE on 2026-08-17,
and both versions are recorded rather than quietly fixed, because the second failure is instructive.

First draft, no hypotheses: the fibre can be EMPTY while the residual realization graph is not, so no
equivalence exists. Adding `hv` and `hcard` looked like enough — and was not.

Second draft, `hv` and `hcard` only: still FALSE, by a counterexample from the wave that was asked to
prove it. Take `V = {v, u}`, `d v = 1`, `d u = 0`, `S = {u}`. Then `v ∉ S` and `S.card = 1 = d v`, yet
the fibre is empty — `N(v) = {u}` forces the edge `vu`, giving `u` degree at least one against
`d u = 0` — while the residual is realizable by the edgeless graph. **The root cause is truncated
subtraction: `residualDegree` computes `d u - 1 = 0 - 1 = 0` in `ℕ`, so the residual silently forgets
that `u` could not have been in `S` at all.**

`hpos` is exactly the missing condition, and it is not new: it is already the hypothesis of
`addVertexGraph_realizes_original` in `Observation0.lean`, which is the lifting lemma this proof has
to use. It holds at every call site, since a member of a realizable neighbourhood is adjacent to the
pivot and so has positive degree. -/
noncomputable def fibreDeleteIso {d : V → ℕ} {v : V} {S : Finset V}
    (hv : v ∉ S) (hcard : S.card = d v) (hpos : ∀ u ∈ S, 0 < d u) :
    interfaceFibreGraph d v S ≃g RealizationGraph (residualDegree d v S) := by
  classical
  let forward : interfaceFibre d v S → Realization (residualDegree d v S) :=
    fun G => deleteVertexGraph_realizes_residual G.1 v S G.2
  let backward : Realization (residualDegree d v S) → interfaceFibre d v S :=
    fun H => ⟨addVertexGraph_realizes_original hv hcard hpos H,
      addVertexGraph_neighborFinset_v v S hv H.graph⟩
  have realization_eq_graph {W : Type u} [Fintype W] {e : W → ℕ}
      (A B : Realization e) (h : A.graph = B.graph) : A = B := by
    cases A with
    | mk graphA decA degreeA =>
      cases B with
      | mk graphB decB degreeB =>
        dsimp at h
        subst graphB
        congr
        exact Subsingleton.elim _ _
  have hleft : Function.LeftInverse backward forward := by
    intro G
    apply Subtype.ext
    have hgraph : (backward (forward G)).1.graph = G.1.graph := by
      ext a b
      change (addVertexGraph v S hv (deleteVertexGraph G.1.graph v)).Adj a b ↔
        G.1.graph.Adj a b
      by_cases ha : a = v
      · subst a
        have hbS : b ∈ S ↔ G.1.graph.Adj v b := by
          simpa only [G.2] using Realization.mem_neighborFinset G.1 v b
        simp [addVertexGraph, hv, hbS]
      · by_cases hb : b = v
        · subst b
          have haS : a ∈ S ↔ G.1.graph.Adj a v := by
            rw [G.1.graph.adj_comm]
            simpa only [G.2] using Realization.mem_neighborFinset G.1 v a
          simp [addVertexGraph, hv, ha, haS]
        · simp [addVertexGraph, deleteVertexGraph, ha, hb]
    exact realization_eq_graph _ _ hgraph
  have hright : Function.RightInverse backward forward := by
    intro H
    have hgraph : (forward (backward H)).graph = H.graph := by
      ext a b
      change (addVertexGraph v S hv H.graph).Adj a.val b.val ↔ H.graph.Adj a b
      simp [addVertexGraph, a.property, b.property]
    exact realization_eq_graph _ _ hgraph
  let U : Finset (Sym2 V) := (Set.toFinset {x : V | x ≠ v}).sym2
  let edgeEmbedding : Sym2 {x : V // x ≠ v} ↪ Sym2 V :=
    (deletedVertexEmbedding v).sym2Map
  have hmap_delete (G : Realization d) :
      (deleteVertexGraph G.graph v).edgeFinset.map edgeEmbedding =
        G.graph.edgeFinset ∩ U := by
    exact SimpleGraph.map_edgeFinset_induce (s := {x : V | x ≠ v}) (G := G.graph)
  have hdiff_card (G H : interfaceFibre d v S) :
      ((forward G).edgeFinset ∆ (forward H).edgeFinset).card =
        (G.1.edgeFinset ∆ H.1.edgeFinset).card := by
    have hmapG : (forward G).edgeFinset.map edgeEmbedding = G.1.edgeFinset ∩ U := by
      change (deleteVertexGraph G.1.graph v).edgeFinset.map edgeEmbedding =
        G.1.graph.edgeFinset ∩ U
      exact hmap_delete G.1
    have hmapH : (forward H).edgeFinset.map edgeEmbedding = H.1.edgeFinset ∩ U := by
      change (deleteVertexGraph H.1.graph v).edgeFinset.map edgeEmbedding =
        H.1.graph.edgeFinset ∩ U
      exact hmap_delete H.1
    have hadj_v (x : V) : G.1.graph.Adj v x ↔ H.1.graph.Adj v x := by
      calc
        G.1.graph.Adj v x ↔ x ∈ G.1.neighborFinset v :=
          (Realization.mem_neighborFinset G.1 v x).symm
        _ ↔ x ∈ S := by simp only [G.2]
        _ ↔ x ∈ H.1.neighborFinset v := by simp only [H.2]
        _ ↔ H.1.graph.Adj v x := Realization.mem_neighborFinset H.1 v x
    have hdiff_subset : G.1.edgeFinset ∆ H.1.edgeFinset ⊆ U := by
      intro edge hedge
      induction edge using Sym2.ind with
      | h a b =>
          have hedge' :
              (G.1.graph.Adj a b ∧ ¬ H.1.graph.Adj a b) ∨
                (H.1.graph.Adj a b ∧ ¬ G.1.graph.Adj a b) := by
            simpa only [Finset.mem_symmDiff, Realization.edgeFinset,
              SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
          have ha : a ≠ v := by
            intro hav
            subst a
            rcases hedge' with ⟨hG, hH⟩ | ⟨hH, hG⟩
            · exact hH ((hadj_v b).mp hG)
            · exact hG ((hadj_v b).mpr hH)
          have hb : b ≠ v := by
            intro hbv
            subst b
            rcases hedge' with ⟨hG, hH⟩ | ⟨hH, hG⟩
            · exact hH ((hadj_v a).mp hG.symm).symm
            · exact hG ((hadj_v a).mpr hH.symm).symm
          simp [U, ha, hb]
    have hmapdiff :
        ((forward G).edgeFinset ∆ (forward H).edgeFinset).map edgeEmbedding =
          G.1.edgeFinset ∆ H.1.edgeFinset := by
      calc
        ((forward G).edgeFinset ∆ (forward H).edgeFinset).map edgeEmbedding =
            (forward G).edgeFinset.map edgeEmbedding ∆
              (forward H).edgeFinset.map edgeEmbedding := by
                simpa only [Finset.map_eq_image] using
                  Finset.image_symmDiff (forward G).edgeFinset (forward H).edgeFinset
                    edgeEmbedding.injective
        _ = (G.1.edgeFinset ∩ U) ∆ (H.1.edgeFinset ∩ U) := by rw [hmapG, hmapH]
        _ = (G.1.edgeFinset ∆ H.1.edgeFinset) ∩ U := by
          ext edge
          simp only [Finset.mem_symmDiff, Finset.mem_inter]
          tauto
        _ = G.1.edgeFinset ∆ H.1.edgeFinset := Finset.inter_eq_left.mpr hdiff_subset
    have := congrArg Finset.card hmapdiff
    simpa only [Finset.card_map] using this
  let e : interfaceFibre d v S ≃ Realization (residualDegree d v S) :=
    Equiv.mk forward backward hleft hright
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro G H
  change twoSwitchAdjacent (forward G) (forward H) ↔ twoSwitchAdjacent G.1 H.1
  unfold twoSwitchAdjacent
  rw [hdiff_card]

/-- **The connector count is the ground witness count.** Manuscript §5.4, "distinct witnesses toggle
distinct ground edges, so `G` has exactly `w_ab(G)` distinct connector partners".

Half of this is already definitional: `residualConnectorCandidates` is built from the neighbourhoods
in `deleteVertexGraph G.graph v`, so it is already a set on the ground, and it coincides with
`interfaceWitnessSet` there -- an `x ∈ N(a)` satisfies `x ≠ a` by looplessness, which is exactly the
clause by which the two set-builders differ. What remains is injectivity of the switch map. -/
theorem card_sSideConnectorTargets_eq_interfaceWitnessCount {d : V → ℕ} {S : Finset V} {v a b : V}
    (G : Realization d) (hS : G.neighborFinset v = S) (hbS : b ∈ S) (haS : a ∉ S)
    (hav : a ≠ v) (hbv : b ≠ v) :
    (sSideConnectorTargets G hS hbS haS hav hbv).card
      = interfaceWitnessCount (deleteVertexGraph G.graph v) ⟨a, hav⟩ ⟨b, hbv⟩ := by
  classical
  rw [sSideConnectorTargets, Finset.card_image_of_injective]
  · rw [Finset.card_attach]
    simp only [interfaceWitnessCount, interfaceWitnessSet_eq_erased_sdiff]
    rfl
  · exact sSideConnectorSwitch_injective G hS hbS haS hav hbv

/-- **CITED: connectivity of the realization graph.** Any two realizations of the same degree
function are joined by a sequence of 2-switches.

Source: R. Fulkerson, A. J. Hoffman, M. H. McAndrew, *Some properties of graphs with multiple
edges*, Canad. J. Math. **17** (1965) 166–177, DOI `10.4153/CJM-1965-016-2`. The attribution was
verified on 2026-08-17 by reading Barrus, *On realization graphs of degree sequences*, p. 1: *"The
best-known result on `G(d)` is that it is a connected graph for any degree sequence `d`; this is a
consequence of a theorem of Fulkerson, Hoffman, and McAndrew [15] (Petersen proved the same result
for regular degree sequences in [23])."* The manuscript cites it in §2.

Formal scope: `Preconnected` of `RealizationGraph f` for every `f`, i.e. every pair of realizations
is joined by a walk of 2-switches. Nothing about lengths or about the switches used.

**THIS IS A TRUST-SURFACE DECISION AND IT WAS JEFF'S**, taken 2026-08-17 night. It was first written
as a named `sorry` so the choice — prove it, or cite it — would be visible and his rather than made
silently by whoever needed it first. He chose to cite it. Consequences, which any axiom audit of this
target must report: `theorem_5_7_cross_degree` and everything downstream now depend on this axiom
instead of carrying `sorryAx`, and it is a cited axiom on the Realization surface.

⚠ **Corrected 2026-08-24.** This said "the SECOND cited axiom … beside
`barrus_theorem9_triangle_free_classification`". **That declaration does not exist** — it was retired
to a theorem on 2026-08-19, and the two Barrus axioms actually present are
`barrus_theorem9_bipartite_iff_triangleFree` and `barrus_theorem9_bipartite_classification`. The
surface carries seven cited axioms, not two. The consequence worth stating plainly: **`ord` and `obi`
are not foundations-only** — both reach this axiom through `theorem_5_8_exact_color_expansion` and
`theorem_5_7_cross_degree`, and neither of their docstrings says so.

`corollary_5_7c_twins_constant` keeps preconnectedness as an explicit HYPOTHESIS rather than invoking
this axiom internally, so the dependency stays legible at every call site.

**Bibliography key: `FHM1965`**, present in this paper's `references.bib`.  Recorded here because a
docstring that names its source only in prose cannot be audited mechanically —
`compute/check_axiom_provenance.py` joins the cited axioms to the bibliography and to §10.4, and it
can only follow a key. -/
axiom realizationGraph_preconnected {V : Type u} [Fintype V] [DecidableEq V] {f : V → ℕ} :
    (RealizationGraph f).Preconnected

/-- Theorem 5.7 (cross-degree), at the realization-graph boundary. For an oriented nonempty
interface `S -> S - b + a`, triangle-freeness of the source fibre forces the signed residual
difference `delta` to be nonnegative, and every source realization has exactly
`max(1, delta)` distinct connector targets. -/
theorem theorem_5_7_cross_degree {d : V → ℕ} {S : Finset V} {v a b : V}
    (hbS : b ∈ S) (haS : a ∉ S)
    (hSreal : HasRealizationWithNeighborSet d v S)
    (hTreal : HasRealizationWithNeighborSet d v (insert a (S.erase b)))
    (hav : a ≠ v) (hbv : b ≠ v)
    (htriangle : (interfaceFibreGraph d v S).CliqueFree 3) :
    (0 : ℤ) ≤
        (residualDegree d v S ⟨a, hav⟩ : ℤ) - residualDegree d v S ⟨b, hbv⟩ ∧
      ∀ G : interfaceFibre d v S,
        (sSideConnectorTargets G.1 G.2 hbS haS hav hbv).card =
          max 1
            (residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩) := by
  classical
  let f := residualDegree d v S
  let av : {x : V // x ≠ v} := ⟨a, hav⟩
  let bv : {x : V // x ≠ v} := ⟨b, hbv⟩
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have habv : av ≠ bv := by
    intro h
    exact hab (congrArg Subtype.val h)
  rcases hSreal with ⟨G₀, hG₀⟩
  have hSreal' : HasRealizationWithNeighborSet d v S := ⟨G₀, hG₀⟩
  have hv : v ∉ S := by
    intro hvS
    have hvloop : v ∈ G₀.neighborFinset v := by simpa [hG₀] using hvS
    exact (SimpleGraph.notMem_neighborFinset_self G₀.graph v) hvloop
  have hcard : S.card = d v := by
    calc
      S.card = (G₀.neighborFinset v).card := congrArg Finset.card hG₀.symm
      _ = G₀.graph.degree v := by
        simp [Realization.neighborFinset, SimpleGraph.card_neighborFinset_eq_degree]
      _ = d v := G₀.degree_eq v
  have hpos : ∀ u ∈ S, 0 < d u := by
    intro u huS
    have hvu : G₀.graph.Adj v u := by
      rw [← Realization.mem_neighborFinset, hG₀]
      exact huS
    rw [← G₀.degree_eq u]
    exact hvu.symm.degree_pos_left
  let e := fibreDeleteIso hv hcard hpos
  have htriangle' : (RealizationGraph f).CliqueFree 3 := by
    exact SimpleGraph.CliqueFree.comap e.symm.isContained htriangle
  have exists_positive (hle : f av ≤ f bv) :
      ∃ F : Realization f, 1 ≤ interfaceWitnessCount F.graph av bv := by
    rcases hTreal with ⟨H, hH⟩
    have hbT : a ∈ insert a (S.erase b) := Finset.mem_insert_self _ _
    have haT : b ∉ insert a (S.erase b) := by simp [hab.symm]
    have hcandidates :
        0 < (residualConnectorCandidates H v b a hbv hav).card := by
      have hlower := residualConnectorCandidates_card_lower H hH hbv hav
      have hle' : d a ≤ d b - 1 := by
        simpa [f, av, bv, residualDegree, hbS, haS] using hle
      have hdiffpos :
          0 < residualDegree d v (insert a (S.erase b)) ⟨b, hbv⟩ -
            residualDegree d v (insert a (S.erase b)) ⟨a, hav⟩ := by
        have hbvalue :
            residualDegree d v (insert a (S.erase b)) ⟨b, hbv⟩ = d b := by
          simp [residualDegree, hbS, hab.symm]
        have havalue :
            residualDegree d v (insert a (S.erase b)) ⟨a, hav⟩ = d a - 1 := by
          simp [residualDegree, haS, hab]
        rw [hbvalue, havalue]
        have hdbpos := hpos b hbS
        exact Nat.sub_pos_of_lt (by omega)
      exact lt_of_lt_of_le hdiffpos hlower
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hcandidates
    have hdata := residualConnectorCandidate_spec H hc
    let G := sSideConnectorSwitch H hH hbT haT hbv hav c hc
    have hGS : G.neighborFinset v = S := by
      have hspec := (sSideConnectorSwitch_spec H hH hbT haT hbv hav c hc).1
      simpa [G, hbS, haS, hab, hab.symm] using hspec
    let F : Realization f := deleteVertexGraph_realizes_residual G v S hGS
    have hGca : G.graph.Adj c.val a := by
      change (quotientSwitchGraph H.graph v a b c.val).Adj c.val a
      simp [quotientSwitchGraph, transferGraph, hdata.1, hdata.2.1, hdata.2.2,
        c.property, hav, hbv, hab, hab.symm]
    have hGcb : ¬ G.graph.Adj c.val b := by
      change ¬ (quotientSwitchGraph H.graph v a b c.val).Adj c.val b
      simp [quotientSwitchGraph, transferGraph, hdata.1, hdata.2.1, hdata.2.2,
        c.property, hav, hbv, hab, hab.symm]
    have hFac : F.graph.Adj av c := by
      change (deleteVertexGraph G.graph v).Adj av c
      simpa [deleteVertexGraph] using hGca.symm
    have hFbc : ¬ F.graph.Adj bv c := by
      change ¬ (deleteVertexGraph G.graph v).Adj bv c
      simpa [deleteVertexGraph] using fun h => hGcb h.symm
    have hcne : c ≠ bv := by
      intro h
      have hcb : c.val = b := congrArg Subtype.val h
      exact hdata.2.1.ne hcb
    have hcW : c ∈ interfaceWitnessSet F.graph av bv := by
      simp only [interfaceWitnessSet, Finset.mem_sdiff, Finset.mem_insert,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hFac, fun h => h.elim hcne hFbc⟩
    refine ⟨F, ?_⟩
    exact Finset.one_le_card.mpr ⟨c, hcW⟩
  have hnonneg :
      (0 : ℤ) ≤ (f av : ℤ) - f bv := by
    by_contra hneg
    have hlt : f av < f bv := by omega
    obtain ⟨F, hpositive⟩ := exists_positive hlt.le
    have hzero := interfaceWitnessCount_eq_zero_of_lt F habv htriangle' hlt
    omega
  refine ⟨?_, ?_⟩
  · simpa [f, av, bv] using hnonneg
  · intro G
    let F : Realization f := deleteVertexGraph_realizes_residual G.1 v S G.2
    letI := F.adjDecidable
    rw [card_sSideConnectorTargets_eq_interfaceWitnessCount]
    change interfaceWitnessCount F.graph av bv = max 1 (f av - f bv)
    by_cases hgt : f bv < f av
    · have hw := interfaceWitnessCount_eq_degree_sub_of_gt F habv htriangle' hgt
      rw [hw]
      omega
    · have heq : f av = f bv := by omega
      obtain ⟨F', hpositive⟩ := exists_positive heq.le
      have hnot_twins' : ¬ Twins F' av bv := by
        intro htwins
        have hzero := (twins_iff_interfaceWitnessCount_eq_zero F' habv heq).1 htwins
        omega
      have htwins_constant := corollary_5_7c_twins_constant habv heq htriangle'
        realizationGraph_preconnected F F'
      have hnot_twins : ¬ Twins F av bv := fun htwins =>
        hnot_twins' (htwins_constant.mp htwins)
      have hne : interfaceWitnessCount F.graph av bv ≠ 0 := fun hzero =>
        hnot_twins ((twins_iff_interfaceWitnessCount_eq_zero F habv heq).2 hzero)
      have hle := interfaceWitnessCount_le_one_of_degree_eq F habv htriangle' heq
      have hone : interfaceWitnessCount F.graph av bv = 1 := by omega
      rw [hone]
      omega

private theorem cliqueFree_three_of_proper_bool {W : Type v} (G : SimpleGraph W)
    (col : W → Bool) (hcol : ∀ x y, G.Adj x y → col x ≠ col y) :
    G.CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, _hs⟩ := SimpleGraph.is3Clique_iff.mp hs
  have hxy' := hcol x y hxy
  have hxz' := hcol x z hxz
  have hyz' := hcol y z hyz
  cases hx : col x <;> cases hy : col y <;> cases hz : col z <;> simp_all

private theorem realization_eq_of_edgeFinset_eq {d : V → ℕ} {G H : Realization d}
    (h : G.edgeFinset = H.edgeFinset) : G = H := by
  have hgraph : G.graph = H.graph := by
    ext x y
    have hmem : s(x, y) ∈ G.edgeFinset ↔ s(x, y) ∈ H.edgeFinset := by rw [h]
    simpa [Realization.edgeFinset, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmem
  cases G with
  | mk graphG decG degreeG =>
      cases H with
      | mk graphH decH degreeH =>
          dsimp at hgraph
          subst graphH
          congr
          exact Subsingleton.elim _ _

/-- Two distinct, nonadjacent members of one source fibre cannot share a literal connector
target. Equivalently, every target's source neighbours form a clique in the source fibre. -/
private theorem connectorTargets_disjoint_of_not_adj {d : V → ℕ} {S : Finset V}
    {v a b : V} (hbS : b ∈ S) (haS : a ∉ S) (hav : a ≠ v) (hbv : b ≠ v)
    (G H : interfaceFibre d v S) (hne : G ≠ H)
    (hnot : ¬ (interfaceFibreGraph d v S).Adj G H) :
    Disjoint
      (sSideConnectorTargets G.1 G.2 hbS haS hav hbv)
      (sSideConnectorTargets H.1 H.2 hbS haS hav hbv) := by
  classical
  rw [Finset.disjoint_left]
  intro K hKG hKH
  rw [sSideConnectorTargets, Finset.mem_image] at hKG hKH
  obtain ⟨cG, _hcGattach, hGK⟩ := hKG
  obtain ⟨cH, _hcHattach, hHK⟩ := hKH
  have hDG := sSideConnectorSwitch_symmDiff G.1 G.2 hbS haS hav hbv cG.1 cG.2
  have hDH := sSideConnectorSwitch_symmDiff H.1 H.2 hbS haS hav hbv cH.1 cH.2
  rw [hGK] at hDG
  rw [hHK] at hDH
  have hcne : cG.1 ≠ cH.1 := by
    intro hc
    have hsourceDiff : (G.1).edgeFinset ∆ (H.1).edgeFinset = ∅ := by
      calc
        (G.1).edgeFinset ∆ (H.1).edgeFinset =
            ((G.1).edgeFinset ∆ K.edgeFinset) ∆ ((H.1).edgeFinset ∆ K.edgeFinset) := by
          calc
            (G.1).edgeFinset ∆ (H.1).edgeFinset =
                ((G.1).edgeFinset ∆ (H.1).edgeFinset) ∆
                  (K.edgeFinset ∆ K.edgeFinset) := by
              rw [symmDiff_self, symmDiff_bot]
            _ = ((G.1).edgeFinset ∆ K.edgeFinset) ∆
                ((H.1).edgeFinset ∆ K.edgeFinset) := by ac_rfl
        _ = ∅ := by rw [hDG, hDH, hc]; simp
    have hreal : G.1 = H.1 :=
      realization_eq_of_edgeFinset_eq (Finset.symmDiff_eq_empty.mp hsourceDiff)
    exact hne (Subtype.ext hreal)
  have hcval : cG.1.val ≠ cH.1.val := by
    intro h
    exact hcne (Subtype.ext h)
  have hGdata := residualConnectorCandidate_spec G.1 cG.2
  have hHdata := residualConnectorCandidate_spec H.1 cH.2
  have hab : a ≠ b := fun h => haS (h ▸ hbS)
  have hcGa : cG.1.val ≠ a := hGdata.2.1.ne
  have hcHa : cH.1.val ≠ a := hHdata.2.1.ne
  have hcGb : cG.1.val ≠ b := hGdata.1
  have hcHb : cH.1.val ≠ b := hHdata.1
  let p : Sym2 V := s(b, v)
  let q : Sym2 V := s(a, v)
  let rG : Sym2 V := s(a, cG.1.val)
  let sG : Sym2 V := s(b, cG.1.val)
  let rH : Sym2 V := s(a, cH.1.val)
  let sH : Sym2 V := s(b, cH.1.val)
  have hpq : p ≠ q := by
    simp [p, q, Sym2.eq_iff, hab, hab.symm, hav, hav.symm, hbv, hbv.symm]
  have hprG : p ≠ rG := by
    simp [p, rG, Sym2.eq_iff, hab, hab.symm, hbv, hbv.symm, cG.1.property,
      cG.1.property.symm, hcGb, hcGb.symm]
  have hpsG : p ≠ sG := by
    simp [p, sG, Sym2.eq_iff, hbv, hbv.symm, cG.1.property, cG.1.property.symm,
      hcGb, hcGb.symm]
  have hprH : p ≠ rH := by
    simp [p, rH, Sym2.eq_iff, hab, hab.symm, hbv, hbv.symm, cH.1.property,
      cH.1.property.symm, hcHb, hcHb.symm]
  have hpsH : p ≠ sH := by
    simp [p, sH, Sym2.eq_iff, hbv, hbv.symm, cH.1.property, cH.1.property.symm,
      hcHb, hcHb.symm]
  have hqrG : q ≠ rG := by
    simp [q, rG, Sym2.eq_iff, hav, hav.symm, cG.1.property, cG.1.property.symm,
      hcGa, hcGa.symm]
  have hqsG : q ≠ sG := by
    simp [q, sG, Sym2.eq_iff, hab, hab.symm, hav, hav.symm, hbv, hbv.symm,
      cG.1.property, cG.1.property.symm, hcGa, hcGa.symm]
  have hqrH : q ≠ rH := by
    simp [q, rH, Sym2.eq_iff, hav, hav.symm, cH.1.property, cH.1.property.symm,
      hcHa, hcHa.symm]
  have hqsH : q ≠ sH := by
    simp [q, sH, Sym2.eq_iff, hab, hab.symm, hav, hav.symm, hbv, hbv.symm,
      cH.1.property, cH.1.property.symm, hcHa, hcHa.symm]
  have hrGsG : rG ≠ sG := by
    simp [rG, sG, Sym2.eq_iff, hab, hab.symm, hcGa, hcGa.symm, hcGb, hcGb.symm]
  have hrGrH : rG ≠ rH := by
    simp [rG, rH, Sym2.eq_iff, hcval, hcval.symm, hcGa, hcGa.symm, hcHa, hcHa.symm]
  have hrGsH : rG ≠ sH := by
    simp [rG, sH, Sym2.eq_iff, hab, hab.symm, hcGa, hcGa.symm, hcHa, hcHa.symm,
      hcGb, hcGb.symm, hcHb, hcHb.symm]
  have hsGrH : sG ≠ rH := by
    simp [sG, rH, Sym2.eq_iff, hab, hab.symm, hcGa, hcGa.symm, hcGb, hcGb.symm,
      hcHa, hcHa.symm, hcHb, hcHb.symm]
  have hsGsH : sG ≠ sH := by
    simp [sG, sH, Sym2.eq_iff, hcval, hcval.symm, hcGb, hcGb.symm, hcHb, hcHb.symm]
  have hrHsH : rH ≠ sH := by
    simp [rH, sH, Sym2.eq_iff, hab, hab.symm, hcHa, hcHa.symm, hcHb, hcHb.symm]
  have hxor : ({p, rG, q, sG} : Finset (Sym2 V)) ∆ {p, rH, q, sH} =
      {rG, sG, rH, sH} := by
    ext e
    by_cases hep : e = p
    · subst e
      simp_all [Finset.mem_symmDiff]
    · by_cases heq : e = q
      · subst e
        simp_all [Finset.mem_symmDiff]
      · by_cases herG : e = rG
        · subst e
          simp_all [Finset.mem_symmDiff]
        · by_cases hesG : e = sG
          · subst e
            simp_all [Finset.mem_symmDiff]
          · by_cases herH : e = rH
            · subst e
              simp_all [Finset.mem_symmDiff]
            · by_cases hesH : e = sH
              · subst e
                simp_all [Finset.mem_symmDiff]
              · simp_all [Finset.mem_symmDiff]
  have hsourceDiff : (G.1).edgeFinset ∆ (H.1).edgeFinset = {rG, sG, rH, sH} := by
    calc
      (G.1).edgeFinset ∆ (H.1).edgeFinset =
          ((G.1).edgeFinset ∆ K.edgeFinset) ∆ ((H.1).edgeFinset ∆ K.edgeFinset) := by
        calc
          (G.1).edgeFinset ∆ (H.1).edgeFinset =
              ((G.1).edgeFinset ∆ (H.1).edgeFinset) ∆
                (K.edgeFinset ∆ K.edgeFinset) := by
            rw [symmDiff_self, symmDiff_bot]
          _ = ((G.1).edgeFinset ∆ K.edgeFinset) ∆
              ((H.1).edgeFinset ∆ K.edgeFinset) := by ac_rfl
      _ = ({p, rG, q, sG} : Finset (Sym2 V)) ∆ {p, rH, q, sH} := by
        simpa [p, q, rG, sG, rH, sH] using congrArg₂ (· ∆ ·) hDG hDH
      _ = {rG, sG, rH, sH} := hxor
  apply hnot
  change ((G.1).edgeFinset ∆ (H.1).edgeFinset).card = 4
  rw [hsourceDiff, Finset.card_eq_four]
  exact ⟨rG, sG, rH, sH, hrGsG, hrGrH, hrGsH, hsGrH, hsGsH, hrHsH, rfl⟩

/-- Theorem 5.8 (exact colour expansion), at the realization-graph boundary. If `col` is a proper
two-colouring of the source fibre, then the connector neighbourhood of every finite subset of one
colour class has exactly `k` targets per source, where `k` is the value from Theorem 5.7. -/
theorem theorem_5_8_exact_color_expansion {d : V → ℕ} {S : Finset V} {v a b : V}
    (hbS : b ∈ S) (haS : a ∉ S)
    (hSreal : HasRealizationWithNeighborSet d v S)
    (hTreal : HasRealizationWithNeighborSet d v (insert a (S.erase b)))
    (hav : a ≠ v) (hbv : b ≠ v)
    (col : interfaceFibre d v S → Bool)
    (hcol : ∀ G H, (interfaceFibreGraph d v S).Adj G H → col G ≠ col H)
    (i : Bool) (A : Finset (interfaceFibre d v S))
    (hA : ∀ G ∈ A, col G = i) :
    (connectorNeighborhood hbS haS hav hbv A).card =
      max 1 (residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩) *
        A.card := by
  classical
  let k := max 1
    (residualDegree d v S ⟨a, hav⟩ - residualDegree d v S ⟨b, hbv⟩)
  have htriangle : (interfaceFibreGraph d v S).CliqueFree 3 :=
    cliqueFree_three_of_proper_bool (interfaceFibreGraph d v S) col hcol
  have hdegree : ∀ G : interfaceFibre d v S,
      (sSideConnectorTargets G.1 G.2 hbS haS hav hbv).card = k :=
    (theorem_5_7_cross_degree hbS haS hSreal hTreal hav hbv htriangle).2
  have hpair : (A : Set (interfaceFibre d v S)).PairwiseDisjoint
      (fun G => sSideConnectorTargets G.1 G.2 hbS haS hav hbv) := by
    intro G hGA H hHA hne
    apply connectorTargets_disjoint_of_not_adj hbS haS hav hbv G H hne
    intro hGH
    apply hcol G H hGH
    exact (hA G hGA).trans (hA H hHA).symm
  calc
    (connectorNeighborhood hbS haS hav hbv A).card =
        ∑ G ∈ A, (sSideConnectorTargets G.1 G.2 hbS haS hav hbv).card := by
      exact Finset.card_biUnion hpair
    _ = ∑ _G ∈ A, k := by
      apply Finset.sum_congr rfl
      intro G _hG
      exact hdegree G
    _ = k * A.card := by simp [Nat.mul_comm]

#print axioms interface_identity_one
#print axioms interface_identity_two
#print axioms interface_edge_degree_difference
#print axioms BipartiteInterface.edge_component_biregular
#print axioms BipartiteInterface.edgeFreeComponent_support_eq_singleton
#print axioms BipartiteInterface.biregular_matching
#print axioms interfaceFibre
#print axioms interfaceFibreGraph
#print axioms connectorNeighborhood
#print axioms lemma_5_7a
#print axioms interfaceWitnessCount_eq_degree_sub_of_gt
#print axioms interfaceWitnessCount_le_one_of_degree_eq
#print axioms interfaceWitnessCount_eq_zero_of_lt
#print axioms theorem_5_7_cross_degree
#print axioms cliqueFree_three_of_proper_bool
#print axioms realization_eq_of_edgeFinset_eq
#print axioms connectorTargets_disjoint_of_not_adj
#print axioms theorem_5_8_exact_color_expansion

end Brualdi.RealizationGraph
