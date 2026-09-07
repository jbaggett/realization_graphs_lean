/-
Copyright (c) 2026 Jeffrey S. Baggett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey S. Baggett
-/
import BrualdiLean.ColemanDefs

set_option autoImplicit false
set_option linter.style.nativeDecide false

namespace Brualdi.Ledger

abbrev CrownV := Fin 12

/-- The bipartition colour on `K_{6,6} - 6K_2`: `false` for `a_0,...,a_5`,
    `true` for `b_0,...,b_5`. -/
def crownColor (v : CrownV) : Bool :=
  decide (6 ≤ v.val)

/-- The crown graph `K_{6,6} - 6K_2`, encoded on `Fin 12`. -/
def crownGraph : SimpleGraph CrownV where
  Adj u v := crownColor u ≠ crownColor v ∧ u.val % 6 ≠ v.val % 6
  symm := { symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩ }
  loopless := { irrefl := fun _ h => h.1 rfl }

instance : DecidableRel crownGraph.Adj := by
  intro u v
  unfold crownGraph
  infer_instance

private def crownAdjB (u v : CrownV) : Bool :=
  decide (crownGraph.Adj u v)

private def crownVerts : List CrownV :=
  List.finRange 12

private def firstSome {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f =>
      match f x with
      | some y => some y
      | none => firstSome xs f

private def pathOnDfs (target : CrownV) :
    Nat → List CrownV → List CrownV → Option (List CrownV)
  | 0, _, _ => none
  | fuel + 1, todo, pathRev =>
      match pathRev with
      | [] => none
      | cur :: _ =>
          if todo.isEmpty then
            if cur = target then some pathRev.reverse else none
          else
            firstSome (todo.filter fun v => crownAdjB cur v) fun v =>
              pathOnDfs target fuel (todo.erase v) (v :: pathRev)

private def findPathOn (allowed : List CrownV) (source target : CrownV) : Option (List CrownV) :=
  if decide (allowed.Nodup ∧ source ∈ allowed ∧ target ∈ allowed) then
    pathOnDfs target (allowed.length + 1) (allowed.erase source) [source]
  else
    none

private def complementVerts (used : List CrownV) : List CrownV :=
  crownVerts.filter fun v => decide (v ∉ used)

private def pairDfs (b₁ a₂ b₂ : CrownV) :
    Nat → List CrownV → Option (List CrownV × List CrownV)
  | 0, _ => none
  | fuel + 1, pathRev =>
      match pathRev with
      | [] => none
      | cur :: _ =>
          if cur = b₁ then
            match findPathOn (complementVerts pathRev) a₂ b₂ with
            | some q => some (pathRev.reverse, q)
            | none => none
          else
            let candidates :=
              crownVerts.filter fun v =>
                crownAdjB cur v &&
                  decide (v ∉ pathRev) &&
                  decide (v ≠ a₂) &&
                  decide (v ≠ b₂)
            firstSome candidates fun v =>
              pairDfs b₁ a₂ b₂ fuel (v :: pathRev)

/-- Insert an index unless it has already appeared. -/
private def appendNew (xs : List Nat) (x : Nat) : List Nat :=
  if x ∈ xs then xs else xs ++ [x]

/-- A simultaneous relabelling of the six missing-edge indices.  The two
`A` endpoints come first, followed by any new `B` endpoint indices and then
the unused indices. -/
private def canonicalNames (p r q s : Nat) : List Nat :=
  let used := appendNew (appendNew [p, r] q) s
  used ++ ((List.range 6).filter fun x ↦ x ∉ used)

/-- The seven equality patterns possible for two distinct `A` indices and
two distinct `B` indices, after simultaneous relabelling.  Each pair of lists
is a spanning pair of paths in `K_{6,6} - 6K₂`. -/
private def canonicalPaths : Nat → Nat → List Nat × List Nat
  | 0, 1 => ([0, 9, 2, 6], [1, 8, 4, 11, 3, 10, 5, 7])
  | 1, 0 => ([0, 7], [1, 8, 3, 10, 2, 11, 4, 9, 5, 6])
  | 0, 2 => ([0, 7, 2, 6], [1, 9, 4, 11, 3, 10, 5, 8])
  | 1, 2 => ([0, 7], [1, 6, 2, 9, 4, 11, 3, 10, 5, 8])
  | 2, 0 => ([0, 8], [1, 9, 2, 7, 4, 11, 3, 10, 5, 6])
  | 2, 1 => ([0, 8], [1, 6, 2, 9, 4, 11, 3, 10, 5, 7])
  | 2, 3 => ([0, 8], [1, 6, 2, 7, 4, 11, 3, 10, 5, 9])
  | _, _ => ([], [])

private def asCrownV (n : Nat) : CrownV :=
  ⟨n % 12, Nat.mod_lt _ (by decide)⟩

/-- Apply the same index permutation in both colour classes. -/
private def renameCanonical (names : List Nat) (v : Nat) : CrownV :=
  if v < 6 then
    asCrownV (names.getD v 0)
  else
    asCrownV (6 + names.getD (v - 6) 0)

/-- Direct constructive certificate.  Reversing a canonical path handles a
demand whose first endpoint lies in the `B` colour class. -/
private def directCert (a₁ b₁ a₂ b₂ : CrownV) : List CrownV × List CrownV :=
  let swap₁ := crownColor a₁
  let swap₂ := crownColor a₂
  let aa₁ := if swap₁ then b₁ else a₁
  let bb₁ := if swap₁ then a₁ else b₁
  let aa₂ := if swap₂ then b₂ else a₂
  let bb₂ := if swap₂ then a₂ else b₂
  let p := aa₁.val % 6
  let r := aa₂.val % 6
  let q := bb₁.val % 6
  let s := bb₂.val % 6
  let names := canonicalNames p r q s
  let pattern := canonicalPaths (names.idxOf q) (names.idxOf s)
  let xs := pattern.1.map (renameCanonical names)
  let ys := pattern.2.map (renameCanonical names)
  (if swap₁ then xs.reverse else xs, if swap₂ then ys.reverse else ys)

private def findCert (a₁ b₁ a₂ b₂ : CrownV) : Option (List CrownV × List CrownV) :=
  some (directCert a₁ b₁ a₂ b₂)

private def ValidCert (a₁ b₁ a₂ b₂ : CrownV) (xs ys : List CrownV) : Prop :=
  xs.head? = some a₁ ∧
  xs.getLast? = some b₁ ∧
  ys.head? = some a₂ ∧
  ys.getLast? = some b₂ ∧
  xs.IsChain crownGraph.Adj ∧
  ys.IsChain crownGraph.Adj ∧
  xs.Nodup ∧
  ys.Nodup ∧
  (∀ x : CrownV, x ∈ xs ∨ x ∈ ys) ∧
  (∀ x : CrownV, ¬ (x ∈ xs ∧ x ∈ ys))

private def chainB : List CrownV → Bool
  | [] => true
  | [_] => true
  | x :: y :: zs => crownAdjB x y && chainB (y :: zs)

private theorem chainB_sound {xs : List CrownV} (h : chainB xs = true) :
    xs.IsChain crownGraph.Adj := by
  induction xs with
  | nil =>
      exact .nil
  | cons x xs ih =>
      cases xs with
      | nil =>
          exact .singleton x
      | cons y ys =>
          rw [chainB, Bool.and_eq_true] at h
          exact .cons_cons (of_decide_eq_true h.1) (ih h.2)

private theorem list_all_sound {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.all p = true) {x : α} (hx : x ∈ xs) : p x = true := by
  have hall : ∀ y ∈ xs, p y = true := by
    simpa [List.all_eq_true] using h
  exact hall x hx

private def coversB (xs ys : List CrownV) : Bool :=
  crownVerts.all fun x => decide (x ∈ xs ∨ x ∈ ys)

private theorem coversB_sound {xs ys : List CrownV} (h : coversB xs ys = true) :
    ∀ x : CrownV, x ∈ xs ∨ x ∈ ys := by
  intro x
  have hx : x ∈ crownVerts := by
    simp [crownVerts]
  exact of_decide_eq_true (list_all_sound h hx)

private def disjointB (xs ys : List CrownV) : Bool :=
  crownVerts.all fun x => decide (¬ (x ∈ xs ∧ x ∈ ys))

private theorem disjointB_sound {xs ys : List CrownV} (h : disjointB xs ys = true) :
    ∀ x : CrownV, ¬ (x ∈ xs ∧ x ∈ ys) := by
  intro x
  have hx : x ∈ crownVerts := by
    simp [crownVerts]
  exact of_decide_eq_true (list_all_sound h hx)

private def headOk (x : CrownV) (xs : List CrownV) : Bool :=
  decide (xs.head? = some x)

private def lastOk (x : CrownV) (xs : List CrownV) : Bool :=
  decide (xs.getLast? = some x)

private def nodupB (xs : List CrownV) : Bool :=
  decide xs.Nodup

private def coverOk (xs ys : List CrownV) : Bool :=
  coversB xs ys

private def disjointOk (xs ys : List CrownV) : Bool :=
  disjointB xs ys

private def validCertChecks (a₁ b₁ a₂ b₂ : CrownV) (xs ys : List CrownV) : List Bool :=
  [ headOk a₁ xs,
    lastOk b₁ xs,
    headOk a₂ ys,
    lastOk b₂ ys,
    chainB xs,
    chainB ys,
    nodupB xs,
    nodupB ys,
    coverOk xs ys,
    disjointOk xs ys ]

private def validCertBool (a₁ b₁ a₂ b₂ : CrownV) (xs ys : List CrownV) : Bool :=
  (validCertChecks a₁ b₁ a₂ b₂ xs ys).all id

private theorem validCertBool_sound {a₁ b₁ a₂ b₂ : CrownV} {xs ys : List CrownV}
    (h : validCertBool a₁ b₁ a₂ b₂ xs ys = true) :
    ValidCert a₁ b₁ a₂ b₂ xs ys := by
  have hchecks : (validCertChecks a₁ b₁ a₂ b₂ xs ys).all id = true := by
    simpa [validCertBool] using h
  have hxsHead : headOk a₁ xs = true :=
    list_all_sound (p := id) hchecks (x := headOk a₁ xs) (by simp [validCertChecks])
  have hxsLast : lastOk b₁ xs = true :=
    list_all_sound (p := id) hchecks (x := lastOk b₁ xs) (by simp [validCertChecks])
  have hysHead : headOk a₂ ys = true :=
    list_all_sound (p := id) hchecks (x := headOk a₂ ys) (by simp [validCertChecks])
  have hysLast : lastOk b₂ ys = true :=
    list_all_sound (p := id) hchecks (x := lastOk b₂ ys) (by simp [validCertChecks])
  have hxsChain : chainB xs = true :=
    list_all_sound (p := id) hchecks (x := chainB xs) (by simp [validCertChecks])
  have hysChain : chainB ys = true :=
    list_all_sound (p := id) hchecks (x := chainB ys) (by simp [validCertChecks])
  have hxsNodup : nodupB xs = true :=
    list_all_sound (p := id) hchecks (x := nodupB xs) (by simp [validCertChecks])
  have hysNodup : nodupB ys = true :=
    list_all_sound (p := id) hchecks (x := nodupB ys) (by simp [validCertChecks])
  have hcover : coverOk xs ys = true :=
    list_all_sound (p := id) hchecks (x := coverOk xs ys) (by simp [validCertChecks])
  have hdisjoint : disjointOk xs ys = true :=
    list_all_sound (p := id) hchecks (x := disjointOk xs ys) (by simp [validCertChecks])
  exact
    ⟨of_decide_eq_true (by simpa [headOk] using hxsHead),
      of_decide_eq_true (by simpa [lastOk] using hxsLast),
      of_decide_eq_true (by simpa [headOk] using hysHead),
      of_decide_eq_true (by simpa [lastOk] using hysLast),
      chainB_sound hxsChain, chainB_sound hysChain,
      of_decide_eq_true (by simpa [nodupB] using hxsNodup),
      of_decide_eq_true (by simpa [nodupB] using hysNodup),
      coversB_sound (by simpa [coverOk] using hcover),
      disjointB_sound (by simpa [disjointOk] using hdisjoint)⟩

private theorem head_eq_of_head?_eq_some {α : Type} {xs : List α} {x : α}
    (hxs : xs.head? = some x) (hne : xs ≠ []) : xs.head hne = x := by
  rw [List.head?_eq_some_head hne] at hxs
  exact Option.some.inj hxs

private theorem getLast_eq_of_getLast?_eq_some {α : Type} {xs : List α} {x : α}
    (hxs : xs.getLast? = some x) (hne : xs ≠ []) : xs.getLast hne = x := by
  rw [List.getLast?_eq_getLast_of_ne_nil hne] at hxs
  exact Option.some.inj hxs

private theorem validCert_to_spanning {a₁ b₁ a₂ b₂ : CrownV} {xs ys : List CrownV}
    (h : ValidCert a₁ b₁ a₂ b₂ xs ys) :
    ∃ (p : crownGraph.Walk a₁ b₁) (q : crownGraph.Walk a₂ b₂),
      p.IsPath ∧ q.IsPath ∧
      (∀ x, x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ x, ¬ (x ∈ p.support ∧ x ∈ q.support)) := by
  rcases h with
    ⟨hxsHead, hxsLast, hysHead, hysLast, hxsChain, hysChain, hxsNodup, hysNodup,
      hcover, hdisjoint⟩
  have hxs_ne : xs ≠ [] := by
    intro hnil
    simp [hnil] at hxsHead
  have hys_ne : ys ≠ [] := by
    intro hnil
    simp [hnil] at hysHead
  let p₀ : crownGraph.Walk (xs.head hxs_ne) (xs.getLast hxs_ne) :=
    SimpleGraph.Walk.ofSupport xs hxs_ne hxsChain
  let q₀ : crownGraph.Walk (ys.head hys_ne) (ys.getLast hys_ne) :=
    SimpleGraph.Walk.ofSupport ys hys_ne hysChain
  have hpStart : xs.head hxs_ne = a₁ := head_eq_of_head?_eq_some hxsHead hxs_ne
  have hpEnd : xs.getLast hxs_ne = b₁ := getLast_eq_of_getLast?_eq_some hxsLast hxs_ne
  have hqStart : ys.head hys_ne = a₂ := head_eq_of_head?_eq_some hysHead hys_ne
  have hqEnd : ys.getLast hys_ne = b₂ := getLast_eq_of_getLast?_eq_some hysLast hys_ne
  let p : crownGraph.Walk a₁ b₁ := p₀.copy hpStart hpEnd
  let q : crownGraph.Walk a₂ b₂ := q₀.copy hqStart hqEnd
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · simpa [p, p₀, SimpleGraph.Walk.support_copy] using
      (SimpleGraph.Walk.IsPath.mk' (by
        simpa [p₀] using hxsNodup) : p₀.IsPath)
  · simpa [q, q₀, SimpleGraph.Walk.support_copy] using
      (SimpleGraph.Walk.IsPath.mk' (by
        simpa [q₀] using hysNodup) : q₀.IsPath)
  · intro x
    simpa [p, q, p₀, q₀, SimpleGraph.Walk.support_copy] using hcover x
  · intro x
    simpa [p, q, p₀, q₀, SimpleGraph.Walk.support_copy] using hdisjoint x

private def certOK (a₁ b₁ a₂ b₂ : CrownV) : Bool :=
  match findCert a₁ b₁ a₂ b₂ with
  | some (xs, ys) => validCertBool a₁ b₁ a₂ b₂ xs ys
  | none => false

private def CrownAdmissible (a₁ b₁ a₂ b₂ : CrownV) : Prop :=
  crownColor a₁ ≠ crownColor b₁ ∧
  crownColor a₂ ≠ crownColor b₂ ∧
  a₁ ≠ a₂ ∧ a₁ ≠ b₂ ∧ b₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ a₁ ≠ b₁ ∧ a₂ ≠ b₂

private def crownAdmissibleB (a₁ b₁ a₂ b₂ : CrownV) : Bool :=
  decide (crownColor a₁ ≠ crownColor b₁) &&
  decide (crownColor a₂ ≠ crownColor b₂) &&
  decide (a₁ ≠ a₂) &&
  decide (a₁ ≠ b₂) &&
  decide (b₁ ≠ a₂) &&
  decide (b₁ ≠ b₂) &&
  decide (a₁ ≠ b₁) &&
  decide (a₂ ≠ b₂)

/-- The portion of the crown certificate check with its first endpoint fixed. -/
private def crownSpan2At (a₁ : CrownV) : Bool :=
  crownVerts.all fun b₁ =>
    crownVerts.all fun a₂ =>
      crownVerts.all fun b₂ =>
        if crownAdmissibleB a₁ b₁ a₂ b₂ then
          certOK a₁ b₁ a₂ b₂
        else
          true

/-- Boolean certificate check for the full paired-2-DPC crown base case. -/
def crownSpan2 : Bool :=
  crownVerts.all crownSpan2At

/- Splitting the closed reduction by first endpoint keeps each pure-kernel
`decide` invocation well below the declaration heartbeat limit. -/
private theorem crownSpan2At_0 : crownSpan2At (0 : CrownV) = true := by decide
private theorem crownSpan2At_1 : crownSpan2At (1 : CrownV) = true := by decide
private theorem crownSpan2At_2 : crownSpan2At (2 : CrownV) = true := by decide
private theorem crownSpan2At_3 : crownSpan2At (3 : CrownV) = true := by decide
private theorem crownSpan2At_4 : crownSpan2At (4 : CrownV) = true := by decide
private theorem crownSpan2At_5 : crownSpan2At (5 : CrownV) = true := by decide
private theorem crownSpan2At_6 : crownSpan2At (6 : CrownV) = true := by decide
private theorem crownSpan2At_7 : crownSpan2At (7 : CrownV) = true := by decide
private theorem crownSpan2At_8 : crownSpan2At (8 : CrownV) = true := by decide
private theorem crownSpan2At_9 : crownSpan2At (9 : CrownV) = true := by decide
private theorem crownSpan2At_10 : crownSpan2At (10 : CrownV) = true := by decide
private theorem crownSpan2At_11 : crownSpan2At (11 : CrownV) = true := by decide

private theorem crownSpan2At_verified (x : CrownV) : crownSpan2At x = true := by
  fin_cases x
  · exact crownSpan2At_0
  · exact crownSpan2At_1
  · exact crownSpan2At_2
  · exact crownSpan2At_3
  · exact crownSpan2At_4
  · exact crownSpan2At_5
  · exact crownSpan2At_6
  · exact crownSpan2At_7
  · exact crownSpan2At_8
  · exact crownSpan2At_9
  · exact crownSpan2At_10
  · exact crownSpan2At_11

private theorem crownSpan2_verified : crownSpan2 = true := by
  unfold crownSpan2
  rw [List.all_eq_true]
  intro x _
  exact crownSpan2At_verified x

private theorem crownSpan2_sound (h : crownSpan2 = true) :
    IsSpanning2DPCOpposite crownGraph crownColor := by
  intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁a₂ ha₁b₂ hb₁a₂ hb₁b₂ ha₁b₁ ha₂b₂
  have hadm : CrownAdmissible a₁ b₁ a₂ b₂ :=
    ⟨hc₁, hc₂, ha₁a₂, ha₁b₂, hb₁a₂, hb₁b₂, ha₁b₁, ha₂b₂⟩
  have ha₁mem : a₁ ∈ crownVerts := by simp [crownVerts]
  have hb₁mem : b₁ ∈ crownVerts := by simp [crownVerts]
  have ha₂mem : a₂ ∈ crownVerts := by simp [crownVerts]
  have hb₂mem : b₂ ∈ crownVerts := by simp [crownVerts]
  have h₁ := list_all_sound h ha₁mem
  have h₂ := list_all_sound h₁ hb₁mem
  have h₃ := list_all_sound h₂ ha₂mem
  have h₄ := list_all_sound h₃ hb₂mem
  have hadmB : crownAdmissibleB a₁ b₁ a₂ b₂ = true := by
    simp [crownAdmissibleB, hc₁, hc₂, ha₁a₂, ha₁b₂, hb₁a₂, hb₁b₂, ha₁b₁, ha₂b₂]
  have hok : certOK a₁ b₁ a₂ b₂ = true := by
    simpa [hadmB] using h₄
  unfold certOK at hok
  cases hcert : findCert a₁ b₁ a₂ b₂ with
  | none =>
      simp [hcert] at hok
  | some cert =>
      rcases cert with ⟨xs, ys⟩
      have hv : ValidCert a₁ b₁ a₂ b₂ xs ys := by
        exact validCertBool_sound (by simpa [hcert] using hok)
      exact validCert_to_spanning hv

/-- The crown graph `K_{6,6} - 6K_2` is paired-2-DPC / spanning-2-laceable. -/
theorem crown_spanning2_laceable : IsSpanning2DPCOpposite crownGraph crownColor := by
  exact crownSpan2_sound crownSpan2_verified

#print axioms crown_spanning2_laceable

end Brualdi.Ledger
