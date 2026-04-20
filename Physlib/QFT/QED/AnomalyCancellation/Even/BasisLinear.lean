/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear.ShiftPlane
/-!

# The combined basis of the symmetric and shifted planes

## i. Overview

This module constructs the combined basis for the linear solutions of
`PureU1 (2 * n.succ)` by combining the two ACC-satisfying planes:

- The *symmetric plane*, named after the symmetric (even) split `n.succ + n.succ`.
  Its key results are `symmPlaneLinSols` (the inclusion into linear solutions) and
  `symmPlane_accCube` (every point satisfies the cubic anomaly cancellation condition).

- The *shifted plane*, named after the shifted split `1 + (n + n + 1)`.
  Its key results are `shiftPlaneLinSols` (the inclusion into linear solutions) and
  `shiftPlane_accCube` (every point satisfies the cubic anomaly cancellation condition).

The main result is `span_basis`: every linear solution of `PureU1 (2 * n.succ)` can
be written as the sum of a point from the symmetric plane and a point from the shifted
plane.

## ii. Key results

- `basisa` : The combined basis vectors from both planes
- `basisa_linear_independent` : The combined basis vectors are linearly independent
- `basisaAsBasis` : The combined basis vectors form a basis
- `span_basis` : Every linear solution is the sum of a point from each plane

## iii. Table of contents

- E. The combined basis
  - E.1. As a map into linear solutions
  - E.2. Inclusion of the span of the basis into charges
  - E.3. Components of the inclusion into charges
  - E.4. Kernel of the inclusion into charges
  - E.5. The inclusion of the span of the basis into linear solutions
  - E.6. The combined basis vectors are linearly independent
  - E.7. Injectivity of the inclusion into linear solutions
  - E.8. Cardinality of the basis
  - E.9. The basis vectors as a basis
- F. Every linear solution is the sum of a point from each plane
  - F.1. Relation under permutations

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

## E. The combined basis

-/

/-!

### E.1. As a map into linear solutions

-/
/-- The whole basis as `LinSols`. -/
def basisa : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).LinSols := fun i =>
  match i with
  | .inl i => symmBasis i
  | .inr i => shiftBasis i

/-!

### E.2. Inclusion of the span of the basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges :=
  symmPlane f + shiftPlane g

/-!

### E.3. Components of the inclusion into charges

-/

lemma Pa_evenShiftFst (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftFst j) = f j.succ + g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlane_evenShiftFst, evenShiftFst_eq_evenFst_succ, symmPlane_evenFst]

lemma Pa_evenShiftSnd (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftSnd j) = - f j.castSucc - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlane_evenShiftSnd, evenShiftSnd_eq_evenSnd_castSucc, symmPlane_evenSnd]
  ring

lemma Pa_evenShiftZero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    Pa f g (evenShiftZero) = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlane_evenShiftZero, evenShiftZero_eq_evenFst_zero, symmPlane_evenFst]
  exact Rat.add_zero (f 0)

lemma Pa_evenShiftLast (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    Pa f g (evenShiftLast) = - f (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlane_evenShiftLast, evenShiftLast_eq_evenSnd_last, symmPlane_evenSnd]
  exact Rat.add_zero (-f (Fin.last n))

/-!

### E.4. Kernel of the inclusion into charges

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pa_zero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_evenShiftZero f g
  rw [h] at h₃
  change 0 = f 0 at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := Pa_evenShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    have h2 := Pa_evenShiftSnd f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    rw [h] at h1 h2
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    erw [hi2] at h2
    change 0 = _ at h2
    simp only [neg_zero, zero_sub, zero_eq_neg] at h2
    rw [h2] at h1
    exact right_eq_add.mp h1
  exact hinduc i.val i.prop

lemma Pa_zero_shift (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, symmPlane] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact shiftPlane_zero g h

/-!

### E.5. The inclusion of the span of the basis into linear solutions

-/
/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_symmPlaneLinSols_shiftPlaneLinSols (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    Pa' f = symmPlaneLinSols (f ∘ Sum.inl) + shiftPlaneLinSols (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined basis vectors are linearly independent

-/

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Pa'_symmPlaneLinSols_shiftPlaneLinSols] at h1
  change (symmPlaneLinSols (f ∘ Sum.inl)).val +
    (shiftPlaneLinSols (f ∘ Sum.inr)).val = 0 at h1
  rw [shiftPlaneLinSols_val, symmPlaneLinSols_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero_shift (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all
  cases i
  · simp_all
  · simp_all
/-!

### E.7. Injectivity of the inclusion into linear solutions

-/

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => (funext (fun i => ?_))) (fun h => ?_)
  · rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin (succ n) ⊕ Fin n, (f i + (- f' i)) • basisa i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib]
      rw [h]
      rw [← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 := by
      exact Fintype.linearIndependent_iff.mp (@basisa_linear_independent n)
        (fun i => f i + -f' i) h1
    have h2i := h2 i
    linarith
  · rw [h]

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_symmPlaneLinSols_shiftPlaneLinSols, Pa'_symmPlaneLinSols_shiftPlaneLinSols]
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
      symmPlaneLinSols_val, shiftPlaneLinSols_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← Pa'_elim_eq_iff, ← Sum.elim_eq_iff]
  exact Pa'_eq _ _

/-!

### E.8. Cardinality of the basis

-/

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n)) =
    Module.finrank ℚ (PureU1 (2 * n.succ)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin, mul_eq]
  exact split_odd n

/-!

### E.9. The basis vectors as a basis

-/

/-- The basis formed out of our `basisa` vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin (succ n) ⊕ Fin n) ℚ (PureU1 (2 * succ n)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

/-!

## F. Every linear solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ)).LinSols) :
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ), S.val = symmPlane g + shiftPlane f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change symmPlaneLinSols _ + shiftPlaneLinSols _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
    symmPlaneLinSols_val, shiftPlaneLinSols_val]
  rfl

/-!

### F.1. Relation under permutations

-/
lemma span_basis_swapShift {S : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    (h : S.val = symmPlane g + shiftPlane f) : ∃ (g' : Fin n.succ → ℚ) (f' : Fin n → ℚ),
      S'.val = symmPlane g' + shiftPlane f' ∧ shiftPlane f' = shiftPlane f +
      (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j ∧ g' = g := by
  let X := shiftPlane f +
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j
  have hX : X ∈ Submodule.span ℚ (Set.range (shiftBasisAsCharges)) := by
    apply Submodule.add_mem
    exact (shiftPlane_in_span f)
    exact (smul_shiftBasisAsCharges_in_span S j)
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change shiftPlane f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← h]
  apply swapShift_as_add at hS
  exact hS

end VectorLikeEvenPlane

end PureU1
