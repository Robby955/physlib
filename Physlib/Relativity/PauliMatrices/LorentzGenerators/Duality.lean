/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.PauliMatrices.LorentzGenerators
public import Physlib.Relativity.Tensors.LeviCivita.Complex
/-!

# Duality of chiral Lorentz generators

## i. Overview

This file proves the duality identities for the Lorentz generators in the left- and
right-handed Weyl representations. With metric signature `(+---)` and
`\epsilon^{0123} = 1`, they obey

`\sigma^{\mu\nu} = -(i/2)\epsilon^{\mu\nu\rho\kappa}\sigma_{\rho\kappa}`

and

`\bar\sigma^{\mu\nu} =
  (i/2)\epsilon^{\mu\nu\rho\kappa}\bar\sigma_{\rho\kappa}`.

Thus the left-handed generators have Hodge-star eigenvalue `+i`, while the right-handed
generators have eigenvalue `-i`.

## ii. Key results

- `leftLorentzGenerator_selfDual` proves self-duality of the left-handed generators.
- `rightLorentzGenerator_antiSelfDual` proves anti-self-duality of the right-handed generators.

## iii. Table of contents

- A. Left-handed lowering and epsilon contractions
- B. Right-handed lowering and epsilon contractions
- C. Self-duality

## iv. References

-/

@[expose] public section

noncomputable section

open Matrix
open TensorProduct

namespace PauliMatrix
open Fermion
open complexLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. Left-handed lowering and epsilon contractions

-/

/-- The diagonal sign of the Lorentz metric with signature `(+---)`. -/
private def metricSign (mu : Fin 4) : Physlib.RatComplexNum :=
  if mu.val = 0 then 1 else -1

/-- Index colors after lowering the first Lorentz index of the left generators. -/
private noncomputable abbrev leftLorentzGeneratorLowerFirstColors : Fin 4 → Color :=
  Function.update ![Color.up, Color.up, Color.upL, Color.downL] 0
    (complexLorentzTensor.τ (![Color.up, Color.up, Color.upL, Color.downL] 0))

/-- Index colors after lowering both Lorentz indices of the left generators. -/
private noncomputable abbrev leftLorentzGeneratorLowerBothColors : Fin 4 → Color :=
  Function.update
    (Function.update ![Color.up, Color.up, Color.upL, Color.downL] 0
      (complexLorentzTensor.τ (![Color.up, Color.up, Color.upL, Color.downL] 0)))
    1
    (complexLorentzTensor.τ
      (Function.update ![Color.up, Color.up, Color.upL, Color.downL] 0
        (complexLorentzTensor.τ (![Color.up, Color.up, Color.upL, Color.downL] 0)) 1))

/-- Components of the left generators with their first Lorentz index lowered. -/
private def leftLorentzGeneratorLowerFirstRawComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leftLorentzGeneratorLowerFirstColors) : Physlib.RatComplexNum :=
  metricSign (b 0) * leftLorentzGeneratorComponent (b 0) (b 1) (b 2) (b 3)

set_option backward.isDefEq.respectTransparency false in
-- Dependent color normalization through `crossToSlot` exceeds the default recursion depth.
set_option maxRecDepth 2000 in
private lemma leftLorentzGeneratorLowerFirstRaw_eq_ofRat :
    toDualMapAtIndex (S := complexLorentzTensor) 0 leftLorentzGenerator =
      ofRat leftLorentzGeneratorLowerFirstRawComponent := by
  rw [leftLorentzGenerator_eq_ofRat, toDualMapAtIndex]
  change crossToSlot (S := complexLorentzTensor) 0 0 rfl η' (ofRat _) = _
  rw [crossToSlot_eq_crossToEnd, crossToEnd]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [coMetric_eq_ofRat]
  rw [prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat, permT_ofRat, permT_ofRat]
  congr 1
  funext b
  revert b
  decide +kernel

/-- Components of the left generators with both Lorentz indices lowered. -/
private def leftLorentzGeneratorLowerBothRawComponentArgs
    (mu nu : Fin 4) (a c : Fin 2) : Physlib.RatComplexNum :=
  metricSign mu * metricSign nu * leftLorentzGeneratorComponent mu nu a c

/-- Tensor-indexed components of the left generators with both Lorentz indices lowered. -/
private def leftLorentzGeneratorLowerBothRawComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leftLorentzGeneratorLowerBothColors) : Physlib.RatComplexNum :=
  leftLorentzGeneratorLowerBothRawComponentArgs (b 0) (b 1) (b 2) (b 3)

set_option backward.isDefEq.respectTransparency false in
-- Dependent color normalization through `crossToSlot` exceeds the default recursion depth.
set_option maxRecDepth 2000 in
private lemma leftLorentzGeneratorLowerBothRaw_eq_ofRat :
    toDualMapAtIndex (S := complexLorentzTensor) 1
      (toDualMapAtIndex (S := complexLorentzTensor) 0 leftLorentzGenerator) =
      ofRat leftLorentzGeneratorLowerBothRawComponent := by
  rw [leftLorentzGeneratorLowerFirstRaw_eq_ofRat, toDualMapAtIndex]
  change crossToSlot (S := complexLorentzTensor) 1 0 rfl η' (ofRat _) = _
  rw [crossToSlot_eq_crossToEnd, crossToEnd]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [coMetric_eq_ofRat]
  rw [prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat, permT_ofRat, permT_ofRat]
  congr 1
  funext b
  revert b
  decide +kernel

/-- Rational-complex components of the complex Levi-Civita tensor. -/
private def leviCivitaComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      ![Color.up, Color.up, Color.up, Color.up]) : Physlib.RatComplexNum :=
  ⟨KroneckerDelta.generalizedKroneckerDelta
    (fun i => Fin.cast (by fin_cases i <;> rfl) (b i)) (id : Fin 4 → Fin 4), 0⟩

/-- Index colors of the complex Levi-Civita tensor. -/
private noncomputable abbrev leviCivitaColors : Fin 4 → Color :=
  ![Color.up, Color.up, Color.up, Color.up]

/-- Index colors before contracting the Levi-Civita tensor with the lowered left generators. -/
private noncomputable abbrev leviCivitaLeftLowerBothProductColors : Fin 8 → Color :=
  Fin.append leviCivitaColors leftLorentzGeneratorLowerBothColors

/-- Components before contracting the Levi-Civita tensor with the lowered left generators. -/
private noncomputable def leviCivitaLeftLowerBothProductComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leviCivitaLeftLowerBothProductColors) : Physlib.RatComplexNum :=
  leviCivitaComponent (ComponentIdx.prod b).1 *
    leftLorentzGeneratorLowerBothRawComponent (ComponentIdx.prod b).2

private lemma leviCivita_prod_leftLowerBoth_eq_ofRat :
    prodT ε4ℂ
      (toDualMapAtIndex (S := complexLorentzTensor) 1
        (toDualMapAtIndex (S := complexLorentzTensor) 0 leftLorentzGenerator)) =
      ofRat leviCivitaLeftLowerBothProductComponent := by
  rw [leftLorentzGeneratorLowerBothRaw_eq_ofRat, leviCivita_eq_ofRat,
    prodT_ofRat_ofRat]
  rfl

private lemma leviCivitaLeftLowerBothContractKappa_valid :
    (3 : Fin 8) ≠ 5 ∧
      complexLorentzTensor.τ (leviCivitaLeftLowerBothProductColors 3) =
        leviCivitaLeftLowerBothProductColors 5 := by
  decide

/-- Index colors after the first Levi-Civita contraction for the left generators. -/
private noncomputable abbrev leviCivitaLeftLowerBothContractKappaColors : Fin 6 → Color :=
  leviCivitaLeftLowerBothProductColors ∘ Fin.succSuccAbove (3 : Fin 8) 5

/-- Components after the first Levi-Civita contraction for the left generators. -/
private noncomputable def leviCivitaLeftLowerBothContractKappaComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leviCivitaLeftLowerBothContractKappaColors) : Physlib.RatComplexNum :=
  ∑ x : Fin (complexLorentzTensor.repDim
      (leviCivitaLeftLowerBothProductColors (3 : Fin 8))),
    leviCivitaLeftLowerBothProductComponent
      (ComponentIdx.DropPairSection.ofFinEquiv
        leviCivitaLeftLowerBothContractKappa_valid.1 b
        (x, Fin.cast (by
          simp [← leviCivitaLeftLowerBothContractKappa_valid.2,
            complexLorentzTensor.repDim_tau]) x))

private lemma leviCivitaLeftLowerBoth_contractKappa_eq_ofRat :
    contrT 6 (3 : Fin 8) 5 leviCivitaLeftLowerBothContractKappa_valid
      (ofRat leviCivitaLeftLowerBothProductComponent) =
      ofRat leviCivitaLeftLowerBothContractKappaComponent := by
  rw [contrT_ofRat]
  rfl

private lemma leviCivitaLeftLowerBothContractRho_valid :
    (2 : Fin 6) ≠ 3 ∧
      complexLorentzTensor.τ (leviCivitaLeftLowerBothContractKappaColors 2) =
        leviCivitaLeftLowerBothContractKappaColors 3 := by
  decide

/-- Index colors after both Levi-Civita contractions for the left generators. -/
private noncomputable abbrev leviCivitaLeftLowerBothContractRhoColors : Fin 4 → Color :=
  leviCivitaLeftLowerBothContractKappaColors ∘ Fin.succSuccAbove (2 : Fin 6) 3

/-- Components after both Levi-Civita contractions for the left generators. -/
private noncomputable def leviCivitaLeftLowerBothContractRhoComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leviCivitaLeftLowerBothContractRhoColors) : Physlib.RatComplexNum :=
  ∑ x : Fin (complexLorentzTensor.repDim
      (leviCivitaLeftLowerBothContractKappaColors (2 : Fin 6))),
    leviCivitaLeftLowerBothContractKappaComponent
      (ComponentIdx.DropPairSection.ofFinEquiv
        leviCivitaLeftLowerBothContractRho_valid.1 b
        (x, Fin.cast (by decide) x))

private lemma leviCivitaLeftLowerBoth_contractRho_eq_ofRat :
    contrT 4 (2 : Fin 6) 3 leviCivitaLeftLowerBothContractRho_valid
      (ofRat leviCivitaLeftLowerBothContractKappaComponent) =
      ofRat leviCivitaLeftLowerBothContractRhoComponent := by
  rw [contrT_ofRat]
  rfl

/-!

## B. Right-handed lowering and epsilon contractions

-/

/-- Index colors after lowering the first Lorentz index of the right generators. -/
private noncomputable abbrev rightLorentzGeneratorLowerFirstColors : Fin 4 → Color :=
  Function.update ![Color.up, Color.up, Color.downR, Color.upR] 0
    (complexLorentzTensor.τ (![Color.up, Color.up, Color.downR, Color.upR] 0))

/-- Index colors after lowering both Lorentz indices of the right generators. -/
private noncomputable abbrev rightLorentzGeneratorLowerBothColors : Fin 4 → Color :=
  Function.update
    (Function.update ![Color.up, Color.up, Color.downR, Color.upR] 0
      (complexLorentzTensor.τ (![Color.up, Color.up, Color.downR, Color.upR] 0)))
    1
    (complexLorentzTensor.τ
      (Function.update ![Color.up, Color.up, Color.downR, Color.upR] 0
        (complexLorentzTensor.τ (![Color.up, Color.up, Color.downR, Color.upR] 0)) 1))

/-- Components of the right generators with their first Lorentz index lowered. -/
private def rightLorentzGeneratorLowerFirstRawComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      rightLorentzGeneratorLowerFirstColors) : Physlib.RatComplexNum :=
  metricSign (b 0) * rightLorentzGeneratorComponent (b 0) (b 1) (b 2) (b 3)

set_option backward.isDefEq.respectTransparency false in
-- Dependent color normalization through `crossToSlot` exceeds the default recursion depth.
set_option maxRecDepth 2000 in
private lemma rightLorentzGeneratorLowerFirstRaw_eq_ofRat :
    toDualMapAtIndex (S := complexLorentzTensor) 0 rightLorentzGenerator =
      ofRat rightLorentzGeneratorLowerFirstRawComponent := by
  rw [rightLorentzGenerator_eq_ofRat, toDualMapAtIndex]
  change crossToSlot (S := complexLorentzTensor) 0 0 rfl η' (ofRat _) = _
  rw [crossToSlot_eq_crossToEnd, crossToEnd]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [coMetric_eq_ofRat]
  rw [prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat, permT_ofRat, permT_ofRat]
  congr 1
  funext b
  revert b
  decide +kernel

/-- Components of the right generators with both Lorentz indices lowered. -/
private def rightLorentzGeneratorLowerBothRawComponentArgs
    (mu nu : Fin 4) (b c : Fin 2) : Physlib.RatComplexNum :=
  metricSign mu * metricSign nu * rightLorentzGeneratorComponent mu nu b c

/-- Tensor-indexed components of the right generators with both Lorentz indices lowered. -/
private def rightLorentzGeneratorLowerBothRawComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      rightLorentzGeneratorLowerBothColors) : Physlib.RatComplexNum :=
  rightLorentzGeneratorLowerBothRawComponentArgs (b 0) (b 1) (b 2) (b 3)

set_option backward.isDefEq.respectTransparency false in
-- Dependent color normalization through `crossToSlot` exceeds the default recursion depth.
set_option maxRecDepth 2000 in
private lemma rightLorentzGeneratorLowerBothRaw_eq_ofRat :
    toDualMapAtIndex (S := complexLorentzTensor) 1
      (toDualMapAtIndex (S := complexLorentzTensor) 0 rightLorentzGenerator) =
      ofRat rightLorentzGeneratorLowerBothRawComponent := by
  rw [rightLorentzGeneratorLowerFirstRaw_eq_ofRat, toDualMapAtIndex]
  change crossToSlot (S := complexLorentzTensor) 1 0 rfl η' (ofRat _) = _
  rw [crossToSlot_eq_crossToEnd, crossToEnd]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [coMetric_eq_ofRat]
  rw [prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat, permT_ofRat, permT_ofRat]
  congr 1
  funext b
  revert b
  decide +kernel

/-- Index colors before contracting the Levi-Civita tensor with the lowered right generators. -/
private noncomputable abbrev leviCivitaRightLowerBothProductColors : Fin 8 → Color :=
  Fin.append leviCivitaColors rightLorentzGeneratorLowerBothColors

/-- Components before contracting the Levi-Civita tensor with the lowered right generators. -/
private noncomputable def leviCivitaRightLowerBothProductComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leviCivitaRightLowerBothProductColors) : Physlib.RatComplexNum :=
  leviCivitaComponent (ComponentIdx.prod b).1 *
    rightLorentzGeneratorLowerBothRawComponent (ComponentIdx.prod b).2

private lemma leviCivita_prod_rightLowerBoth_eq_ofRat :
    prodT ε4ℂ
      (toDualMapAtIndex (S := complexLorentzTensor) 1
        (toDualMapAtIndex (S := complexLorentzTensor) 0 rightLorentzGenerator)) =
      ofRat leviCivitaRightLowerBothProductComponent := by
  rw [rightLorentzGeneratorLowerBothRaw_eq_ofRat, leviCivita_eq_ofRat,
    prodT_ofRat_ofRat]
  rfl

private lemma leviCivitaRightLowerBothContractKappa_valid :
    (3 : Fin 8) ≠ 5 ∧
      complexLorentzTensor.τ (leviCivitaRightLowerBothProductColors 3) =
        leviCivitaRightLowerBothProductColors 5 := by
  decide

/-- Index colors after the first Levi-Civita contraction for the right generators. -/
private noncomputable abbrev leviCivitaRightLowerBothContractKappaColors : Fin 6 → Color :=
  leviCivitaRightLowerBothProductColors ∘ Fin.succSuccAbove (3 : Fin 8) 5

/-- Components after the first Levi-Civita contraction for the right generators. -/
private noncomputable def leviCivitaRightLowerBothContractKappaComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leviCivitaRightLowerBothContractKappaColors) : Physlib.RatComplexNum :=
  ∑ x : Fin (complexLorentzTensor.repDim
      (leviCivitaRightLowerBothProductColors (3 : Fin 8))),
    leviCivitaRightLowerBothProductComponent
      (ComponentIdx.DropPairSection.ofFinEquiv
        leviCivitaRightLowerBothContractKappa_valid.1 b
        (x, Fin.cast (by
          simp [← leviCivitaRightLowerBothContractKappa_valid.2,
            complexLorentzTensor.repDim_tau]) x))

private lemma leviCivitaRightLowerBoth_contractKappa_eq_ofRat :
    contrT 6 (3 : Fin 8) 5 leviCivitaRightLowerBothContractKappa_valid
      (ofRat leviCivitaRightLowerBothProductComponent) =
      ofRat leviCivitaRightLowerBothContractKappaComponent := by
  rw [contrT_ofRat]
  rfl

private lemma leviCivitaRightLowerBothContractRho_valid :
    (2 : Fin 6) ≠ 3 ∧
      complexLorentzTensor.τ (leviCivitaRightLowerBothContractKappaColors 2) =
        leviCivitaRightLowerBothContractKappaColors 3 := by
  decide

/-- Index colors after both Levi-Civita contractions for the right generators. -/
private noncomputable abbrev leviCivitaRightLowerBothContractRhoColors : Fin 4 → Color :=
  leviCivitaRightLowerBothContractKappaColors ∘ Fin.succSuccAbove (2 : Fin 6) 3

/-- Components after both Levi-Civita contractions for the right generators. -/
private noncomputable def leviCivitaRightLowerBothContractRhoComponent
    (b : ComponentIdx (S := complexLorentzTensor)
      leviCivitaRightLowerBothContractRhoColors) : Physlib.RatComplexNum :=
  ∑ x : Fin (complexLorentzTensor.repDim
      (leviCivitaRightLowerBothContractKappaColors (2 : Fin 6))),
    leviCivitaRightLowerBothContractKappaComponent
      (ComponentIdx.DropPairSection.ofFinEquiv
        leviCivitaRightLowerBothContractRho_valid.1 b
        (x, Fin.cast (by decide) x))

private lemma leviCivitaRightLowerBoth_contractRho_eq_ofRat :
    contrT 4 (2 : Fin 6) 3 leviCivitaRightLowerBothContractRho_valid
      (ofRat leviCivitaRightLowerBothContractKappaComponent) =
      ofRat leviCivitaRightLowerBothContractRhoComponent := by
  rw [contrT_ofRat]
  rfl

/-!

## C. Self-duality

-/

set_option backward.isDefEq.respectTransparency false in
/-- The left Lorentz generators are self-dual. With signature `(+---)` and
`\epsilon^{0123} = 1`, the equivalent Hodge-star eigenvalue is `+i`. -/
lemma leftLorentzGenerator_selfDual : ({leftLorentzGenerator | μ ν α α' =
    (-Complex.I / 2) •ₜ
      (ε4ℂ | μ ν ρ κ ⊗ leftLorentzGenerator | τ(ρ) τ(κ) α α')}ᵀ : Prop) := by
  conv_lhs => rw [leftLorentzGenerator_eq_ofRat]
  conv_rhs =>
    enter [2, 2, 2, 2]
    rw [leviCivita_prod_leftLowerBoth_eq_ofRat]
  conv_rhs =>
    enter [2, 2, 2]
    rw [leviCivitaLeftLowerBoth_contractKappa_eq_ofRat]
  conv_rhs =>
    enter [2, 2]
    rw [leviCivitaLeftLowerBoth_contractRho_eq_ofRat]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofRat_basis_repr_apply, permT_basis_repr_symm_apply]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    ofRat_basis_repr_apply]
  rw [show -Complex.I / 2 =
      Physlib.RatComplexNum.toComplexNum ⟨0, (-1 / 2 : ℚ)⟩ by
    simp [Physlib.RatComplexNum.toComplexNum]
    ring]
  rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
/-- The right Lorentz generators are anti-self-dual. With signature `(+---)` and
`\epsilon^{0123} = 1`, the equivalent Hodge-star eigenvalue is `-i`. -/
lemma rightLorentzGenerator_antiSelfDual : ({rightLorentzGenerator | μ ν β β' =
    (Complex.I / 2) •ₜ
      (ε4ℂ | μ ν ρ κ ⊗ rightLorentzGenerator | τ(ρ) τ(κ) β β')}ᵀ : Prop) := by
  conv_lhs => rw [rightLorentzGenerator_eq_ofRat]
  conv_rhs =>
    enter [2, 2, 2, 2]
    rw [leviCivita_prod_rightLowerBoth_eq_ofRat]
  conv_rhs =>
    enter [2, 2, 2]
    rw [leviCivitaRightLowerBoth_contractKappa_eq_ofRat]
  conv_rhs =>
    enter [2, 2]
    rw [leviCivitaRightLowerBoth_contractRho_eq_ofRat]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofRat_basis_repr_apply, permT_basis_repr_symm_apply]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    ofRat_basis_repr_apply]
  rw [show Complex.I / 2 =
      Physlib.RatComplexNum.toComplexNum ⟨0, (1 / 2 : ℚ)⟩ by
    simp [Physlib.RatComplexNum.toComplexNum]
    ring]
  rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

end PauliMatrix
