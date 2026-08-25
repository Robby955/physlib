/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.PauliMatrices.ToTensor
/-!

# Chiral Lorentz generators

## i. Overview

This file defines the Lorentz generators in the left- and right-handed Weyl representations,

`\sigma^{\mu\nu} = (i/4)(\sigma^\mu \bar\sigma^\nu - \sigma^\nu \bar\sigma^\mu)`

and

`\bar\sigma^{\mu\nu} =
  (i/4)(\bar\sigma^\mu \sigma^\nu - \bar\sigma^\nu \sigma^\mu)`.

It gives exact rational-complex component formulas and proves antisymmetry in the two Lorentz
indices. The self-duality and anti-self-duality identities are proved in
`Physlib.Relativity.PauliMatrices.LorentzGenerators.Duality`.

## ii. Key results

- `leftLorentzGenerator`, `rightLorentzGenerator` define the Lorentz generators in the two
  chiral Weyl representations.
- `leftLorentzGenerator_eq_ofRat`, `rightLorentzGenerator_eq_ofRat` give their exact
  rational-complex components.
- `leftLorentzGenerator_antisymm`, `rightLorentzGenerator_antisymm` prove antisymmetry in
  the two Lorentz indices.

## iii. Table of contents

- A. Definitions
- B. Exact components
- C. Antisymmetry

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

## A. Definitions

-/

/-- The Lorentz generators `\sigma^{\mu\nu}` in the left-handed Weyl representation. -/
noncomputable def leftLorentzGenerator :
    ℂT[.up, .up, .upL, .downL] :=
  (Complex.I / 4) •
    (permT ![0, 2, 1, 3] (IsReindexing.auto) <|
      {(σ^^^ | μ α β ⊗ σ^__ | ν β α') +
        (- (σ^^^ | ν α β ⊗ σ^__ | μ β α'))}ᵀ)

/-- The Lorentz generators `\bar\sigma^{\mu\nu}` in the right-handed Weyl representation. -/
noncomputable def rightLorentzGenerator :
    ℂT[.up, .up, .downR, .upR] :=
  (Complex.I / 4) •
    (permT ![0, 2, 1, 3] (IsReindexing.auto) <|
      {(σ^__ | μ β α ⊗ σ^^^ | ν α β') +
        (- (σ^__ | ν β α ⊗ σ^^^ | μ α β'))}ᵀ)

/-!

## B. Exact components

-/

/-- Rational-complex components of the left Lorentz generators. -/
def leftLorentzGeneratorComponent
    (mu nu : Fin 4) (a c : Fin 2) : Physlib.RatComplexNum :=
  ⟨0, (1 / 4 : ℚ)⟩ *
    ((∑ x : Fin 2,
      pauliContrComponent mu a x * pauliContrDownComponent nu x c) -
    (∑ x : Fin 2,
      pauliContrComponent nu a x * pauliContrDownComponent mu x c))

set_option backward.isDefEq.respectTransparency false in
/-- The left Lorentz generators in the rational-complex tensor basis. -/
lemma leftLorentzGenerator_eq_ofRat :
    leftLorentzGenerator = ofRat (fun b =>
      leftLorentzGeneratorComponent (b 0) (b 1) (b 2) (b 3)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [leftLorentzGenerator]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [permT_basis_repr_symm_apply, ofRat_basis_repr_apply]
  simp only [map_add,
    Finsupp.coe_add, Pi.add_apply, map_neg, Finsupp.coe_neg, Pi.neg_apply]
  simp only [permT_basis_repr_symm_apply, contrT_basis_repr_apply,
    prodT_basis_repr_apply, toTensor_eq_ofRat, pauliContrDown_ofRat,
    ofRat_basis_repr_apply]
  simp_rw [contr_basis_ratComplexNum]
  rw [show Complex.I / 4 =
      Physlib.RatComplexNum.toComplexNum ⟨0, (1 / 4 : ℚ)⟩ by
    simp [Physlib.RatComplexNum.toComplexNum]
    ring]
  simp only [← Physlib.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum Physlib.RatComplexNum.toComplexNum,
    ← map_sum Physlib.RatComplexNum.toComplexNum, ← map_neg, ← map_add,
    ← Physlib.RatComplexNum.toComplexNum.map_mul]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

/-- Rational-complex components of the right Lorentz generators. -/
def rightLorentzGeneratorComponent
    (mu nu : Fin 4) (b c : Fin 2) : Physlib.RatComplexNum :=
  ⟨0, (1 / 4 : ℚ)⟩ *
    ((∑ x : Fin 2,
      pauliContrDownComponent mu b x * pauliContrComponent nu x c) -
    (∑ x : Fin 2,
      pauliContrDownComponent nu b x * pauliContrComponent mu x c))

set_option backward.isDefEq.respectTransparency false in
/-- The right Lorentz generators in the rational-complex tensor basis. -/
lemma rightLorentzGenerator_eq_ofRat :
    rightLorentzGenerator = ofRat (fun b =>
      rightLorentzGeneratorComponent (b 0) (b 1) (b 2) (b 3)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [rightLorentzGenerator]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [permT_basis_repr_symm_apply, ofRat_basis_repr_apply]
  simp only [map_add,
    Finsupp.coe_add, Pi.add_apply, map_neg, Finsupp.coe_neg, Pi.neg_apply]
  simp only [permT_basis_repr_symm_apply, contrT_basis_repr_apply,
    prodT_basis_repr_apply, pauliContrDown_ofRat, toTensor_eq_ofRat,
    ofRat_basis_repr_apply]
  simp_rw [contr_basis_ratComplexNum]
  rw [show Complex.I / 4 =
      Physlib.RatComplexNum.toComplexNum ⟨0, (1 / 4 : ℚ)⟩ by
    simp [Physlib.RatComplexNum.toComplexNum]
    ring]
  simp only [← Physlib.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum Physlib.RatComplexNum.toComplexNum,
    ← map_sum Physlib.RatComplexNum.toComplexNum, ← map_neg, ← map_add,
    ← Physlib.RatComplexNum.toComplexNum.map_mul]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

/-!

## C. Antisymmetry

-/

/-- The left Lorentz generators are antisymmetric in their Lorentz indices. -/
lemma leftLorentzGenerator_antisymm :
    ({leftLorentzGenerator | μ ν α α' =
      - (leftLorentzGenerator | ν μ α α')}ᵀ : Prop) := by
  rw [leftLorentzGenerator_eq_ofRat]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofRat_basis_repr_apply, permT_basis_repr_symm_apply]
  simp only [Pi.neg_apply, ofRat_basis_repr_apply, ← map_neg]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

/-- The right Lorentz generators are antisymmetric in their Lorentz indices. -/
lemma rightLorentzGenerator_antisymm :
    ({rightLorentzGenerator | μ ν β β' =
      - (rightLorentzGenerator | ν μ β β')}ᵀ : Prop) := by
  rw [rightLorentzGenerator_eq_ofRat]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofRat_basis_repr_apply, permT_basis_repr_symm_apply]
  simp only [Pi.neg_apply, ofRat_basis_repr_apply, ← map_neg]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

end PauliMatrix
