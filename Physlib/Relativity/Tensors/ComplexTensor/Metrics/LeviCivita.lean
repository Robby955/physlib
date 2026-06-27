/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Units.Basic
public import Physlib.Mathematics.KroneckerDelta
/-!

# A. Levi-Civita tensor as a complex Lorentz tensor

This file defines the rank-four Levi-Civita tensor as a complex Lorentz tensor.

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
noncomputable section

namespace complexLorentzTensor
open Fermion
open TensorSpecies
open Tensor
open KroneckerDelta

/-- The Levi-Civita tensor `εⁱʲᵏˡ` as a complex Lorentz tensor, with `ε⁰¹²³ = 1`.

The component on a multi-index `f` is the generalized Kronecker delta of `f` against the
identity, i.e. the sign of `f` when `f` is a permutation and `0` otherwise. -/
noncomputable def leviCivita : ℂT[.up, .up, .up, .up] :=
  ofRat (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    ⟨((generalizedKroneckerDelta
        (fun i => Fin.cast (by fin_cases i <;> rfl) (f i)) (id : Fin 4 → Fin 4) : ℤ) : ℚ), 0⟩

/-- The Levi-Civita tensor `εⁱʲᵏˡ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "ε4" => leviCivita

/-- The `ofRat` form of the Levi-Civita tensor. -/
lemma leviCivita_eq_ofRat : ε4 =
    ofRat (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    ⟨((generalizedKroneckerDelta
        (fun i => Fin.cast (by fin_cases i <;> rfl) (f i)) (id : Fin 4 → Fin 4) : ℤ) : ℚ), 0⟩ :=
  rfl

/-- The Levi-Civita tensor is antisymmetric in its first two indices
`{ε4 | μ ν ρ σ = - ε4 | ν μ ρ σ}ᵀ`. -/
lemma leviCivita_antisymm : {ε4 | μ ν ρ σ = - (ε4 | ν μ ρ σ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [Tensorial.self_toTensor_apply]
  rw [permT_basis_repr_symm_apply]
  rw [leviCivita_eq_ofRat, ofRat_basis_repr_apply, ← map_neg, ofRat_basis_repr_apply]
  congr 1
  simp only [Pi.neg_apply]
  have hcast : ∀ (x y : ℤ), x = -y →
      ({ fst := (↑x : ℚ), snd := 0 } : Physlib.RatComplexNum)
        = -{ fst := (↑y : ℚ), snd := 0 } := by
    intro x y h; subst h
    show (⟨(↑(-y) : ℚ), 0⟩ : Physlib.RatComplexNum) = ⟨-↑y, -0⟩
    rw [Int.cast_neg, neg_zero]
  apply hcast
  rw [← generalizedKroneckerDelta_swap _ _ (Fin.zero_ne_one (n := 2))]
  congr 1
  funext i
  fin_cases i <;> rfl

end complexLorentzTensor
