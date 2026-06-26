/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Units.Basic
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

/-- The Levi-Civita tensor `εⁱʲᵏˡ` as a complex Lorentz tensor, with `ε⁰¹²³ = 1`. -/
noncomputable def leviCivita : ℂT[.up, .up, .up, .up] :=
  ofRat (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    if f 0 = (0 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨1, 0⟩ else
    ⟨0, 0⟩

/-- The Levi-Civita tensor `εⁱʲᵏˡ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "ε4" => leviCivita

/-- The `ofRat` form of the Levi-Civita tensor. -/
lemma leviCivita_eq_ofRat : ε4 =
    ofRat (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    if f 0 = (0 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (0 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (1 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (3 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (3 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (2 : Fin 4) ∧ f 1 = (3 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (0 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (2 : Fin 4) then ⟨1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (1 : Fin 4) ∧
        f 2 = (2 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (0 : Fin 4) ∧ f 3 = (1 : Fin 4) then ⟨-1, 0⟩ else
    if f 0 = (3 : Fin 4) ∧ f 1 = (2 : Fin 4) ∧
        f 2 = (1 : Fin 4) ∧ f 3 = (0 : Fin 4) then ⟨1, 0⟩ else
    ⟨0, 0⟩ := rfl

set_option maxRecDepth 100000 in
/-- The Levi-Civita tensor is antisymmetric in its first two indices
`{ε4 | μ ν ρ σ = - ε4 | ν μ ρ σ}ᵀ`. -/
lemma leviCivita_antisymm : {ε4 | μ ν ρ σ = - (ε4 | ν μ ρ σ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [Tensorial.self_toTensor_apply]
  rw [permT_basis_repr_symm_apply]
  rw [leviCivita_eq_ofRat, ofRat_basis_repr_apply, ← map_neg, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide

end complexLorentzTensor
