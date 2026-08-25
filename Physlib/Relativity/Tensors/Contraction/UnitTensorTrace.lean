/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.UnitTensor
public import Mathlib.LinearAlgebra.Trace
/-!

# Trace of the unit tensor

## i. Overview

The unit tensor is the coevaluation associated with a tensor-species contraction. Closing its two
indices therefore gives the dimension of the representation:

`contrT(unitTensor c) = dim(V c)`.

The proof identifies the unit tensor with the identity endomorphism by the snake identity
`TensorSpecies.contr_unit`, then computes its linear-map trace.

## ii. Key result

- `TensorSpecies.Tensor.contrT_unitTensor_toField` states that the full contraction of
  `unitTensor c` is the cardinality of the chosen basis for `V c`.

-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace TensorSpecies

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-- The contraction pairing, curried into the dual of its first argument. -/
private noncomputable def contrToDual (c : C) : V (S.τ c) →ₗ[k] Module.Dual k (V c) :=
  (TensorProduct.curry (S.contr c).toLinearMap).flip

private lemma dualTensorHom_map_contrToDual_apply (c : C)
    (u : V (S.τ c) ⊗[k] V c) (x : V c) :
    dualTensorHom k (V c) (V c)
      (TensorProduct.map (contrToDual (S := S) c) LinearMap.id u) x =
    (TensorProduct.lid k (V c) <|
      (S.contr c).toLinearMap.rTensor (V c) <|
      (TensorProduct.assoc k (V c) (V (S.τ c)) (V c)).symm <|
      x ⊗ₜ[k] u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp [contrToDual]
  | tmul y z => simp [contrToDual]
  | add u v hu hv =>
      simpa only [map_add, LinearMap.add_apply, tmul_add] using
        congrArg₂ (fun a b => a + b) hu hv

private lemma dualTensorHom_map_unit_eq_id (c : C) :
    dualTensorHom k (V c) (V c)
      (TensorProduct.map (contrToDual (S := S) c) LinearMap.id (S.unit c (1 : k))) =
      LinearMap.id := by
  ext x
  rw [dualTensorHom_map_contrToDual_apply]
  exact S.contr_unit c x

private lemma contractLeft_map_contrToDual (c : C) (u : V (S.τ c) ⊗[k] V c) :
    contractLeft k (V c)
      (TensorProduct.map (contrToDual (S := S) c) LinearMap.id u) =
    (S.contr (S.τ c))
      (TensorProduct.map (LinearMap.id : V (S.τ c) →ₗ[k] V (S.τ c))
        ((LinearEquiv.cast (R := k) (M := V) (S.τ_τ_apply c).symm).toLinearMap :
          V c →ₗ[k] V (S.τ (S.τ c))) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul y x =>
      simpa [contrToDual] using S.contr_tmul_symm c x y
  | add u v hu hv => simp [hu, hv]

private lemma toField_contrT_fromPairT (c : C) (u : V (S.τ c) ⊗[k] V c) :
    (contrT 0 0 1 (by simp) (fromPairT (S := S) u)).toField =
    (S.contr (S.τ c))
      (TensorProduct.map (LinearMap.id : V (S.τ c) →ₗ[k] V (S.τ c))
        ((LinearEquiv.cast (R := k) (M := V) (S.τ_τ_apply c).symm).toLinearMap :
          V c →ₗ[k] V (S.τ (S.τ c))) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul y x =>
      rw [fromPairT_eq_pure, contrT_pure]
      simp [Pure.contrP, Pure.contrPCoeff]
      congr 2
  | add u v hu hv => simp [hu, hv]

/-- The full contraction of the unit tensor is the dimension of its representation space. -/
lemma contrT_unitTensor_toField (c : C) :
    (contrT 0 0 1 (by simp) (unitTensor (S := S) c)).toField =
      (Fintype.card (basisIdx c) : k) := by
  let _ : Module.Free k (V c) := Module.Free.of_basis (b c)
  let _ : Module.Finite k (V c) := Module.Finite.of_basis (b c)
  rw [unitTensor, fromConstPair, toField_contrT_fromPairT]
  rw [← contractLeft_map_contrToDual]
  rw [← LinearMap.trace_eq_contract_apply]
  rw [dualTensorHom_map_unit_eq_id, LinearMap.trace_id]
  rw [Module.finrank_eq_card_basis (b c)]

end Tensor

end TensorSpecies
