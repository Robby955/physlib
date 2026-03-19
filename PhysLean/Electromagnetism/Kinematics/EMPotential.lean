/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Electromagnetism.Basic
public import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
public import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a function from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `ElectromagneticPotential` : is the type of electromagnetic potentials.
- `ElectromagneticPotential.deriv` : the derivative tensor `∂_μ A^ν`.
- `DistElectromagneticPotential` : the type of electromagnetic potentials as distributions.

## iii. Table of contents

- A. The electromagnetic potential
  - A.1. The action on the space-time derivatives
  - A.2. Differentiability
  - A.3. Variational adjoint derivative of component
  - A.4. Variational adjoint derivative of derivatives of the potential
- B. The derivative tensor of the electromagnetic potential
  - B.1. Equivariance of the derivative tensor
  - B.2. The elements of the derivative tensor in terms of the basis
- C. The electromagnetic potential as a distribution
  - C.1. The derivative of the electromagnetic potential as a distribution
  - C.2. The derivative in terms of the basis
  - C.3. Equivariance of the derivative distribution

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html
- https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf

-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential

We define the electromagnetic potential as a function from spacetime to
contravariant Lorentz vectors, and prove some simple results about it.

-/
/-- The electromagnetic potential is a tensor `A^μ`. -/
structure ElectromagneticPotential (d : ℕ := 3) where
  val : SpaceTime d → Lorentz.Vector d

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

instance {d} : CoeFun (ElectromagneticPotential d) (λ _ => SpaceTime d → Lorentz.Vector d) :=
  ⟨ElectromagneticPotential.val⟩

/-!

## A.1. Differentiablity and smoothness

The API shall contain properties related to the differentability and smoothness
of the electromagnetic potential.

-/

@[fun_prop]
lemma differentiable_component {d : ℕ} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (μ : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => A x μ) := by
  revert μ
  rw [SpaceTime.differentiable_vector]
  exact hA

@[fun_prop]
lemma contDiff_components {n} {d : ℕ} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (μ : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun x => A x μ) := by
  revert μ
  rw [SpaceTime.contDiff_vector]
  exact hA

@[fun_prop]
lemma differentiable_deriv {d} {μ : Fin 1 ⊕ Fin d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) : Differentiable ℝ (∂_ μ A) := by
  refine Differentiable.clm_apply ?_ ?_
  · exact ((contDiff_succ_iff_fderiv (n := 1)).mp hA).2.2.differentiable (by simp)
  · fun_prop

@[fun_prop]
lemma contDiff_deriv {n} {d} {μ : Fin 1 ⊕ Fin d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (∂_ μ A) := by
  refine ContDiff.clm_apply ?_ ?_
  · fun_prop
  · fun_prop

@[fun_prop]
lemma differentiable_tensorDeriv {d} (A : ElectromagneticPotential d) (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (tensorDeriv A) := by
  refine Differentiable.fun_sum fun i _ =>
    (IsBoundedLinearMap.differentiable ?_).fun_comp (by fun_prop)
  refine IsLinearMap.with_bound ?_ ‖Lorentz.CoVector.basis i‖  (by simp)
  exact {map_add x y := by simp [tmul_add], map_smul c x := by simp [tmul_smul]}

@[fun_prop]
lemma contDiff_tensorDeriv {n} {d} (A : ElectromagneticPotential d) (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (tensorDeriv A) := by
  refine ContDiff.sum fun i _ =>
    (IsBoundedLinearMap.contDiff ?_).fun_comp (by fun_prop)
  refine IsLinearMap.with_bound ?_ ‖Lorentz.CoVector.basis i‖  (by simp)
  exact {map_add x y := by simp [tmul_add], map_smul c x := by simp [tmul_smul]}

/-!

## A.2. Group action

The API shall contain an action of the Lorentz group on the electromagnetic potential.

-/

noncomputable instance {d} : SMul (LorentzGroup d) (ElectromagneticPotential d) where
  smul Λ A := ⟨fun x => Λ • A (Λ⁻¹ • x)⟩

lemma smul_val_eq {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d) :
    (Λ • A).val = fun x => Λ • A (Λ⁻¹ • x) := rfl

lemma smul_val_eq_comp_actionCLM {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d) :
    (Λ • A).val = Lorentz.Vector.actionCLM Λ ∘ A.val ∘ Lorentz.Vector.actionCLM Λ⁻¹ := rfl

@[fun_prop]
lemma smul_differentiable {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ (Λ • A) := by
  rw [smul_val_eq_comp_actionCLM]
  fun_prop

@[fun_prop]
lemma smul_contDiff {n} {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (Λ • A) := by
  rw [smul_val_eq_comp_actionCLM]
  fun_prop

/-- A simplification of the derivative of the electromagnetic potential
  with a group action on it. -/
lemma spaceTime_deriv_action_eq_sum {d} {μ ν : Fin 1 ⊕ Fin d} {x : SpaceTime d} (Λ : LorentzGroup d)
    (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) :
    ∂_ μ (Λ • A) x ν =  ∑ κ, ∑ ρ, (Λ.1 ν κ * Λ⁻¹.1 ρ μ) * ∂_ ρ A (Λ⁻¹ • x) κ  := by
  rw [SpaceTime.deriv_eq, smul_val_eq_comp_actionCLM, fderiv_comp _ (by fun_prop) (by fun_prop),
    fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [Function.comp_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp']
  simp only [Lorentz.Vector.actionCLM, Nat.reduceSucc, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, Lorentz.Vector.smul_eq_sum, Lorentz.Vector.smul_basis]
  simp only [map_sum, map_smul, Lorentz.Vector.apply_sum, Lorentz.Vector.apply_smul, Finset.mul_sum]
  ring_nf
  rfl

lemma tensorDeriv_equivariant {d} {x : SpaceTime d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d) (hf : Differentiable ℝ A) :
    tensorDeriv (Λ • A) x = Λ • tensorDeriv A (Λ⁻¹ • x) := by
  rw [smul_val_eq, SpaceTime.tensorDeriv_equivariant _ _ _ hf]

/-!

### A.3. Variational adjoint derivative of component

We find the variational adjoint derivative of the components of the potential.
This will be used to find e.g. the variational derivative of the kinetic term,
and derive the equations of motion.

-/

open ContDiff
lemma hasVarAdjDerivAt_component {d : ℕ} (μ : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
        HasVarAdjDerivAt (fun (A' : SpaceTime d → Lorentz.Vector d) x => A' x μ)
          (fun (A' : SpaceTime d → ℝ) x => A' x • Lorentz.Vector.basis μ) A := by
  let f : SpaceTime d → Lorentz.Vector d → ℝ := fun x v => v μ
  let f' : SpaceTime d → Lorentz.Vector d → ℝ → Lorentz.Vector d := fun x _ c =>
    c • Lorentz.Vector.basis μ
  change HasVarAdjDerivAt (fun A' x => f x (A' x)) (fun ψ x => f' x (A x) (ψ x)) A
  apply HasVarAdjDerivAt.fmap
  · fun_prop
  · fun_prop
  intro x A
  refine { differentiableAt := ?_, hasAdjoint_fderiv := ?_ }
  · fun_prop
  refine { adjoint_inner_left := ?_ }
  intro u v
  simp [f,f']
  simp [inner_smul_left, Lorentz.Vector.basis_inner]
  ring_nf
  rfl

/-!

### A.4. Variational adjoint derivative of derivatives of the potential

We find the variational adjoint derivative of the derivatives of the components of the potential.
This will again be used to find the variational derivative of the kinetic term,
and derive the equations of motion (Maxwell's equations).

-/

lemma deriv_hasVarAdjDerivAt {d} (μ ν : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
    HasVarAdjDerivAt (fun (A : SpaceTime d → Lorentz.Vector d) x => ∂_ μ A x ν)
      (fun ψ x => - (fderiv ℝ ψ x) (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν) A := by
  have h0' := HasVarAdjDerivAt.fderiv' _ _
        (hF := hasVarAdjDerivAt_component ν A hA) A (Lorentz.Vector.basis μ)
  refine HasVarAdjDerivAt.congr (G := (fun (A : SpaceTime d →
    Lorentz.Vector d) x => ∂_ μ A x ν)) h0' ?_
  intro φ hφ
  funext x
  simp only
  rw [deriv_apply_eq μ ν φ]
  exact hφ.differentiable (by simp)

/-!

### A.3 Tensor derivative simplification


-/

open Lorentz Tensorial


lemma tensorDeriv_eq_sum_tensor_basis {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    tensorDeriv A x = ∑ b, ∂_ (finSumFinEquiv.symm (b 0)) A x (finSumFinEquiv.symm (b 1)) •
      toTensor.symm (Tensor.basis _ b) := by
  simp [SpaceTime.tensorDeriv_eq_sum_tensor_basis hA, CoVector.indexEquiv,
    SpaceTime.deriv_apply_eq _ _ _ hA, Vector.tensor_basis_repr_toTensor_apply]
  rfl

lemma tensorDeriv_eq_sum_sum_basis {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    tensorDeriv A x = ∑ μ, ∑ ν, ∂_ μ A x ν • CoVector.basis μ ⊗ₜ[ℝ] Vector.basis ν := by
  apply Tensorial.toTensor.injective
  apply (Tensor.basis (Fin.append ![Color.down] _)).repr.injective
  ext b
  trans ∂_ (finSumFinEquiv.symm (b 0)) A x (finSumFinEquiv.symm (b 1))
  · rw [SpaceTime.tensorDeriv_toTensor_basis_repr hA, SpaceTime.deriv_apply_eq _ _ _ hA]
    simp only [Nat.reduceSucc, Nat.reduceAdd, Vector.tensor_basis_repr_toTensor_apply, Fin.isValue]
    rfl
  simp only [Fin.isValue, Nat.reduceSucc, Nat.reduceAdd, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs =>
    enter [2, μ, 2, ν]
    rw [Tensorial.basis_toTensor_apply, Tensorial.basis_map_prod]
    simp only [Nat.reduceAdd, Basis.tensorProduct, CoVector.tensor_basis_map_eq_basis_reindex,
      Vector.tensor_basis_map_eq_basis_reindex, LinearEquiv.trans_symm,
      Finsupp.lcongr_symm, Equiv.refl_symm, ComponentIdx.prodEquiv, Basis.repr_reindex,
      Equiv.coe_fn_symm_mk, Basis.map_repr, LinearEquiv.symm_symm, Finsupp.basisSingleOne_repr,
      LinearEquiv.trans_refl, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
      Basis.repr_self, Finsupp.mapDomain_single, finsuppTensorFinsupp_single, Finsupp.lcongr_single,
      Equiv.refl_apply, AlgebraTensorModule.rid_tmul, smul_eq_mul, mul_one, Finsupp.single_apply,
      ComponentIdx.eq_iff, Fin.forall_fin_two, mul_ite, mul_zero]
    change if (CoVector.indexEquiv.symm μ) 0 = b 0 ∧ (Vector.indexEquiv.symm ν) 0 = b 1 then
      ∂_ μ A.val x ν else 0
  simp [Vector.indexEquiv, CoVector.indexEquiv,
      Equiv.apply_eq_iff_eq_symm_apply (f := finSumFinEquiv), ite_and]

lemma tensorDeriv_eq_sum_basis {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    tensorDeriv A x = ∑ (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)),
      ∂_ μν.1 A x μν.2 • CoVector.basis μν.1 ⊗ₜ[ℝ] Vector.basis μν.2 := by
  rw [tensorDeriv_eq_sum_sum_basis, Fintype.sum_prod_type]
  exact hA

end ElectromagneticPotential

/-!

## C. The electromagnetic potential as a distribution

-/

/-- The electromagnetic potential as a distribution and as a tensor `A^μ`. -/
noncomputable abbrev DistElectromagneticPotential (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

### C.1. The derivative of the electromagnetic potential as a distribution

-/

/-- The derivative of a electromagnetic potential, which is a distribution. -/
noncomputable def deriv {d} : DistElectromagneticPotential d →ₗ[ℝ]
    (SpaceTime d) →d[ℝ] Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := distTensorDeriv

lemma deriv_eq_sum_sum {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    deriv A ε =∑ μ, ∑ ν, (SpaceTime.distDeriv μ A ε ν) •
      Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  simp [deriv, distTensorDeriv_apply]
  congr
  funext μ
  conv_lhs => rw [← Lorentz.Vector.basis.sum_repr (SpaceTime.distDeriv μ A ε)]
  rw [tmul_sum]
  congr
  funext ν
  simp
  rfl
/-!

### C.2. The derivative in terms of the basis

-/

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A ε) μν =
    distDeriv μν.1 A ε μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [deriv_eq_sum_sum]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_deriv_basis_repr_apply {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A ε)) b =
    distDeriv (finSumFinEquiv.symm (b 0)) A ε (finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

/-!

### C.3. Equivariance of the derivative distribution

-/

lemma deriv_equivariant {d} {A : DistElectromagneticPotential d}
    (Λ : LorentzGroup d) : deriv (Λ • A) = Λ • deriv A := by
  rw [deriv, distTensorDeriv_equivariant]

end DistElectromagneticPotential

end Electromagnetism
