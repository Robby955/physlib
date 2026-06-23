/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
module

public import Physlib.SpaceAndTime.TimeAndSpace.EuclideanGroup.Action
/-!

# The Euclidean group action on Schwartz maps over `TimeAndSpace`

## i. Overview

In this file we define the pullback action of the Euclidean group on Schwartz maps over
`TimeAndSpace d`. The action is
`g • η = fun tx => η (g⁻¹ • tx)`.

## ii. Key results

- `TimeAndSpace.schwartzAction` : The Euclidean group action on Schwartz maps as a monoid
  homomorphism into continuous linear maps.
- `TimeAndSpace.instMulActionSchwartzMap` : The induced `MulAction` instance on Schwartz maps.
- `TimeAndSpace.smul_schwartzMap_apply` : Pointwise formula for the action.

## iii. Table of contents

- A. Temperate growth of the coordinate action
- B. The pullback action on Schwartz maps

## iv. References

-/

@[expose] public section
noncomputable section

open SchwartzMap

namespace TimeAndSpace

variable {d : ℕ}

/-!

## A. Temperate growth of the coordinate action

-/

/-- The linear part of the Euclidean-group action on `TimeAndSpace d`. -/
private noncomputable def actionLinearMap (g : EuclideanGroup d) :
    TimeAndSpace d →L[ℝ] TimeAndSpace d :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ Time (Space d))
    (Space.basis.repr.symm.toContinuousLinearMap.comp
      ((EuclideanGroup.orthogonalToLinearIsometryEquiv g.linear).toContinuousLinearMap.comp
        (Space.basis.repr.toContinuousLinearMap.comp
          (ContinuousLinearMap.snd ℝ Time (Space d)))))

/-- The translation part of the Euclidean-group action on `TimeAndSpace d`. -/
private noncomputable def actionTranslation (g : EuclideanGroup d) : TimeAndSpace d :=
  (0, Space.basis.repr.symm g.translation)

private lemma smul_eq_actionLinearMap_add (g : EuclideanGroup d) (tx : TimeAndSpace d) :
    g • tx = actionLinearMap g tx + actionTranslation g := by
  refine Prod.ext ?_ ?_
  · simp [actionLinearMap, actionTranslation]
  · ext i
    have hx : tx.2 -ᵥ (0 : Space d) = Space.basis.repr tx.2 := by
      ext j
      simp [Space.vsub_apply, Space.zero_apply, Space.basis_repr_apply]
    rw [TimeAndSpace.snd_smul, EuclideanGroup.smul_apply]
    simp [actionLinearMap, actionTranslation, hx, Space.add_apply, Space.basis_repr_symm_apply]

/-- The Euclidean-group action on `TimeAndSpace d` has temperate growth. -/
lemma smul_hasTemperateGrowth (g : EuclideanGroup d) :
    Function.HasTemperateGrowth (fun tx : TimeAndSpace d => g • tx) := by
  have hfun : (fun tx : TimeAndSpace d => g • tx) =
      fun tx => actionLinearMap g tx + actionTranslation g := by
    funext tx
    exact smul_eq_actionLinearMap_add g tx
  rw [hfun]
  exact Function.HasTemperateGrowth.add (actionLinearMap g).hasTemperateGrowth
    (Function.HasTemperateGrowth.const (actionTranslation g))

/-- The Euclidean-group action on `TimeAndSpace d` is an isometry. -/
lemma isometry_smul (g : EuclideanGroup d) :
    Isometry (fun tx : TimeAndSpace d => g • tx) :=
  Isometry.of_dist_eq (TimeAndSpace.dist_smul g)

/-- The Euclidean-group action on `TimeAndSpace d` is antilipschitz. -/
lemma antilipschitz_smul (g : EuclideanGroup d) :
    AntilipschitzWith 1 (fun tx : TimeAndSpace d => g • tx) :=
  (isometry_smul g).antilipschitz

/-!

## B. The pullback action on Schwartz maps

-/

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Euclidean-group pullback action on Schwartz maps over `TimeAndSpace d`. -/
noncomputable def schwartzAction {d : ℕ} :
    EuclideanGroup d →* 𝓢(TimeAndSpace d, F) →L[ℝ] 𝓢(TimeAndSpace d, F) where
  toFun g := SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ)
    (g := fun tx : TimeAndSpace d => g⁻¹ • tx)
    (TimeAndSpace.smul_hasTemperateGrowth g⁻¹)
    (TimeAndSpace.antilipschitz_smul g⁻¹)
  map_one' := by
    ext η tx
    simp
  map_mul' g h := by
    ext η tx
    simp only [_root_.mul_inv_rev, SchwartzMap.compCLMOfAntilipschitz_apply,
      Function.comp_apply]
    rw [mul_smul]
    rfl

/-- Pointwise formula for the monoid-homomorphism form of the Schwartz-map pullback action. -/
@[simp]
lemma schwartzAction_apply {d : ℕ} (g : EuclideanGroup d) (η : 𝓢(TimeAndSpace d, F))
    (tx : TimeAndSpace d) :
    (schwartzAction g η) tx = η (g⁻¹ • tx) := rfl

/-- The Euclidean group acts on Schwartz maps over `TimeAndSpace d` by pullback. -/
noncomputable instance instMulActionSchwartzMap {d : ℕ} :
    MulAction (EuclideanGroup d) 𝓢(TimeAndSpace d, F) where
  smul g η := schwartzAction g η
  one_smul η := by
    ext tx
    change (schwartzAction (1 : EuclideanGroup d) η) tx = η tx
    rw [schwartzAction_apply]
    simp
  mul_smul g h η := by
    ext tx
    change (schwartzAction (g * h) η) tx = (schwartzAction g (schwartzAction h η)) tx
    simp only [schwartzAction_apply, _root_.mul_inv_rev]
    rw [mul_smul]

/-- Pointwise formula for the `MulAction` instance on Schwartz maps. -/
@[simp]
lemma smul_schwartzMap_apply {d : ℕ} (g : EuclideanGroup d) (η : 𝓢(TimeAndSpace d, F))
    (tx : TimeAndSpace d) :
    (g • η) tx = η (g⁻¹ • tx) := rfl

/-- Applying `g` and then `h` to a Schwartz map is the pullback action of `h * g`. -/
lemma schwartzAction_mul_apply {d : ℕ} (g h : EuclideanGroup d)
    (η : 𝓢(TimeAndSpace d, F)) :
    schwartzAction h (schwartzAction g η) = schwartzAction (h * g) η := by
  ext tx
  simp only [schwartzAction_apply, _root_.mul_inv_rev]
  rw [mul_smul]

/-- Each Euclidean-group pullback action on Schwartz maps is injective. -/
lemma schwartzAction_injective {d : ℕ} (g : EuclideanGroup d) :
    Function.Injective (schwartzAction (F := F) g) := by
  intro η1 η2 hη
  ext tx
  have htx := congrArg (fun η : 𝓢(TimeAndSpace d, F) => η (g • tx)) hη
  simpa using htx

/-- Each Euclidean-group pullback action on Schwartz maps is surjective. -/
lemma schwartzAction_surjective {d : ℕ} (g : EuclideanGroup d) :
    Function.Surjective (schwartzAction (F := F) g) := by
  intro η
  use schwartzAction g⁻¹ η
  ext tx
  simp

end TimeAndSpace

end
