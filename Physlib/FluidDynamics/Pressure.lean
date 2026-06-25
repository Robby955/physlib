/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.FluidDynamics.FluidState
public import Physlib.SpaceAndTime.Space.Derivatives.MatrixDiv
/-!

# Pressure fields in fluid dynamics

## i. Overview

This module defines pressure fields for fluids and relates pressure to the isotropic
Cauchy stress contribution `-p I`. The main bridge is that the matrix divergence of
this pressure stress is the pressure force `-∇p`.

## ii. Key results

- `PressureField` : A time-dependent pressure field on space.
- `FluidWithPressure` : A fluid state with a pressure field.
- `pressureStress` : The isotropic Cauchy stress contribution `-p I`.
- `pressureForce` : The pressure force `-∇p`.
- `matrixDiv_pressureStress` : The divergence of `pressureStress` is `pressureForce`.
- `FluidWithPressure.toMomentumBalance` : A pressure fluid as momentum-balance data.

## iii. Table of contents

- A. Pressure fields
- B. Pressure stress
- C. Pressure force
- D. Momentum-balance data

## iv. References

- Landau and Lifshitz, Fluid Mechanics, Chapter 1.

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics

/-!

## A. Pressure fields

-/

/-- A pressure field on `d`-dimensional space, depending on time. -/
abbrev PressureField (d : ℕ) := ScalarField d

/-- A fluid state together with a pressure field. -/
structure FluidWithPressure (d : ℕ) extends FluidState d where
  /-- The pressure field. -/
  pressure : PressureField d

/-!

## B. Pressure stress

-/

/-- The isotropic Cauchy stress contribution from pressure, `-p I`. -/
def pressureStress (d : ℕ) (p : PressureField d) : StressTensor d :=
  fun t x => Matrix.diagonal fun _ => - p t x

@[simp]
lemma pressureStress_apply (d : ℕ) (p : PressureField d)
    (t : Time) (x : Space d) (i j : Fin d) :
    pressureStress d p t x i j = if i = j then - p t x else 0 := by
  simp [pressureStress, Matrix.diagonal_apply]

lemma pressureStress_offDiag (d : ℕ) (p : PressureField d)
    (t : Time) (x : Space d) {i j : Fin d} (hij : i ≠ j) :
    pressureStress d p t x i j = 0 := by
  simp [pressureStress, hij]

lemma pressureStress_symm (d : ℕ) (p : PressureField d)
    (t : Time) (x : Space d) (i j : Fin d) :
    pressureStress d p t x i j = pressureStress d p t x j i := by
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [pressureStress, hij, hji]

/-!

## C. Pressure force

-/

/-- The pressure force associated to a pressure field, `-∇p`. -/
noncomputable def pressureForce (d : ℕ) (p : PressureField d) : VectorField d :=
  fun t x => - ∇ (p t) x

@[simp]
lemma pressureForce_apply (d : ℕ) (p : PressureField d)
    (t : Time) (x : Space d) (i : Fin d) :
    pressureForce d p t x i = - ∂[i] (p t) x := by
  simp [pressureForce, Space.grad_apply]

/-- The matrix divergence of the pressure stress `-p I` is the pressure force `-∇p`. -/
lemma matrixDiv_pressureStress (d : ℕ) (p : PressureField d) (t : Time) :
    matrixDiv d (pressureStress d p t) = pressureForce d p t := by
  ext x i
  rw [matrixDiv_apply, pressureForce_apply]
  rw [Finset.sum_eq_single i]
  · simp [pressureStress, Space.deriv_eq]
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    simp [pressureStress, hij]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-!

## D. Momentum-balance data

-/

namespace FluidWithPressure

/-- The momentum-balance data obtained by using pressure stress and a supplied body force. -/
def toMomentumBalance {d : ℕ} (fluid : FluidWithPressure d) (bodyForce : BodyForce d) :
    FluidInMomentumBalance d where
  toFluidState := fluid.toFluidState
  stress := pressureStress d fluid.pressure
  bodyForce := bodyForce

end FluidWithPressure

end FluidDynamics
