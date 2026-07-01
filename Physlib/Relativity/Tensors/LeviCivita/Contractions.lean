/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.LeviCivita.Basic
public import Physlib.Mathematics.KroneckerDeltaContraction
/-!

# Contraction identities for the Levi-Civita tensor

This file proves the "epsilon-epsilon" contraction identities for the rank-four Levi-Civita
tensor `leviCivita` (notation `ε4`) in `d = 3`, stated in terms of the standard-basis
components of `ε4` itself (`realLorentzTensor.leviCivita_basis_repr_apply`).

The purely combinatorial backbone — facts about the `generalizedKroneckerDelta` alone, with no
tensor content — lives in `Physlib.Mathematics.KroneckerDeltaContraction`, next to the
definition of `generalizedKroneckerDelta`.  Here we specialise those facts to the components of
`ε4`:

* `leviCivita_symbol_contract_zero` : `∑_b (ε4)_b · (ε4)_b = 24` (full contraction);
* `leviCivita_symbol_contract_one`  : `∑_h (ε4)_{a,h} · (ε4)_{b,h} = 6 · δ[a,b]`;
* `leviCivita_symbol_contract_two`  :
  `∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])`.

Here `(ε4)_b = (Tensor.basis _).repr ε4 b` is the standard-basis component of `ε4`, an integer
Levi-Civita symbol carried to the reals, and the sums run over the remaining (uncontracted)
component slots.

These are the all-upper-index ("symbol level") forms: each factor carries upper indices, and the
contracted slots are paired by the naive Kronecker pairing of a basis index against itself, so the
constants are the *positive* `24, 6, 2`.  The metric-covariant contraction `ε^{μνρσ} ε_{μνρσ}`
lowers one factor with the Lorentz metric `η` (whose determinant is `-1` in four dimensions),
which multiplies each identity by `det η = -1` and recovers the textbook `ε^{μνρσ} ε_{μνρσ} = -24`,
`ε^{μνρσ} ε_{μνρτ} = -6 δ^σ_τ` and `ε^{μνρσ} ε_{μντω} = -2 (δ^ρ_τ δ^σ_ω - δ^ρ_ω δ^σ_τ)`.  Writing
that covariant form in the `{ε4 | μ ν ρ σ ⊗ … }ᵀ` index notation of `LeviCivita.Basic` requires the
fully index-lowered Levi-Civita tensor `ε_{μνρσ}`, which is not developed here; these component
identities are the reusable ingredient from which such a covariant statement would be assembled.

-/

@[expose] public section

open Matrix TensorSpecies Tensor KroneckerDelta

namespace realLorentzTensor

/-!

## Combinatorial bridge lemmas

The integer Levi-Civita symbol is `generalizedKroneckerDelta f id` for `f : Fin 4 → Fin 4`, and
`realLorentzTensor.leviCivita_basis_repr_apply` identifies it with the standard-basis component of
`ε4` after transporting the component index along `finSumFinEquiv`.  The following private lemmas
package the symbol-level value of each contraction (from `KroneckerDeltaContraction`) and the
bookkeeping needed to switch between component indices `Fin 1 ⊕ Fin 3` and the `Fin 4` labels.

-/

/-- Transporting a `Fin.cons` along `finSumFinEquiv` component-wise. -/
private lemma cons_finSum {n : ℕ} (a : Fin 1 ⊕ Fin 3) (h : Fin n → (Fin 1 ⊕ Fin 3)) :
    (fun i => finSumFinEquiv ((Fin.cons a h : Fin (n + 1) → _) i))
      = Fin.cons (finSumFinEquiv a) (fun j => finSumFinEquiv (h j)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

/-- The Kronecker delta is invariant under the component-index equivalence `finSumFinEquiv`. -/
private lemma kron_finSum (a b : Fin 1 ⊕ Fin 3) :
    kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) = kroneckerDelta a b := by
  simp only [kroneckerDelta, Equiv.apply_eq_iff_eq]

/-- Symbol-level full contraction over `Fin 4 → Fin 4`. -/
private lemma symbol_zero :
    ∑ g : Fin 4 → Fin 4,
      generalizedKroneckerDelta g id * generalizedKroneckerDelta g id = (24 : ℤ) := by
  rw [Finset.sum_congr rfl fun g _ => generalizedKroneckerDelta_mul g g,
    sum_generalizedKroneckerDelta_self 4]
  norm_num [Finset.prod_range_succ]

/-- Symbol-level triple contraction, one free pair `σ, τ`. -/
private lemma symbol_one (σ τ : Fin 4) :
    ∑ h : Fin 3 → Fin 4,
        generalizedKroneckerDelta (Fin.cons σ h) id
          * generalizedKroneckerDelta (Fin.cons τ h) id
      = 6 * ((kroneckerDelta σ τ : ℕ) : ℤ) := by
  rw [Finset.sum_congr rfl fun h _ =>
      generalizedKroneckerDelta_mul (Fin.cons σ h) (Fin.cons τ h),
    sum_generalizedKroneckerDelta_cons σ τ 3]
  norm_num [Finset.prod_range_succ]

/-- Symbol-level double contraction, two free pairs. -/
private lemma symbol_two (ρ σ τ ω : Fin 4) :
    ∑ h : Fin 2 → Fin 4,
        generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ h)) id
          * generalizedKroneckerDelta (Fin.cons τ (Fin.cons ω h)) id
      = 2 * (((kroneckerDelta ρ τ : ℕ) : ℤ) * ((kroneckerDelta σ ω : ℕ) : ℤ)
          - ((kroneckerDelta ρ ω : ℕ) : ℤ) * ((kroneckerDelta σ τ : ℕ) : ℤ)) := by
  have hdet : generalizedKroneckerDelta ![ρ, σ] ![τ, ω]
      = ((kroneckerDelta ρ τ : ℕ) : ℤ) * ((kroneckerDelta σ ω : ℕ) : ℤ)
        - ((kroneckerDelta ρ ω : ℕ) : ℤ) * ((kroneckerDelta σ τ : ℕ) : ℤ) := by
    rw [show generalizedKroneckerDelta ![ρ, σ] ![τ, ω]
          = (Matrix.of fun i j => ((kroneckerDelta (![ρ, σ] i) (![τ, ω] j) : ℕ) : ℤ)).det from rfl,
      Matrix.det_fin_two]
    simp
  rw [Finset.sum_congr rfl fun h _ =>
      generalizedKroneckerDelta_mul (Fin.cons ρ (Fin.cons σ h)) (Fin.cons τ (Fin.cons ω h)),
    sum_generalizedKroneckerDelta_cons₂ ρ σ τ ω 2, hdet]
  norm_num [Finset.prod_range_succ]

/-!

## Epsilon-epsilon contraction identities

-/

/-- **Full Levi-Civita contraction** `ε^{μνρσ} ε^{μνρσ} = 24` at the symbol level.  Summing the
square of every standard-basis component of `ε4` over all four index slots counts the `4! = 24`
permutations. -/
lemma leviCivita_symbol_contract_zero :
    ∑ b : ComponentIdx (S := realLorentzTensor 3)
        ![Color.up, Color.up, Color.up, Color.up],
      (Tensor.basis _).repr ε4 b * (Tensor.basis _).repr ε4 b = 24 := by
  simp_rw [leviCivita_basis_repr_apply]
  rw [show (∑ b : ComponentIdx (S := realLorentzTensor 3)
        ![Color.up, Color.up, Color.up, Color.up],
        (generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4) : ℝ)
          * (generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4) : ℝ))
      = ∑ g : Fin 4 → Fin 4,
        (generalizedKroneckerDelta g id : ℝ) * (generalizedKroneckerDelta g id : ℝ) from
    Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 4 => finSumFinEquiv)) _ _ (fun x => rfl)]
  have hcast : ∀ g : Fin 4 → Fin 4,
      ((generalizedKroneckerDelta g id : ℝ)) * (generalizedKroneckerDelta g id : ℝ)
        = ((generalizedKroneckerDelta g id * generalizedKroneckerDelta g id : ℤ) : ℝ) :=
    fun g => by push_cast; ring
  rw [Finset.sum_congr rfl fun g _ => hcast g, ← Int.cast_sum, symbol_zero]
  norm_num

/-- **Triple Levi-Civita contraction** `ε^{μνρσ} ε^{μνρτ} = 6 δ^σ_τ` at the symbol level:
contracting three of the four component slots of `ε4` leaves one free pair `a, b` and the factor
`3! = 6`. -/
lemma leviCivita_symbol_contract_one (a b : Fin 1 ⊕ Fin 3) :
    ∑ h : Fin 3 → (Fin 1 ⊕ Fin 3),
        (Tensor.basis _).repr ε4 (Fin.cons a h) * (Tensor.basis _).repr ε4 (Fin.cons b h)
      = 6 * ((kroneckerDelta a b : ℕ) : ℝ) := by
  simp_rw [leviCivita_basis_repr_apply, cons_finSum]
  rw [show (∑ h : Fin 3 → (Fin 1 ⊕ Fin 3),
        (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv a) (fun j => finSumFinEquiv (h j)))
            (id : Fin 4 → Fin 4) : ℝ)
          * (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv b) (fun j => finSumFinEquiv (h j)))
            (id : Fin 4 → Fin 4) : ℝ))
      = ∑ h' : Fin 3 → Fin 4,
        (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv a) h') id : ℝ)
          * (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv b) h') id : ℝ) from
    Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 3 => finSumFinEquiv)) _ _ (fun h => rfl)]
  have hcast : ∀ h' : Fin 3 → Fin 4,
      (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv a) h') id : ℝ)
        * (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv b) h') id : ℝ)
        = ((generalizedKroneckerDelta (Fin.cons (finSumFinEquiv a) h') id
            * generalizedKroneckerDelta (Fin.cons (finSumFinEquiv b) h') id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum, symbol_one, kron_finSum]
  push_cast; ring

/-- **Double Levi-Civita contraction** `ε^{μνρσ} ε^{μντω} = 2 (δ^ρ_τ δ^σ_ω - δ^ρ_ω δ^σ_τ)` at the
symbol level: contracting two of the four component slots of `ε4` leaves two free pairs and the
factor `2! = 2`. -/
lemma leviCivita_symbol_contract_two (r s t w : Fin 1 ⊕ Fin 3) :
    ∑ h : Fin 2 → (Fin 1 ⊕ Fin 3),
        (Tensor.basis _).repr ε4 (Fin.cons r (Fin.cons s h))
          * (Tensor.basis _).repr ε4 (Fin.cons t (Fin.cons w h))
      = 2 * (((kroneckerDelta r t : ℕ) : ℝ) * ((kroneckerDelta s w : ℕ) : ℝ)
          - ((kroneckerDelta r w : ℕ) : ℝ) * ((kroneckerDelta s t : ℕ) : ℝ)) := by
  simp_rw [leviCivita_basis_repr_apply, cons_finSum]
  rw [show (∑ h : Fin 2 → (Fin 1 ⊕ Fin 3),
        (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv r)
              (Fin.cons (finSumFinEquiv s) (fun j => finSumFinEquiv (h j))))
            (id : Fin 4 → Fin 4) : ℝ)
          * (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv t)
              (Fin.cons (finSumFinEquiv w) (fun j => finSumFinEquiv (h j))))
            (id : Fin 4 → Fin 4) : ℝ))
      = ∑ h' : Fin 2 → Fin 4,
        (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv r) (Fin.cons (finSumFinEquiv s) h')) id : ℝ)
          * (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv t) (Fin.cons (finSumFinEquiv w) h')) id : ℝ) from
    Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 2 => finSumFinEquiv)) _ _ (fun h => rfl)]
  have hcast : ∀ h' : Fin 2 → Fin 4,
      (generalizedKroneckerDelta
          (Fin.cons (finSumFinEquiv r) (Fin.cons (finSumFinEquiv s) h')) id : ℝ)
        * (generalizedKroneckerDelta
          (Fin.cons (finSumFinEquiv t) (Fin.cons (finSumFinEquiv w) h')) id : ℝ)
        = ((generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv r) (Fin.cons (finSumFinEquiv s) h')) id
            * generalizedKroneckerDelta
              (Fin.cons (finSumFinEquiv t) (Fin.cons (finSumFinEquiv w) h')) id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum, symbol_two,
    kron_finSum, kron_finSum, kron_finSum, kron_finSum]
  push_cast; ring

end realLorentzTensor
