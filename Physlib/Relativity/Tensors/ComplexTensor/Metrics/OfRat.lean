/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
/-!

# Lowering Lorentz indices of rational-component tensors

This file gives a component interface for lowering the first two contravariant Lorentz indices
of a rank-four complex Lorentz tensor. The two remaining indices may have arbitrary colors.

The main result, `lowerFirstTwoLorentzIndices_ofRat`, computes the lowering operation by
multiplying the corresponding components by the two diagonal metric signs. It lets component
proofs use index lowering without unfolding `crossToSlot` or increasing recursion limits.

-/

@[expose] public section

open Matrix
open TensorProduct

noncomputable section

open TensorSpecies
open TensorSpecies.Tensor

namespace complexLorentzTensor

/-- The diagonal sign of the Lorentz metric with signature `(+---)`. -/
def lorentzMetricSign (mu : Fin 4) : Physlib.RatComplexNum :=
  if mu.val = 0 then 1 else -1

private lemma lorentzMetricSign_mul_comm (mu nu : Fin 4) :
    lorentzMetricSign mu * lorentzMetricSign nu =
      lorentzMetricSign nu * lorentzMetricSign mu := by
  fin_cases mu <;> fin_cases nu <;> simp [lorentzMetricSign]

private abbrev sourceColors (a d : Color) : Fin 4 → Color :=
  ![Color.up, Color.up, a, d]

private abbrev lowerFirstColors (a d : Color) : Fin 4 → Color :=
  Function.update (sourceColors a d) 0
    (complexLorentzTensor.τ (sourceColors a d 0))

private def sourceIndex {a d : Color}
    (b : ComponentIdx (S := complexLorentzTensor) (lowerFirstColors a d)) :
    ComponentIdx (S := complexLorentzTensor) (sourceColors a d) :=
  fun j => Fin.cast (by fin_cases j <;> rfl) (b j)

private def lowerFirstComponent {a d : Color}
    (f : ComponentIdx (S := complexLorentzTensor) (sourceColors a d) →
      Physlib.RatComplexNum)
    (b : ComponentIdx (S := complexLorentzTensor) (lowerFirstColors a d)) :
    Physlib.RatComplexNum :=
  lorentzMetricSign (Fin.cast (by rfl) (b 0)) * f (sourceIndex b)

private lemma toDualMapAtIndex_succ {n : ℕ} {c : Fin (n + 1) → Color}
    (i : Fin (n + 1)) (t : complexLorentzTensor.Tensor c) :
    toDualMapAtIndex (S := complexLorentzTensor) i t =
      crossToSlot i (0 : Fin 2) rfl
        (metricTensor (S := complexLorentzTensor) (complexLorentzTensor.τ (c i))) t := rfl

private lemma normalizeFirstCoMetric {a d : Color}
    (t : complexLorentzTensor.Tensor (sourceColors a d)) :
    crossToSlot (S := complexLorentzTensor) 0 0 rfl
      (metricTensor (S := complexLorentzTensor)
        (complexLorentzTensor.τ (sourceColors a d 0))) t =
      crossToSlot (S := complexLorentzTensor) 0 0 rfl η' t := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma lowerFirst_ofRat {a d : Color}
    (f : ComponentIdx (S := complexLorentzTensor) (sourceColors a d) →
      Physlib.RatComplexNum) :
    toDualMapAtIndex (S := complexLorentzTensor) 0 (ofRat f) =
      ofRat (lowerFirstComponent f) := by
  rw [toDualMapAtIndex_succ, normalizeFirstCoMetric]
  rw [crossToSlot_eq_crossToEnd, crossToEnd]
  rw [LinearMap.compr₂_apply]
  rw [LinearMap.comp_apply]
  rw [coMetric_eq_ofRat]
  rw [prodT_ofRat_ofRat, LinearMap.comp_apply, permT_ofRat, contrT_ofRat,
    permT_ofRat, permT_ofRat]
  apply congrArg (fun g : ComponentIdx (S := complexLorentzTensor)
    (lowerFirstColors a d) → Physlib.RatComplexNum => ofRat g)
  funext b
  let mu : Fin 4 := Fin.cast (by rfl) (b 0)
  calc
    _ = ∑ x : Fin 4, f (Function.update (sourceIndex b) 0 x) *
        (if x = (0 : Fin 4) ∧ mu = 0 then 1 else if x = mu then -1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      · apply congrArg f
        funext j
        fin_cases j <;> rfl
    _ = lowerFirstComponent f b := by
      rw [Finset.sum_eq_single mu]
      · have hUpdate : Function.update (sourceIndex b) 0 mu = sourceIndex b := by
          funext j
          fin_cases j <;> rfl
        rw [hUpdate]
        simp [lowerFirstComponent, lorentzMetricSign, mu]
      · intro x _ hne
        rw [if_neg]
        · simp [hne]
        · intro h
          exact hne (h.1.trans h.2.symm)
      · simp

private abbrev lowerBothColors (a d : Color) : Fin 4 → Color :=
  Function.update (lowerFirstColors a d) 1
    (complexLorentzTensor.τ (lowerFirstColors a d 1))

private def lowerFirstIndex {a d : Color}
    (b : ComponentIdx (S := complexLorentzTensor) (lowerBothColors a d)) :
    ComponentIdx (S := complexLorentzTensor) (lowerFirstColors a d) :=
  fun j => Fin.cast (by fin_cases j <;> rfl) (b j)

private def lowerSecondComponent {a d : Color}
    (f : ComponentIdx (S := complexLorentzTensor) (lowerFirstColors a d) →
      Physlib.RatComplexNum)
    (b : ComponentIdx (S := complexLorentzTensor) (lowerBothColors a d)) :
    Physlib.RatComplexNum :=
  lorentzMetricSign (Fin.cast (by rfl) (b 1)) * f (lowerFirstIndex b)

private lemma normalizeSecondCoMetric {a d : Color}
    (t : complexLorentzTensor.Tensor (lowerFirstColors a d)) :
    crossToSlot (S := complexLorentzTensor) 1 0 rfl
      (metricTensor (S := complexLorentzTensor)
        (complexLorentzTensor.τ (lowerFirstColors a d 1))) t =
      crossToSlot (S := complexLorentzTensor) 1 0 rfl η' t := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma lowerSecond_ofRat {a d : Color}
    (f : ComponentIdx (S := complexLorentzTensor) (lowerFirstColors a d) →
      Physlib.RatComplexNum) :
    toDualMapAtIndex (S := complexLorentzTensor) 1 (ofRat f) =
      ofRat (lowerSecondComponent f) := by
  rw [toDualMapAtIndex_succ, normalizeSecondCoMetric]
  rw [crossToSlot_eq_crossToEnd, crossToEnd]
  rw [LinearMap.compr₂_apply]
  rw [LinearMap.comp_apply]
  rw [coMetric_eq_ofRat]
  rw [prodT_ofRat_ofRat, LinearMap.comp_apply, permT_ofRat, contrT_ofRat,
    permT_ofRat, permT_ofRat]
  apply congrArg (fun g : ComponentIdx (S := complexLorentzTensor)
    (lowerBothColors a d) → Physlib.RatComplexNum => ofRat g)
  funext b
  let mu : Fin 4 := Fin.cast (by rfl) (b 1)
  calc
    _ = ∑ x : Fin 4, f (Function.update (lowerFirstIndex b) 1 x) *
        (if x = (0 : Fin 4) ∧ mu = 0 then 1 else if x = mu then -1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      · apply congrArg f
        funext j
        fin_cases j <;> rfl
    _ = lowerSecondComponent f b := by
      rw [Finset.sum_eq_single mu]
      · have hUpdate : Function.update (lowerFirstIndex b) 1 mu = lowerFirstIndex b := by
          funext j
          fin_cases j <;> rfl
        rw [hUpdate]
        simp [lowerSecondComponent, lorentzMetricSign, mu]
      · intro x _ hne
        rw [if_neg]
        · simp [hne]
        · intro h
          exact hne (h.1.trans h.2.symm)
      · simp

private def sourceIndexBoth {a d : Color}
    (b : ComponentIdx (S := complexLorentzTensor) (lowerBothColors a d)) :
    ComponentIdx (S := complexLorentzTensor) (sourceColors a d) :=
  fun j => Fin.cast (by fin_cases j <;> rfl) (b j)

private def lowerBothComponent {a d : Color}
    (f : ComponentIdx (S := complexLorentzTensor) (sourceColors a d) →
      Physlib.RatComplexNum)
    (b : ComponentIdx (S := complexLorentzTensor) (lowerBothColors a d)) :
    Physlib.RatComplexNum :=
  lorentzMetricSign (Fin.cast (by rfl) (b 0)) *
    lorentzMetricSign (Fin.cast (by rfl) (b 1)) * f (sourceIndexBoth b)

private lemma lowerBoth_ofRat {a d : Color}
    (f : ComponentIdx (S := complexLorentzTensor) (sourceColors a d) →
      Physlib.RatComplexNum) :
    toDualMapAtIndex (S := complexLorentzTensor) 1
      (toDualMapAtIndex (S := complexLorentzTensor) 0 (ofRat f)) =
      ofRat (lowerBothComponent f) := by
  rw [lowerFirst_ofRat, lowerSecond_ofRat]
  apply congrArg (fun g : ComponentIdx (S := complexLorentzTensor)
    (lowerBothColors a d) → Physlib.RatComplexNum => ofRat g)
  funext b
  simp only [lowerSecondComponent, lowerFirstComponent, lowerBothComponent]
  have hIndex : sourceIndex (lowerFirstIndex b) = sourceIndexBoth b := by
    funext j
    fin_cases j <;> rfl
  rw [hIndex]
  have hMetric :
      lorentzMetricSign (Fin.cast (by rfl) (lowerFirstIndex b 0)) =
        lorentzMetricSign (Fin.cast (by rfl) (b 0)) := by rfl
  rw [hMetric]
  rw [← mul_assoc, lorentzMetricSign_mul_comm, mul_assoc]

/-- Lower the first two contravariant Lorentz indices of a rank-four tensor. -/
def lowerFirstTwoLorentzIndices {a d : Color} :
    complexLorentzTensor.Tensor ![Color.up, Color.up, a, d] →ₗ[ℂ]
      complexLorentzTensor.Tensor ![Color.down, Color.down, a, d] :=
  (permT (S := complexLorentzTensor) (id : Fin 4 → Fin 4)
    (IsReindexing.on_id.mpr (fun i => by fin_cases i <;> rfl))).comp
    ((toDualMapAtIndex (S := complexLorentzTensor) 1).comp
      (toDualMapAtIndex (S := complexLorentzTensor) 0))

/-- Components of a rank-four rational tensor with two leading contravariant Lorentz indices. -/
def lorentzPairComponent {a d : Color}
    (f : Fin 4 → Fin 4 → Fin (repDim a) → Fin (repDim d) →
      Physlib.RatComplexNum)
    (b : ComponentIdx (S := complexLorentzTensor) ![Color.up, Color.up, a, d]) :
    Physlib.RatComplexNum :=
  f (b 0) (b 1) (b 2) (b 3)

/-- Components obtained by lowering both leading Lorentz indices of `lorentzPairComponent`. -/
def loweredLorentzPairComponent {a d : Color}
    (f : Fin 4 → Fin 4 → Fin (repDim a) → Fin (repDim d) →
      Physlib.RatComplexNum)
    (b : ComponentIdx (S := complexLorentzTensor) ![Color.down, Color.down, a, d]) :
    Physlib.RatComplexNum :=
  lorentzMetricSign (b 0) * lorentzMetricSign (b 1) *
    f (b 0) (b 1) (b 2) (b 3)

/-- Components of lowering the first two contravariant Lorentz indices of an `ofRat` tensor. -/
lemma lowerFirstTwoLorentzIndices_ofRat {a d : Color}
    (f : Fin 4 → Fin 4 → Fin (repDim a) → Fin (repDim d) →
      Physlib.RatComplexNum) :
    lowerFirstTwoLorentzIndices (ofRat (lorentzPairComponent f)) =
      ofRat (loweredLorentzPairComponent f) := by
  rw [lowerFirstTwoLorentzIndices, LinearMap.comp_apply, LinearMap.comp_apply,
    lowerBoth_ofRat, permT_ofRat]
  apply congrArg (fun g : ComponentIdx (S := complexLorentzTensor)
    ![Color.down, Color.down, a, d] → Physlib.RatComplexNum => ofRat g)
  funext b
  rfl

end complexLorentzTensor
