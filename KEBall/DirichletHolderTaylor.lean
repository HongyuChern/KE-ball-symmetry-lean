import KEBall.DirichletCompactHolder
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative Taylor remainders on the closed domain

The segment stays in the original convex domain.  The estimates therefore
apply at sphere points to the actual within jets, without an exterior
regularity assumption or a shrinking interior ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff NNReal

namespace KEBall

theorem norm_dirichlet_first_order_remainder_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set V} (hS : Convex ℝ S) {f : V → F} {D : V → V →L[ℝ] F}
    (hD : ∀ z ∈ S, HasFDerivWithinAt f (D z) S z)
    {K α : ℝ≥0} (hH : HolderOnWith K α D S)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x - D x (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ (α : ℝ) * ‖y - x‖ := by
  let r : V → F := fun z => f z - f x - D x (z - x)
  have hSeg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hrD (z : V) (hz : z ∈ segment ℝ x y) :
      HasFDerivWithinAt r (D z - D x) (segment ℝ x y) z := by
    have hLin : HasFDerivAt (fun z => D x (z - x)) (D x) z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        (D x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    exact (((hD z (hSeg hz)).sub_const (f x)).sub hLin.hasFDerivWithinAt).mono hSeg
  have hrBound (z : V) (hz : z ∈ segment ℝ x y) :
      ‖D z - D x‖ ≤ (K : ℝ) * ‖y - x‖ ^ (α : ℝ) := by
    have h := hH.dist_le (hSeg hz) hx
    simp only [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le_of_mem_segment hz) α.coe_nonneg)
      K.coe_nonneg)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hrD hrBound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [r, sub_self, map_zero, sub_zero] using h

theorem norm_dirichlet_second_order_remainder_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} (hS : Convex ℝ S) {f : V → ℝ} {D : V → V →L[ℝ] ℝ}
    {H : V → V →L[ℝ] V →L[ℝ] ℝ}
    (hD : ∀ z ∈ S, HasFDerivWithinAt f (D z) S z)
    (hH : ∀ z ∈ S, HasFDerivWithinAt D (H z) S z)
    {K α : ℝ≥0} (hHolder : HolderOnWith K α H S)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hSym : ∀ a b : V, H x a b = H x b a) :
    ‖f y - f x - D x (y - x) - (1 / 2 : ℝ) * H x (y - x) (y - x)‖ ≤
      (K : ℝ) * ‖y - x‖ ^ (α : ℝ) * ‖y - x‖ ^ 2 := by
  let r : V → ℝ := fun z => f z - f x - D x (z - x) -
    (1 / 2 : ℝ) * H x (z - x) (z - x)
  have hSeg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hQuad (z : V) : HasFDerivAt
      (fun z => (1 / 2 : ℝ) * H x (z - x) (z - x)) (H x (z - x)) z := by
    have hL : HasFDerivAt (fun z => H x (z - x)) (H x) z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        (H x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    have hQ := (hL.clm_apply ((hasFDerivAt_id z).sub_const x)).const_mul (1 / 2 : ℝ)
    have he : (1 / 2 : ℝ) •
        ((H x (z - x)).comp (ContinuousLinearMap.id ℝ V) +
          (H x).flip (z - x)) = H x (z - x) := by
      ext v
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.flip_apply, smul_eq_mul]
      rw [hSym v (z - x)]
      ring
    exact he ▸ hQ
  have hrD (z : V) (hz : z ∈ segment ℝ x y) :
      HasFDerivWithinAt r (D z - D x - H x (z - x)) (segment ℝ x y) z := by
    have hLin : HasFDerivAt (fun z => D x (z - x)) (D x) z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        (D x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    exact ((((hD z (hSeg hz)).sub_const (f x)).sub hLin.hasFDerivWithinAt).sub
      (hQuad z).hasFDerivWithinAt).mono hSeg
  have hrBound (z : V) (hz : z ∈ segment ℝ x y) :
      ‖D z - D x - H x (z - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ (α : ℝ) * ‖y - x‖ := by
    have h := norm_dirichlet_first_order_remainder_le hS hH hHolder hx (hSeg hz)
    have hd : ‖z - x‖ ≤ ‖y - x‖ := norm_sub_le_of_mem_segment hz
    exact h.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hd α.coe_nonneg)
        K.coe_nonneg) hd (norm_nonneg _) (by positivity))
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hrD hrBound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [r, sub_self, map_zero, ContinuousLinearMap.zero_apply, mul_zero,
    sub_zero, pow_two, mul_assoc] using h

end KEBall
