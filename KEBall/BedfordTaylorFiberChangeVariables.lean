import KEBall.BedfordTaylorFiberRealCoordinates
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Change of variables in the normalized fiber integral
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped ContDiff

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)

theorem setIntegral_smul_ball {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [Measure.IsAddHaarMeasure μ] (f : V → ℝ) {R S : ℝ} (hR : 0 < R) :
    (∫ x in ball 0 S, R ^ Module.finrank ℝ V * f (R • x) ∂μ) =
      ∫ x in ball 0 (R * S), f x ∂μ := by
  let g := (ball (0 : V) (R * S)).indicator f
  have hpre (x : V) : R • x ∈ ball (0 : V) (R * S) ↔ x ∈ ball (0 : V) S := by
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      mul_lt_mul_iff_right₀ hR]
  have he : (fun x => g (R • x)) = (ball (0 : V) S).indicator (fun x => f (R • x)) := by
    funext x
    by_cases hx : x ∈ ball (0 : V) S
    · simp only [g, indicator_of_mem hx, indicator_of_mem ((hpre x).mpr hx)]
    · simp only [g, indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hpre x).mp h))]
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg μ g R (hR := hR.le)
  rw [he, integral_indicator measurableSet_ball] at h
  dsimp only [g] at h
  rw [integral_indicator measurableSet_ball, smul_eq_mul] at h
  rw [integral_const_mul, h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul]

/-- A normalized integral in real coordinates, after dilation, has the
usual Bedford–Taylor volume normalization on the larger complex ball. -/
theorem setIntegral_volume0_dilation_coordinates {n : ℕ}
    (f : ComplexModel n → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in unitBall n, R ^ (2 * n) * f (R • complexCoordinates n x) ∂volume0 n) =
      ((n.factorial : ℝ) / Real.pi ^ n) * ∫ z in ball (0 : ComplexModel n) R, f z := by
  rw [setIntegral_volume0]
  congr 1
  have h := setIntegral_smul_ball (volume : Measure (E n)) (f ∘ complexCoordinates n)
    (S := 1) hR
  simp only [finrank_E, mul_one, Function.comp_apply, map_smul] at h
  change (∫ x in ball (0 : E n) 1, R ^ (2 * n) * f (R • complexCoordinates n x)) = _
  rw [h]
  have hpre : (complexCoordinates n) ⁻¹' ball (0 : ComplexModel n) R = ball (0 : E n) R := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  rw [← hpre]
  exact (complexCoordinates_measurePreserving n).setIntegral_preimage_emb
    (complexCoordinates n).toHomeomorph.toMeasurableEquiv.measurableEmbedding f _

end KEBall.BedfordTaylor
