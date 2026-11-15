import KEBall.SphereMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp

/-!
# Squared radius on the normalized ball

The pushforward of normalized volume under the squared norm has density
`n * s^(n-1)` on the unit interval, here expressed through integration.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace KEBall.MoserTrudinger

theorem integral_volume0_sqNorm {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) :
    (∫ x in unitBall n, f (‖x‖ ^ 2) ∂volume0 n) =
      ∫ s in (0 : ℝ)..1, (n : ℝ) * s ^ (n - 1) * f s := by
  let : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_E]; omega)
  let g : ℝ → ℝ := (Iio (1 : ℝ)).indicator (fun r => f (r ^ 2))
  have hg (x : E n) :
      (unitBall n).indicator (fun x : E n => f (‖x‖ ^ 2)) x = g ‖x‖ := by
    by_cases hx : ‖x‖ < 1 <;> simp [g, unitBall, Metric.mem_ball, dist_zero_right, hx]
  rw [setIntegral_volume0, ← integral_indicator (by exact Metric.isOpen_ball.measurableSet),
    show (unitBall n).indicator (fun x : E n => f (‖x‖ ^ 2)) = (fun x => g ‖x‖) from funext hg,
    integral_fun_norm_addHaar (volume : Measure (E n)), finrank_E, nsmul_eq_mul]
  simp only [smul_eq_mul]
  have hvol : (volume : Measure (E n)).real (Metric.ball 0 1) =
      Real.pi ^ n / (n.factorial : ℝ) := by
    rw [measureReal_def, ← unitBall, volume_unitBall n hn, ENNReal.toReal_ofReal (by positivity)]
  rw [hvol]
  have hrestrict :
      (∫ r in Ioi (0 : ℝ), r ^ (2 * n - 1) * g r) =
        ∫ r in (0 : ℝ)..1, r ^ (2 * n - 1) * f (r ^ 2) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator
            (fun r => r ^ (2 * n - 1) * f (r ^ 2)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        by_cases hr : r < 1 <;> simp [g, hr]
      _ = _ := by
        rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        congr 2
        ext r
        simp [and_comm]
  rw [hrestrict]
  have hscale : (n.factorial : ℝ) / Real.pi ^ n * ((2 * n : ℝ) *
      (Real.pi ^ n / (n.factorial : ℝ))) = (2 * n : ℝ) := by
    field_simp
  push_cast
  simp only [← mul_assoc] at hscale ⊢
  rw [hscale, ← intervalIntegral.integral_const_mul]
  have hsq (r : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    simpa [pow_one] using (hasDerivAt_pow 2 r)
  have hcomp : ContinuousOn (fun s : ℝ => (n : ℝ) * s ^ (n - 1) * f s)
      ((fun r : ℝ => r ^ 2) '' [[(0 : ℝ), 1]]) := by
    refine ((continuous_const.mul (continuous_id.pow _)).continuousOn.mul hf).mono ?_
    rintro s ⟨r, hr, rfl⟩
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hr
    exact ⟨sq_nonneg _, pow_le_one₀ hr'.1 hr'.2⟩
  have hsubst := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1)
    (fun r _ => hsq r) (by fun_prop) hcomp
  simp only [zero_pow (by decide : 2 ≠ 0), one_pow, Function.comp_apply] at hsubst
  rw [← hsubst]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  have he : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, pow_add, pow_mul, pow_one]
  ring

#print axioms integral_volume0_sqNorm

end KEBall.MoserTrudinger
