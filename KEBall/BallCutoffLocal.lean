import KEBall.BallCutoff

/-!
# Local integrability suffices for the ball cutoff limit

This avoids imposing any integrability at infinity on the vector fields and
potentials used in the manuscript. Only one slightly larger closed ball is
required; the cutoff is eventually supported there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology

namespace KEBall

theorem tendsto_integral_ballCutoff_of_integrableOn (n : ℕ) {R : ℝ} (hR : 1 < R)
    {f : E n → ℝ} (hf : IntegrableOn f (Metric.closedBall (0 : E n) R) volume) :
    Tendsto (fun k : ℕ =>
      ∫ x, ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) * f x)
      atTop (𝓝 (∫ x in closedUnitBall n, f x)) := by
  let F : E n → ℝ := (Metric.closedBall (0 : E n) R).indicator f
  have hF : Integrable F volume :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr hf
  have hsub : closedUnitBall n ⊆ Metric.closedBall (0 : E n) R := by
    intro x hx
    exact Metric.closedBall_subset_closedBall hR.le hx
  have hint : (∫ x in closedUnitBall n, F x) = ∫ x in closedUnitBall n, f x := by
    apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
    intro x hx
    exact Set.indicator_of_mem (hsub hx) f
  have hlim := tendsto_integral_ballCutoff n hF
  rw [hint] at hlim
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < R - 1 :=
    (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _ (by linarith)
  apply hlim.congr'
  filter_upwards [hsmall] with k hk
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : E n) R
  · simp only [F, Set.indicator_of_mem hx]
  · have hnorm : R < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hz : ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) = 0 :=
      ballCutoffProfile_eq_zero (by positivity) (by nlinarith)
    simp only [hz, zero_mul]

#print axioms tendsto_integral_ballCutoff_of_integrableOn

end KEBall
