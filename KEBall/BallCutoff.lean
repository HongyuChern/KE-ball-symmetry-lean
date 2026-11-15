import KEBall.RadialGreen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-!
# Actual smooth cutoffs converging to the closed unit ball

The profile is one for squared radius at most one and zero for squared
radius at least `1+ε`. For `ε = 1/(k+1)`, dominated convergence gives the
sharp-ball limit of the volume side of the radial Green identity.
The derivative-weighted boundary side is a distinct remaining theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace KEBall

noncomputable def ballCutoffProfile (ε s : ℝ) : ℝ :=
  Real.smoothTransition ((1 + ε - s) / ε)

theorem ballCutoffProfile_contDiff (ε : ℝ) : ContDiff ℝ ∞ (ballCutoffProfile ε) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const ε)

theorem ballCutoffProfile_nonneg (ε s : ℝ) : 0 ≤ ballCutoffProfile ε s :=
  Real.smoothTransition.nonneg _

theorem ballCutoffProfile_le_one (ε s : ℝ) : ballCutoffProfile ε s ≤ 1 :=
  Real.smoothTransition.le_one _

theorem ballCutoffProfile_eq_one {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 1) :
    ballCutoffProfile ε s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hε).mpr
  linarith

theorem ballCutoffProfile_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : 1 + ε ≤ s) :
    ballCutoffProfile ε s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hε.le

theorem ballCutoff_hasCompactSupport (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fun x : E n => ballCutoffProfile ε (‖x‖ ^ 2)) := by
  apply hasCompactSupport_radialCutoff (R := 1 + ε) (by linarith)
  intro s hs
  apply ballCutoffProfile_eq_zero hε
  nlinarith

theorem ballCutoff_contDiff (n : ℕ) (ε : ℝ) :
    ContDiff ℝ ∞ (fun x : E n => ballCutoffProfile ε (‖x‖ ^ 2)) :=
  (ballCutoffProfile_contDiff ε).comp (contDiff_norm_sq ℝ)

theorem ballCutoff_tendsto_indicator (n : ℕ) (f : E n → ℝ) (x : E n) :
    Tendsto (fun k : ℕ => ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) * f x)
      atTop (𝓝 ((closedUnitBall n).indicator f x)) := by
  by_cases hx : x ∈ closedUnitBall n
  · have hnorm : ‖x‖ ≤ 1 := by
      simpa only [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
    have hs : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hprof (k : ℕ) :
        ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) = 1 :=
      ballCutoffProfile_eq_one (by positivity) hs
    simpa only [hprof, one_mul, Set.indicator_of_mem hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
  · have hnorm : 1 < ‖x‖ := by
      simpa only [closedUnitBall, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hs : 0 < ‖x‖ ^ 2 - 1 := by nlinarith
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ‖x‖ ^ 2 - 1 :=
      (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _ hs
    have heq : (fun k : ℕ =>
        ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) * f x) =ᶠ[atTop]
          fun _ => (0 : ℝ) := by
      filter_upwards [hsmall] with k hk
      rw [ballCutoffProfile_eq_zero (by positivity) (by linarith), zero_mul]
    rw [Set.indicator_of_notMem hx]
    exact tendsto_const_nhds.congr' heq.symm

/-- The volume side of a sharp-ball limit, for every actual `L¹` function.
No conclusion about the derivative-weighted boundary term is assumed. -/
theorem tendsto_integral_ballCutoff (n : ℕ) {f : E n → ℝ}
    (hf : Integrable f volume) :
    Tendsto (fun k : ℕ =>
      ∫ x, ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) * f x)
      atTop (𝓝 (∫ x in closedUnitBall n, f x)) := by
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun x : E n => ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) * f x) volume :=
    (ballCutoff_contDiff n _).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hbound (k : ℕ) : ∀ᵐ x : E n ∂volume,
      ‖ballCutoffProfile (1 / ((k : ℝ) + 1)) (‖x‖ ^ 2) * f x‖ ≤ ‖f x‖ := by
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (ballCutoffProfile_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (ballCutoffProfile_le_one _ _)
  have h := tendsto_integral_of_dominated_convergence (fun x : E n => ‖f x‖)
    hmeas hf.norm hbound (Filter.Eventually.of_forall (ballCutoff_tendsto_indicator n f))
  simpa only [integral_indicator (show MeasurableSet (closedUnitBall n) from
    Metric.isClosed_closedBall.measurableSet)] using h

#print axioms ballCutoffProfile_contDiff
#print axioms ballCutoffProfile_eq_one
#print axioms ballCutoffProfile_eq_zero
#print axioms ballCutoff_hasCompactSupport
#print axioms ballCutoff_tendsto_indicator
#print axioms tendsto_integral_ballCutoff

end KEBall
