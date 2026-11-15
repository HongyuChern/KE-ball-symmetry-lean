import KEBall.SphereFlux
import KEBall.BallCutoffLocal

/-!
# Actual nonzero-boundary Euclidean divergence theorem on the unit ball

The proof starts with the upstream compact-support coordinate Green theorem,
passes to the actual polar surface measure, and takes the proved sharp-cutoff
and derivative-kernel limits. The boundary field need not vanish.

The first interface assumes a globally `C¹` field. A local-neighborhood version
requires the separate localization/extension step; no such step is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall

theorem euclideanDivergence_continuous {n : ℕ} {V : E n → E n}
    (hV : ContDiff ℝ 1 V) : Continuous (euclideanDivergence V) := by
  apply continuous_finsetSum
  intro i hi
  have hVi : ContDiff ℝ 1 (fun x : E n => V x i) :=
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).contDiff.comp hV
  exact (hVi.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem ballCutoff_deriv_hasCompactSupport (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fun x : E n => deriv (ballCutoffProfile ε) (‖x‖ ^ 2)) := by
  apply hasCompactSupport_radialCutoff (R := 1 + ε) (by linarith)
  intro s hs
  have hzero : ballCutoffProfile ε s = 0 :=
    ballCutoffProfile_eq_zero hε (by nlinarith)
  have hmin : IsLocalMin (ballCutoffProfile ε) s := by
    apply Eventually.of_forall
    intro y
    rw [hzero]
    exact ballCutoffProfile_nonneg ε y
  exact hmin.deriv_eq_zero

theorem integral_ballCutoff_divergence_eq_kernel {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {V : E n → E n} (hV : ContDiff ℝ 1 V) :
    (∫ x, ballCutoffProfile ε (‖x‖ ^ 2) * euclideanDivergence V x) =
      ∫ r in Icc (0 : ℝ) 2,
        ballBoundaryKernel ε r * (r ^ (2 * n - 1) * radialFlux n V r) := by
  have hχ : ContDiff ℝ 1 (ballCutoffProfile ε) :=
    (ballCutoffProfile_contDiff ε).of_le (by simp)
  have hc := ballCutoff_hasCompactSupport n hε
  have hf : Integrable (fun x : E n =>
      deriv (ballCutoffProfile ε) (‖x‖ ^ 2) * inner ℝ x (V x)) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((ballCutoffProfile_contDiff ε).continuous_deriv (by simp)).comp
        (continuous_norm.pow 2) |>.mul (continuous_id.inner hV.continuous)
    · exact (ballCutoff_deriv_hasCompactSupport n hε).mul_right
  rw [integral_radialCutoff_divergence hχ hc V (fun x _ => hV.contDiffAt),
    integral_polar_iterated n hn hf]
  have hinner (r : ℝ) :
      (∫ θ : Sphere n, deriv (ballCutoffProfile ε) (‖r • θ.1‖ ^ 2) *
        inner ℝ (r • θ.1) (V (r • θ.1)) ∂sphereMeasure n) =
      (deriv (ballCutoffProfile ε) (r ^ 2) * r) * radialFlux n V r := by
    rw [radialFlux, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with θ
    have hnorm : ‖θ.1‖ = 1 := by
      simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using θ.2
    simp only [norm_smul, Real.norm_eq_abs, hnorm, mul_one, sq_abs,
      real_inner_smul_left, mul_assoc]
  simp_rw [hinner]
  rw [← integral_const_mul]
  have hfun : (fun r : ℝ => -2 * (r ^ (2 * n - 1) *
      (deriv (ballCutoffProfile ε) (r ^ 2) * r * radialFlux n V r))) =
      (fun r : ℝ => ballBoundaryKernel ε r * (r ^ (2 * n - 1) * radialFlux n V r)) := by
    funext r
    rw [ballBoundaryKernel_eq]
    ring
  rw [hfun]
  calc
    _ = ∫ r in Ioc (0 : ℝ) 2,
        ballBoundaryKernel ε r * (r ^ (2 * n - 1) * radialFlux n V r) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun r hr => hr.1)
      intro r hr
      have hr2 : 2 < r := by
        exact lt_of_not_ge (fun hle => hr.2 ⟨hr.1, hle⟩)
      rw [ballBoundaryKernel_eq_zero_of_ge hε (by linarith), zero_mul]
    _ = _ := integral_Icc_eq_integral_Ioc.symm

theorem setIntegral_closedUnitBall_eq_unitBall (n : ℕ) (f : E n → ℝ) :
    (∫ x in closedUnitBall n, f x) = ∫ x in unitBall n, f x := by
  have hs : (volume : Measure (E n)) (unitSphere n) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume (0 : E n) one_ne_zero
  have hae : closedUnitBall n =ᵐ[volume] unitBall n := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs] with x hx
    have hne : ‖x‖ ≠ 1 := by
      simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
    apply propext
    change ‖x - 0‖ ≤ 1 ↔ ‖x - 0‖ < 1
    simp only [sub_zero]
    exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
  rw [Measure.restrict_congr_set hae]

/-- The true outward flux formula for the Euclidean unit ball. -/
theorem integral_unitBall_divergence {n : ℕ} (hn : 0 < n)
    {V : E n → E n} (hV : ContDiff ℝ 1 V) :
    (∫ x in unitBall n, euclideanDivergence V x) =
      ∫ θ : Sphere n, inner ℝ θ.1 (V θ.1) ∂sphereMeasure n := by
  have hleft := tendsto_integral_ballCutoff_of_integrableOn n (R := 2) (by norm_num)
    ((euclideanDivergence_continuous hV).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : E n) 2))
  have hright := tendsto_integral_ballBoundaryKernel_radialFlux n hV.continuous
  have heq (k : ℕ) := integral_ballCutoff_divergence_eq_kernel hn
    (ε := 1 / ((k : ℝ) + 1)) (by positivity) (by
      apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]) hV
  have hright' := hright.congr' (Eventually.of_forall (fun k => (heq k).symm))
  have h := tendsto_nhds_unique hleft hright'
  rw [setIntegral_closedUnitBall_eq_unitBall] at h
  exact h

/-- Exact probability-volume/probability-surface conversion: the coefficient
is the real dimension `2*n`. -/
theorem integral_unitBall_divergence_normalized {n : ℕ} (hn : 0 < n)
    {V : E n → E n} (hV : ContDiff ℝ 1 V) :
    (∫ x in unitBall n, euclideanDivergence V x ∂volume0 n) =
      (2 * n : ℝ) * ∫ θ : Sphere n, inner ℝ θ.1 (V θ.1) ∂sphere0 n := by
  rw [setIntegral_volume0, integral_unitBall_divergence hn hV, integral_sphere0 n hn]
  have hcoeff : (n.factorial : ℝ) / Real.pi ^ n =
      (2 * n : ℝ) * ((n.factorial : ℝ) / ((2 * n : ℝ) * Real.pi ^ n)) := by
    field_simp
  rw [hcoeff, mul_assoc]

#print axioms euclideanDivergence_continuous
#print axioms integral_ballCutoff_divergence_eq_kernel
#print axioms setIntegral_closedUnitBall_eq_unitBall
#print axioms integral_unitBall_divergence
#print axioms integral_unitBall_divergence_normalized

end KEBall
