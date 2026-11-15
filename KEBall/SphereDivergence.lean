import KEBall.BallGreen

/-!
# Sphere divergence from the actual polar surface measure

A vector field tangent to every concentric sphere has zero integrated
ambient divergence on the unit sphere. The proof uses the proved Euclidean
compact-support Green theorem with an annular test, actual polar integration,
and the actual radial derivative kernel converging to radius one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace

namespace KEBall

noncomputable def sphericalAverage (n : ℕ) (f : E n → ℝ) (r : ℝ) : ℝ :=
  ∫ θ : Sphere n, f (r • θ.1) ∂sphereMeasure n

theorem sphericalAverage_continuous (n : ℕ) {f : E n → ℝ} (hf : Continuous f) :
    Continuous (sphericalAverage n f) := by
  have hc : Continuous (fun p : ℝ × Sphere n => f (p.1 • p.2.1)) :=
    hf.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  have h := continuous_parametric_integral_of_continuous
    (f := fun r (θ : Sphere n) => f (r • θ.1))
    (μ := sphereMeasure n) hc (s := univ) isCompact_univ
  change Continuous (fun r => ∫ θ : Sphere n, f (r • θ.1) ∂sphereMeasure n)
  simpa only [Measure.restrict_univ] using h

theorem integral_annular_divergence_eq_kernel {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {V : E n → E n} (hV : ContDiff ℝ 1 V) :
    (∫ x, (-2 * deriv (ballCutoffProfile ε) (‖x‖ ^ 2)) * euclideanDivergence V x) =
      ∫ r in Icc (0 : ℝ) 2,
        ballBoundaryKernel ε r *
          (r ^ (2 * n - 2) * sphericalAverage n (euclideanDivergence V) r) := by
  have hc : Continuous (fun x : E n =>
      (-2 * deriv (ballCutoffProfile ε) (‖x‖ ^ 2)) * euclideanDivergence V x) :=
    (continuous_const.mul
      (((ballCutoffProfile_contDiff ε).continuous_deriv (by simp)).comp
        (continuous_norm.pow 2))).mul (euclideanDivergence_continuous hV)
  have hs : HasCompactSupport (fun x : E n =>
      (-2 * deriv (ballCutoffProfile ε) (‖x‖ ^ 2)) * euclideanDivergence V x) :=
    ((ballCutoff_deriv_hasCompactSupport n hε).mul_left).mul_right
  rw [integral_polar_iterated n hn (hc.integrable_of_hasCompactSupport hs)]
  have hi (r : ℝ) :
      (∫ θ : Sphere n, (-2 * deriv (ballCutoffProfile ε) (‖r • θ.1‖ ^ 2)) *
          euclideanDivergence V (r • θ.1) ∂sphereMeasure n) =
        (-2 * deriv (ballCutoffProfile ε) (r ^ 2)) *
          sphericalAverage n (euclideanDivergence V) r := by
    rw [sphericalAverage, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with θ
    have hnorm : ‖θ.1‖ = 1 := by
      simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using θ.2
    simp only [norm_smul, Real.norm_eq_abs, hnorm, mul_one, sq_abs]
  simp_rw [hi]
  have hp : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  have he (r : ℝ) :
      r ^ (2 * n - 1) *
        ((-2 * deriv (ballCutoffProfile ε) (r ^ 2)) *
          sphericalAverage n (euclideanDivergence V) r) =
        ballBoundaryKernel ε r *
          (r ^ (2 * n - 2) * sphericalAverage n (euclideanDivergence V) r) := by
    rw [ballBoundaryKernel_eq, hp, pow_succ]
    ring
  simp_rw [he]
  calc
    _ = ∫ r in Ioc (0 : ℝ) 2,
        ballBoundaryKernel ε r *
          (r ^ (2 * n - 2) * sphericalAverage n (euclideanDivergence V) r) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun r hr => hr.1)
      intro r hr
      have hr2 : 2 < r := lt_of_not_ge (fun hle => hr.2 ⟨hr.1, hle⟩)
      rw [ballBoundaryKernel_eq_zero_of_ge hε (by linarith), zero_mul]
    _ = _ := integral_Icc_eq_integral_Ioc.symm

/-- An actual radially tangent smooth field has zero total sphere divergence. -/
theorem integral_sphere_divergence_eq_zero {n : ℕ} (hn : 0 < n)
    {V : E n → E n} (hV : ContDiff ℝ 1 V)
    (htan : ∀ x, inner ℝ x (V x) = 0) :
    (∫ θ : Sphere n, euclideanDivergence V θ.1 ∂sphereMeasure n) = 0 := by
  have hzero (ε : ℝ) (hε : 0 < ε) :
      (∫ x, (-2 * deriv (ballCutoffProfile ε) (‖x‖ ^ 2)) * euclideanDivergence V x) = 0 := by
    have hχ : ContDiff ℝ 1 (fun s => -2 * deriv (ballCutoffProfile ε) s) :=
      contDiff_const.mul
        (((contDiff_infty_iff_deriv.mp (ballCutoffProfile_contDiff ε)).2).of_le (by simp))
    have hχc : HasCompactSupport (fun x : E n => -2 * deriv (ballCutoffProfile ε) (‖x‖ ^ 2)) :=
      (ballCutoff_deriv_hasCompactSupport n hε).mul_left
    rw [integral_radialCutoff_divergence hχ hχc V (fun x _ => hV.contDiffAt)]
    simp only [htan, mul_zero, integral_zero]
  have hc : Continuous (fun r : ℝ =>
      r ^ (2 * n - 2) * sphericalAverage n (euclideanDivergence V) r) :=
    (continuous_id.pow _).mul
      (sphericalAverage_continuous n (euclideanDivergence_continuous hV))
  have hlim := tendsto_integral_ballBoundaryKernel
    (hc.continuousOn.integrableOn_compact isCompact_Icc) hc.continuousWithinAt
  have heq (k : ℕ) :
      (∫ r in Icc (0 : ℝ) 2,
        ballBoundaryKernel (1 / ((k : ℝ) + 1)) r *
          (r ^ (2 * n - 2) * sphericalAverage n (euclideanDivergence V) r)) = 0 := by
    rw [← integral_annular_divergence_eq_kernel hn (by positivity) (by
      apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]) hV]
    exact hzero _ (by positivity)
  have hlim0 : Tendsto (fun k : ℕ =>
      ∫ r in Icc (0 : ℝ) 2,
        ballBoundaryKernel (1 / ((k : ℝ) + 1)) r *
          (r ^ (2 * n - 2) * sphericalAverage n (euclideanDivergence V) r))
      atTop (𝓝 0) := tendsto_const_nhds.congr (fun k => (heq k).symm)
  have h := tendsto_nhds_unique hlim hlim0
  simpa only [one_pow, one_mul, sphericalAverage, one_smul] using h

theorem integral_sphere0_divergence_eq_zero {n : ℕ} (hn : 0 < n)
    {V : E n → E n} (hV : ContDiff ℝ 1 V)
    (htan : ∀ x, inner ℝ x (V x) = 0) :
    (∫ θ : Sphere n, euclideanDivergence V θ.1 ∂sphere0 n) = 0 := by
  rw [integral_sphere0 n hn, integral_sphere_divergence_eq_zero hn hV htan, mul_zero]

#print axioms integral_annular_divergence_eq_kernel
#print axioms integral_sphere_divergence_eq_zero
#print axioms integral_sphere0_divergence_eq_zero

end KEBall
