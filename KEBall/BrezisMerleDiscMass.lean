import KEBall.BrezisMerleDisc
import KEBall.BedfordTaylorSmoothMeasure

/-!
# Disc mass in the normalization of Corollary 1.3
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Laplacian

namespace KEBall.BrezisMerle

theorem laplacian_eq_realHessian_disc (u : E 1 → ℝ) (x : E 1) :
    Δ u x = realHessian u x (realDirection 0) (realDirection 0) +
      realHessian u x (imagDirection 0) (imagDirection 0) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply, realHessian]
  rfl

theorem complexHessian_det_re_eq_laplacian_div_four {u : E 1 → ℝ} {x : E 1}
    (hu : ContDiffAt ℝ ∞ u x) :
    (complexHessian u x).det.re = Δ u x / 4 := by
  rw [Matrix.det_fin_one, complexHessian_real_entry hu, laplacian_eq_realHessian_disc]
  rw [realHessian_symm hu (realDirection 0) (imagDirection 0), sub_self]
  simp [Complex.mul_re, Complex.inv_re]
  ring

/-- Smooth one-dimensional Monge–Ampère mass is the ordinary Laplacian
mass divided by `4π`. -/
theorem d0TopMeasure_disc_eq {u : E 1 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ u x) :
    d0TopMeasure u (unitBall 1) = ENNReal.ofReal (discMass u) := by
  have hB : MeasurableSet (unitBall 1) := measurableSet_ball
  have hΔi : IntegrableOn (Δ u) (unitBall 1) :=
    (((continuous_laplacian (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : E 1) 1))).mono_set ball_subset_closedBall
  have hΔ₀ : 0 ≤ᵐ[(volume : Measure (E 1)).restrict (unitBall 1)] Δ u :=
    (ae_restrict_mem hB).mono hΔ
  rw [d0TopMeasure_eq_density, volume0, withDensity_smul_measure, Measure.smul_apply,
    smul_eq_mul, withDensity_apply _ hB]
  simp only [Nat.factorial_one, Nat.cast_one, pow_one]
  simp_rw [complexHessian_det_re_eq_laplacian_div_four hu.contDiffAt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hΔi.div_const 4)
      (hΔ₀.mono fun _ hx => div_nonneg hx (by norm_num)),
    integral_div, ← ENNReal.ofReal_mul (by positivity), discMass]
  congr 1
  have hp := Real.pi_pos
  field_simp

theorem laplacian_disc_quadratic (x : E 1) :
    Δ (fun y : E 1 => ‖y‖ ^ 2 - (1 : ℝ)) x = (4 : ℝ) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  let T : E 1 →L[ℝ] E 1 →L[ℝ] ℝ := (2 : ℝ) • innerSL ℝ
  have h' : fderiv ℝ (fun y : E 1 => ‖y‖ ^ 2 - (1 : ℝ)) = ⇑T := by
    funext y
    rw [((hasStrictFDerivAt_norm_sq y).hasFDerivAt.sub_const 1).fderiv]
    ext v
    simp only [T, smul_apply, smul_eq_mul, two_nsmul, two_mul]
    rfl
  have hT (i : Fin 2) : T ((EuclideanSpace.basisFun (Fin 2) ℝ) i)
      ((EuclideanSpace.basisFun (Fin 2) ℝ) i) = 2 := by
    let e := (EuclideanSpace.basisFun (Fin 2) ℝ) i
    have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.norm_eq_one i
    change 2 * inner ℝ e e = 2
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, h',
    ContinuousLinearMap.fderiv, hT]
  norm_num

/-- Mass at most `t < 1` gives a uniform exponential bound. The added
quadratic accounts for the difference between the actual mass and `t`. -/
theorem lintegral_exp_addBoundary_le_of_discMass_le {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    {δ : ℝ} (hBoundary : ∀ x ∈ unitSphere 1, -δ ≤ u x)
    (hΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ u x)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) (hMass : discMass u ≤ t) :
    (∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-(u z + δ))) ∂volume) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  let b := t - discMass u
  let q : E 1 → ℝ := fun x => ‖x‖ ^ 2 - 1
  let w : E 1 → ℝ := fun x => u x + b • q x
  have hb : 0 ≤ b := sub_nonneg.mpr hMass
  have hq : ContDiff ℝ 2 q := (contDiff_norm_sq ℝ).sub contDiff_const
  have hw : ContDiff ℝ 2 w := hu.add (hq.const_smul _)
  have hwle (x : E 1) (hx : x ∈ closedUnitBall 1) : w x ≤ u x := by
    have hx₁ : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    change u x + b * (‖x‖ ^ 2 - 1) ≤ u x
    linarith [mul_nonpos_of_nonneg_of_nonpos hb
      (show ‖x‖ ^ 2 - 1 ≤ 0 by nlinarith [norm_nonneg x])]
  have hwBoundary (x : E 1) (hx : x ∈ unitSphere 1) : -δ ≤ w x := by
    have hx₁ : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    simpa [w, q, hx₁] using hBoundary x hx
  have hwΔ (x : E 1) : Δ w x = Δ u x + 4 * b := by
    change Δ (u + b • q) x = _
    have hq' : ContDiff ℝ 2 (b • q) := hq.const_smul b
    rw [hu.contDiffAt.laplacian_add hq'.contDiffAt,
      InnerProductSpace.laplacian_smul _ hq.contDiffAt, smul_eq_mul,
      show Δ q x = 4 from laplacian_disc_quadratic x]
    ring
  have hBall : (volume : Measure (E 1)).real (unitBall 1) = Real.pi := by
    rw [measureReal_def, volume_unitBall 1 (by decide)]
    simp [ENNReal.toReal_ofReal, Real.pi_pos.le]
  have hwMass : discMass w = t := by
    unfold discMass
    simp_rw [hwΔ]
    have huΔ : IntegrableOn (Δ u) (unitBall 1) :=
      ((continuous_laplacian hu).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall
    rw [integral_add huΔ (integrableOn_const (C := 4 * b) measure_ball_lt_top.ne),
      setIntegral_const, hBall, smul_eq_mul]
    dsimp only [b, discMass]
    have hp := Real.pi_pos
    field_simp
    ring
  have h := lintegral_exp_addBoundary_le_of_discMass hw hwBoundary
    (fun x hx => by rw [hwΔ]; linarith [hΔ x hx]) (hwMass.symm ▸ ht₀) (hwMass.symm ▸ ht₁)
  rw [hwMass] at h
  refine le_trans (lintegral_mono_ae ?_) h
  filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet (unitBall 1) from measurableSet_ball)]
    with x hx
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (neg_le_neg (add_le_add (hwle x (ball_subset_closedBall hx)) le_rfl)))

set_option linter.unusedVariables false in
/-- The mass estimate on the unit disk with zero boundary values. -/
theorem lintegral_exp_le_of_discMass_le {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hneg : ∀ x ∈ closedUnitBall 1, u x ≤ 0) (hzero : ∀ x ∈ unitSphere 1, u x = 0)
    (hΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ u x)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) (hMass : discMass u ≤ t) :
    (∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-u z)) ∂volume) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  simpa only [add_zero] using lintegral_exp_addBoundary_le_of_discMass_le hu (δ := 0)
    (fun x hx => by rw [hzero x hx, neg_zero]) hΔ ht₀ ht₁ hMass

end KEBall.BrezisMerle
