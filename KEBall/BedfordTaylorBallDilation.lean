import KEBall.BedfordTaylorFiberChangeVariables
import KEBall.CegrellFiberCurvature

/-!
# Dilation of a smooth potential and its total Monge–Ampère mass
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh smoothDensity smoothMeasure)

theorem lintegral_smul_ball {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [Measure.IsAddHaarMeasure μ] (f : V → ℝ≥0∞) {r R : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ Module.finrank ℝ V) * (∫⁻ x in ball 0 R, f (r • x) ∂μ) =
      ∫⁻ x in ball 0 (r * R), f x ∂μ := by
  let s := ball (0 : V) (r * R)
  let g := s.indicator f
  let e := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr.ne').unit : V ≃ₜ V).toMeasurableEquiv
  have hp (x : V) : r • x ∈ s ↔ x ∈ ball (0 : V) R := by
    simp only [s, mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le, mul_lt_mul_iff_right₀ hr]
  have he : (fun x => g (r • x)) = (ball (0 : V) R).indicator (fun x => f (r • x)) := by
    funext x
    by_cases hx : x ∈ ball (0 : V) R
    · simp only [g, indicator_of_mem hx, indicator_of_mem ((hp x).mpr hx)]
    · simp only [g, indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hp x).mp h))]
  have hI : (∫⁻ x, g (r • x) ∂μ) = ∫⁻ y, g y ∂Measure.map (fun x => r • x) μ :=
    (lintegral_map_equiv g e).symm
  rw [Measure.map_addHaar_smul μ hr.ne', abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)),
    lintegral_smul_measure, smul_eq_mul, he, lintegral_indicator measurableSet_ball] at hI
  dsimp only [g] at hI
  rw [lintegral_indicator (show MeasurableSet s from measurableSet_ball)] at hI
  rw [hI, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _),
    mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), ENNReal.ofReal_one, one_mul]

theorem finrank_complexModel_real (n : ℕ) : Module.finrank ℝ (ComplexModel n) = 2 * n :=
  (complexCoordinates n).toLinearEquiv.finrank_eq.symm.trans (finrank_E n)

private theorem realHessian_dilate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : V → ℝ} (hu : ContDiff ℝ 2 u) (r : ℝ) (x a b : V) :
    PshLines.realHessian (fun y => u (r • y)) x a b =
      r ^ 2 * PshLines.realHessian u (r • x) a b := by
  let L : V →L[ℝ] V := r • ContinuousLinearMap.id ℝ V
  have h := PshLines.realHessian_comp_affine hu L 0 x a b
  simp only [L, smul_apply, ContinuousLinearMap.id_apply, zero_add] at h
  rw [h, PshLines.realHessian_eq_fderiv, PshLines.realHessian_eq_fderiv]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

theorem modelHessian_dilate {n : ℕ} {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (r : ℝ) (x : ComplexModel n) :
    modelHessian (fun y => u (r • y)) x =
      (r : ℂ) ^ 2 • modelHessian u (r • x) := by
  ext i j : 1
  simp only [PshLines.FirstPass.MongeAmpere.complexHessian, realHessian_dilate hu,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

theorem smoothDensity_dilate {n : ℕ} {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (r : ℝ) (x : ComplexModel n) :
    smoothDensity (fun y => u (r • y)) x = r ^ (2 * n) * smoothDensity u (r • x) := by
  unfold smoothDensity
  rw [modelHessian_dilate hu, Matrix.det_smul, Fintype.card_fin,
    ← pow_mul, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem isSmoothPshOn_ball_dilate {n : ℕ} {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    {r R : ℝ} (hr : 0 < r) (hU : IsSmoothPshOn (ballDomain 0 (r * R)) u) :
    IsSmoothPshOn (ballDomain 0 R) (fun x => u (r • x)) := by
  let v (x : ComplexModel n) := u (r • x)
  have hv : ContDiff ℝ ∞ v := hu.comp (contDiff_id.const_smul r)
  have hF : Differentiable ℂ (fun x : ComplexModel n => r • x) := by
    let L : ComplexModel n →L[ℂ] ComplexModel n := (r : ℂ) • ContinuousLinearMap.id ℂ _
    have he : (fun x : ComplexModel n => r • x) = L := by
      funext x
      change r • x = (r : ℂ) • x
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) r x
    rw [he]
    exact L.differentiable
  have hMap : MapsTo (fun x : ComplexModel n => r • x) (ballDomain 0 R : Opens (ComplexModel n))
      (ballDomain 0 (r * R) : Opens (ComplexModel n)) := by
    intro x hx
    change r • x ∈ ball 0 (r * R)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx) hr
  exact isSmoothPshOn_of_psh hv.contDiffOn
    (locallyBoundedPsh_comp_holomorphic (isLocallyBoundedPshOn_of_isSmoothPshOn hU)
      hF.differentiableOn hMap).1

theorem topMeasure_univ_eq_lintegral_smoothDensity {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) univ =
      ∫⁻ x in (Ω : Set (ComplexModel n)), ENNReal.ofReal (smoothDensity u x) := by
  rw [topMeasure_eq_smoothMeasure hu, smoothMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

/-- Dilation preserves total mass when the radius and potential are
transformed together. -/
theorem topMeasure_univ_ball_dilate {n : ℕ} {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    {r R : ℝ} (hr : 0 < r) (hU : IsSmoothPshOn (ballDomain 0 (r * R)) u) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_ball_dilate hu hr hU)) univ =
      topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hU) univ := by
  rw [topMeasure_univ_eq_lintegral_smoothDensity (isSmoothPshOn_ball_dilate hu hr hU),
    topMeasure_univ_eq_lintegral_smoothDensity hU]
  change (∫⁻ x in ball (0 : ComplexModel n) R, ENNReal.ofReal (smoothDensity (fun y => u (r • y)) x)) =
    ∫⁻ x in ball (0 : ComplexModel n) (r * R), ENNReal.ofReal (smoothDensity u x)
  simp_rw [smoothDensity_dilate (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simpa only [finrank_complexModel_real] using
    lintegral_smul_ball (volume : Measure (ComplexModel n)) (fun x => ENNReal.ofReal (smoothDensity u x)) hr

end KEBall.BedfordTaylor
