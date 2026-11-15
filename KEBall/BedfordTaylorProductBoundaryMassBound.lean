import KEBall.BedfordTaylorProductFiberMass
import KEBall.BedfordTaylorProductHessianBlocks

/-!
# The product mass controlled by the base Hessian and vertical mass
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn smoothDensity smoothMeasure)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

private theorem continuous_modelHessian {n : ℕ} {q : ComplexModel n → ℝ}
    (hq : ContDiff ℝ ∞ q) : Continuous (modelHessian q) := by
  have hD : Continuous (fderiv ℝ (fderiv ℝ q)) :=
    ((hq.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [PshLines.FirstPass.MongeAmpere.complexHessian, PshLines.realHessian_eq_fderiv]
  fun_prop

/-- Integrating the block determinant inequality bounds the ambient
measure of a product by the base Hessian bound and the vertical mass. -/
theorem topMeasure_preimage_prod_le_of_fiber_mass {n : ℕ}
    {q : ComplexModel (n + 1) → ℝ} {W : Opens (ComplexModel (n + 1))}
    (hq : ContDiff ℝ ∞ q) (hP : IsSmoothPshOn W q)
    {Z : Set (ComplexModel n)} {T : Set (ComplexModel 1)}
    (hZ : MeasurableSet Z) (hT : MeasurableSet T)
    (hZT : (complexProductCoordinates n 1) ⁻¹' (Z ×ˢ T) ⊆ W)
    {C : ℝ} (hC : 0 ≤ C)
    (hBase : ∀ x ∈ (complexProductCoordinates n 1) ⁻¹' (Z ×ˢ T),
      ∀ y : ComplexModel (n + 1), (complexProductCoordinates n 1 y).1 = 0 →
        PshLines.realHessian q x y y ≤ C * ‖y‖ ^ 2)
    {M : ℝ≥0∞}
    (hMass : ∀ w ∈ T, (∫⁻ z in Z, ENNReal.ofReal
      (modelHessian (fun y => q ((complexProductCoordinates n 1).symm (y, w))) z).det.re) ≤ M) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hP)
      ((complexProductCoordinates n 1) ⁻¹' (Z ×ˢ T)) ≤
      ENNReal.ofReal (((n + 1).factorial : ℝ) / Real.pi ^ (n + 1) * (C / 2)) *
        ((volume : Measure (ComplexModel 1)) T * M) := by
  let e := complexProductCoordinates n 1
  let S := e ⁻¹' (Z ×ˢ T)
  let a : ℝ := ((n + 1).factorial : ℝ) / Real.pi ^ (n + 1)
  let d (p : ComplexModel n × ComplexModel 1) := ENNReal.ofReal (smoothDensity q (e.symm p))
  let f (p : ComplexModel n × ComplexModel 1) :=
    ENNReal.ofReal (modelHessian (fun y => q (e.symm (y, p.2))) p.1).det.re
  have hD : Continuous (modelHessian q) := continuous_modelHessian hq
  have hdc : Continuous (smoothDensity q) :=
    continuous_const.mul (Complex.continuous_re.comp hD.matrix_det)
  have hd : Measurable d := (hdc.comp e.symm.continuous).measurable.ennreal_ofReal
  have hf : Measurable f := by
    have hq₂ := hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hEq (p : ComplexModel n × ComplexModel 1) : f p =
        ENNReal.ofReal (((modelHessian q (e.symm p)).submatrix
          (fun i : Fin n => finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1))
          (fun i : Fin n => finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1))).det.re) := by
      have h := complexProductHessian_fiber (n := n) (m := 1) hq₂ (e.symm p)
      change ((modelHessian q (e.symm p)).submatrix
        (fun i : Fin n => finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1))
        (fun i : Fin n => finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1))) =
        modelHessian (fun z => q (e.symm (z, (e (e.symm p)).2))) (e (e.symm p)).1 at h
      rw [e.apply_symm_apply] at h
      rw [h]
    rw [show f = _ from funext hEq]
    let I (i : Fin n) := finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1)
    have h := Complex.continuous_re.comp ((hD.comp e.symm.continuous).matrix_submatrix I I).matrix_det
    exact h.measurable.ennreal_ofReal
  have he : MeasurePreserving e := measurePreserving_complexProductCoordinates n 1
  have hSM : MeasurableSet S := e.continuous.measurable (hZ.prod hT)
  have hμ : topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hP) S =
      ∫⁻ p in Z ×ˢ T, d p := by
    rw [topMeasure_eq_smoothMeasure hP, smoothMeasure, withDensity_apply _ hSM,
      Measure.restrict_restrict hSM, inter_eq_left.mpr hZT]
    have h := he.setLIntegral_comp_preimage (hZ.prod hT) hd
    simpa only [d, S, e.symm_apply_apply] using h
  have hdom (p : ComplexModel n × ComplexModel 1) (hp : p ∈ Z ×ˢ T) :
      d p ≤ ENNReal.ofReal (a * (C / 2)) * f p := by
    have hmem : e.symm p ∈ S := by simpa only [S, mem_preimage, e.apply_symm_apply] using hp
    have h := complexHessian_det_re_le_fiber_mul_of_base_bound
      (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hP.2.2 _ (hZT hmem))
      (hBase _ hmem)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at h
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hle := mul_le_mul_of_nonneg_left h ha
    dsimp only [d, f, smoothDensity]
    rw [← ENNReal.ofReal_mul (show 0 ≤ a * (C / 2) by positivity)]
    exact ENNReal.ofReal_le_ofReal (hle.trans_eq (by dsimp [a]; ring))
  calc
    _ = ∫⁻ p in Z ×ˢ T, d p := hμ
    _ ≤ ∫⁻ p in Z ×ˢ T, ENNReal.ofReal (a * (C / 2)) * f p :=
      lintegral_mono_ae ((ae_restrict_mem (hZ.prod hT)).mono hdom)
    _ = ENNReal.ofReal (a * (C / 2)) * (∫⁻ w in T, ∫⁻ z in Z, f (z, w)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact congrArg (_ * ·) (setLIntegral_prod_symm f hf.aemeasurable)
    _ ≤ _ := by
      have h : (∫⁻ w in T, ∫⁻ z in Z, f (z, w)) ≤
          ∫⁻ _ in T, M ∂(volume : Measure (ComplexModel 1)) :=
        lintegral_mono_ae ((ae_restrict_mem hT).mono hMass)
      rw [lintegral_const, Measure.restrict_apply_univ, mul_comm M] at h
      exact mul_le_mul_right h _

end KEBall.BedfordTaylor
