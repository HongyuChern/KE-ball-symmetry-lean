import KEBall.DirichletSobolev
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! Translation difference quotients for compactly supported smooth functions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory Set
open scoped ContDiff Interval

namespace KEBall

theorem sub_translate_eq_integral_fderiv {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x v : E n) (h : ℝ) :
    f (x + h • v) - f x = h * ∫ s in (0 : ℝ)..1, fderiv ℝ f (x + s • (h • v)) v := by
  let D (s : ℝ) := fderiv ℝ f (x + s • (h • v)) v
  have hD : Continuous D := by
    have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by simp)).continuous
    exact (hd.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hDeriv (s : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • (h • v))) (h * D s) s := by
    have hLine : HasDerivAt (fun t : ℝ => x + t • (h • v)) (h • v) s := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const (h • v)).const_add x
    have hd := (hf.differentiable (by simp) (x + s • (h • v))).hasFDerivAt.comp_hasDerivAt s hLine
    simpa only [Function.comp_def, map_smul, smul_eq_mul, D] using hd
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hDeriv s)
    ((continuous_const.mul hD).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hInt
  simpa only [one_smul, zero_smul, add_zero, D] using hInt.symm

theorem integral_sq_translationDifferenceQuotient_le {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfC : HasCompactSupport f) (v : E n) {h : ℝ} (hh : h ≠ 0) :
    (∫ x, (h⁻¹ * (f (x + h • v) - f x)) ^ 2) ≤ ∫ x, (fderiv ℝ f x v) ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  let D (x : E n) (s : ℝ) := fderiv ℝ f (x + s • (h • v)) v
  let J (x : E n) := (fderiv ℝ f x v) ^ 2
  have hD : Continuous (fun p : E n × ℝ => D p.1 p.2) := by
    have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by simp)).continuous
    exact (hd.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hJ : Integrable J := by
    have hc : Continuous (fun x => fderiv ℝ f x v) :=
      (hf.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
    apply (hc.pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two] using (hfC.fderiv_apply ℝ v).mul_right
      (f' := fun x => fderiv ℝ f x v)
  have hQ : Integrable (fun x => (h⁻¹ * (f (x + h • v) - f x)) ^ 2) := by
    have hTrans : HasCompactSupport (fun x => f (x + h • v)) :=
      hfC.comp_homeomorph (Homeomorph.addRight (h • v))
    have hBase : HasCompactSupport (fun x => h⁻¹ * (f (x + h • v) - f x)) :=
      HasCompactSupport.mul_left (f := fun _ => h⁻¹) (hTrans.sub hfC)
    have hc : Continuous (fun x => h⁻¹ * (f (x + h • v) - f x)) := by fun_prop
    apply (hc.pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two] using hBase.mul_right
      (f' := fun x => h⁻¹ * (f (x + h • v) - f x))
  have hP (x : E n) : (h⁻¹ * (f (x + h • v) - f x)) ^ 2 ≤ ∫ s, (D x s) ^ 2 ∂μ := by
    have hDx : Continuous (D x) := hD.comp (continuous_const.prodMk continuous_id)
    have hI : Integrable (D x) μ := (hDx.intervalIntegrable 0 1).1
    have hI₂ : Integrable (fun s => (D x s) ^ 2) μ := ((hDx.pow 2).intervalIntegrable 0 1).1
    have hj := ((by decide : Even (2 : ℕ)).convexOn_pow (𝕜 := ℝ)).map_integral_le
      (continuous_id.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) hI hI₂
    have he : h⁻¹ * (f (x + h • v) - f x) = ∫ s, D x s ∂μ := by
      rw [sub_translate_eq_integral_fderiv hf, ← mul_assoc, inv_mul_cancel₀ hh, one_mul,
        intervalIntegral.integral_of_le zero_le_one]
    rw [he]
    exact hj
  have hTrans (s : ℝ) : Integrable (fun x => (D x s) ^ 2) :=
    (measurePreserving_add_right volume (s • (h • v))).integrable_comp_of_integrable hJ
  have hEq (s : ℝ) : (∫ x, (D x s) ^ 2) = ∫ x, J x :=
    integral_add_right_eq_self J (s • (h • v))
  have hProd : Integrable (fun p : E n × ℝ => (D p.1 p.2) ^ 2) (volume.prod μ) := by
    apply (integrable_prod_iff' (hD.pow 2).aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hTrans, ?_⟩
    have he (s : ℝ) : (∫ x, ‖(D x s) ^ 2‖) = ∫ x, J x := by
      calc
        _ = ∫ x, (D x s) ^ 2 := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => Real.norm_of_nonneg (sq_nonneg (D x s))
        _ = _ := hEq s
    exact (integrable_const (∫ x, J x) (μ := μ)).congr
      (Eventually.of_forall fun s => (he s).symm)
  calc
    _ ≤ ∫ x, ∫ s, (D x s) ^ 2 ∂μ := integral_mono hQ hProd.integral_prod_left hP
    _ = ∫ s, (∫ x, (D x s) ^ 2) ∂μ := integral_integral_swap hProd
    _ = _ := by simp_rw [hEq]; simp [J]

end KEBall
