import KEBall.DirichletLipschitzMollification
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The derivative of a mollified Lipschitz function as an actual operator-valued convolution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped Convolution NNReal

noncomputable section

namespace KEBall

theorem integrable_dirichlet_mollified_fderiv {n : ℕ}
    {f : E n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (φ : ContDiffBump (0 : E n)) (x : E n) :
    Integrable (fun y => φ.normed volume (y - x) • fderiv ℝ f y) volume := by
  have hk : Integrable (fun y => φ.normed volume (y - x)) volume :=
    φ.integrable_normed.comp_sub_right x
  have hm : AEStronglyMeasurable (fun y => φ.normed volume (y - x) • fderiv ℝ f y) volume :=
    ((φ.continuous_normed.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).smul
      (measurable_fderiv ℝ f).aestronglyMeasurable
  apply (hk.mul_const (L : ℝ)).mono' hm
  apply Eventually.of_forall
  intro y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
  exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf) (φ.nonneg_normed _)

theorem dirichlet_normed_convolution_eq_pairing {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : E n → F) (φ : ContDiffBump (0 : E n)) (x : E n) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x =
      ∫ y, φ.normed volume (y - x) • h y := by
  simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  have hφ : φ.normed volume (x - y) = φ.normed volume (y - x) := by
    rw [← φ.normed_neg (x - y), neg_sub]
  change φ.normed volume (x - y) • h y = φ.normed volume (y - x) • h y
  rw [hφ]

theorem fderiv_dirichlet_mollify_eq_convolution {n : ℕ}
    {f : E n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (φ : ContDiffBump (0 : E n)) :
    fderiv ℝ (PshLines.mollify volume f φ) =
      φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ f := by
  funext x
  rw [dirichlet_normed_convolution_eq_pairing]
  ext v
  rw [ContinuousLinearMap.integral_apply (integrable_dirichlet_mollified_fderiv hf φ x),
    fderiv_dirichlet_mollify_of_lipschitz hf]
  simp only [PshLines.mollify, PshLines.translationPairing, _root_.smul_apply, smul_eq_mul, mul_comm]

end KEBall
