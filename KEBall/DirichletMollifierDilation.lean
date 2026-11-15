import KEBall.DirichletWeakMollification
import KEBall.DirichletWholeRegularity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Dilation estimates for bringing mollified weak derivatives to the boundary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions ENNReal Pointwise
open PshLines (translationPairing contDiff_translationPairing)

namespace KEBall

private theorem fderiv_comp_real_smul {n : ℕ} {f : E n → ℝ}
    (hf : Differentiable ℝ f) (a : ℝ) (x d : E n) :
    fderiv ℝ (fun y : E n => f (a • y)) x d = a * fderiv ℝ f (a • x) d := by
  have h := (hf (a • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a)
  change fderiv ℝ (f ∘ (a • ·)) x d = _
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using
    congrArg (fun T : E n →L[ℝ] ℝ => T d) h.fderiv

theorem iteratedLineDerivative_comp_real_smul {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (ds : List (E n)) :
    (ds.foldr (fun d C x => fderiv ℝ C x d) (fun y => f (a • y))) =
      fun x => a ^ ds.length * (ds.foldr (fun d C y => fderiv ℝ C y d) f) (a • x) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      let F := ds.foldr (fun d C y => fderiv ℝ C y d) f
      have hF : ContDiff ℝ ∞ F := iteratedLineDerivative_contDiff hf ds
      have hFa : Differentiable ℝ (fun y : E n => F (a • y)) :=
        hF.differentiable (by simp) |>.comp (differentiable_id.const_smul a)
      funext x
      simp only [List.foldr_cons, List.length_cons, ih]
      change fderiv ℝ (fun y : E n => a ^ ds.length * F (a • y)) x d =
        a ^ (ds.length + 1) * fderiv ℝ F (a • x) d
      rw [fderiv_const_mul (hFa x), smul_apply, smul_eq_mul,
        fderiv_comp_real_smul (hF.differentiable (by simp)), pow_succ, mul_assoc]

private theorem smul_unitBall {n : ℕ} {a : ℝ} (ha : 0 < a) :
    a • unitBall n = ball (0 : E n) a := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_lt_of_lt_one_right ha (mem_ball_zero_iff.mp hy)
  · intro hx
    refine ⟨a⁻¹ • x, ?_, smul_inv_smul₀ ha.ne' x⟩
    change a⁻¹ • x ∈ ball (0 : E n) 1
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_lt_iff₀ ha).mpr (by simpa only [mul_one] using mem_ball_zero_iff.mp hx)

/-- The exact scaling of a square integral under the inward dilation of
an arbitrary finite-order directional derivative. -/
theorem setIntegral_sq_iteratedLineDerivative_comp_real_smul {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) (ds : List (E n)) :
    (∫ x in unitBall n, (ds.foldr (fun d C y => fderiv ℝ C y d) (fun y => f (a • y))) x ^ 2
      ∂volume0 n) = (a ^ ds.length) ^ 2 * (a ^ (2 * n))⁻¹ *
      ∫ x in ball (0 : E n) a, (ds.foldr (fun d C y => fderiv ℝ C y d) f) x ^ 2 ∂volume0 n := by
  have hHaar : (volume0 n).IsAddHaarMeasure := by
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  let F := ds.foldr (fun d C y => fderiv ℝ C y d) f
  simp_rw [iteratedLineDerivative_comp_real_smul hf a ds, mul_pow]
  rw [integral_const_mul,
    Measure.setIntegral_comp_smul (volume0 n) (fun x => F x ^ 2) (unitBall n) ha.ne',
    smul_unitBall ha, finrank_E, abs_of_nonneg (by positivity), smul_eq_mul, mul_assoc]

/-- An inward dilation makes the smooth mollifications available on the
entire closed ball. The squared derivative norm on the ball is uniformly
controlled by the norm of the corresponding weak derivative. -/
theorem setIntegral_sq_iteratedLineDerivative_dilatedMollification_le {n : ℕ}
    {f F : E n → ℝ} (φ : ContDiffBump (0 : E n)) {a : ℝ}
    (ha : 0 < a) (hRadius : φ.rOut + a ≤ 1)
    (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length)
    (hF : MemLp F 2 ((volume0 n).restrict (unitBall n)))
    (he : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ), dirichletWeakDerivativeTest f ds ψ =
      ∫ x in unitBall n, ψ x * F x ∂volume0 n) :
    (∫ x in unitBall n, (ds.foldr (fun d C y => fderiv ℝ C y d)
      (fun y => translationPairing ((volume0 n).restrict (unitBall n)) f
        (φ.normed (volume0 n)) (a • y))) x ^ 2 ∂volume0 n) ≤
      (a ^ (2 * n))⁻¹ * ∫ x in unitBall n, F x ^ 2 ∂volume0 n := by
  let μ := (volume0 n).restrict (unitBall n)
  let k := φ.normed (volume0 n)
  have hSmooth : ContDiff ℝ ∞ (translationPairing μ f k) :=
    contDiff_translationPairing (hf.1.locallyIntegrable (by norm_num))
      φ.hasCompactSupport_normed φ.contDiff_normed
  have hInside (x : E n) (hx : x ∈ ball (0 : E n) a)
      (y : E n) (hy : y ∈ tsupport k) : y + x ∈ unitBall n := by
    have hx' := mem_ball_zero_iff.mp hx
    change y ∈ tsupport (φ.normed (volume0 n)) at hy
    rw [φ.tsupport_normed_eq, mem_closedBall, dist_zero_right] at hy
    apply mem_ball_zero_iff.mpr
    exact (norm_add_le _ _).trans_lt
      ((add_lt_add_of_le_of_lt hy hx').trans_le hRadius)
  have hNorm := integral_sq_iteratedLineDerivative_dirichletTranslationPairing_le
    isOpen_ball φ hInside ds hf hF he
  have ha₁ : a ≤ 1 := by linarith [φ.rOut_pos]
  have hFactor : (a ^ ds.length) ^ 2 ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ ha.le ha₁)
  have hIntegral : 0 ≤ ∫ x in unitBall n, F x ^ 2 ∂volume0 n :=
    integral_nonneg fun _ => sq_nonneg _
  rw [setIntegral_sq_iteratedLineDerivative_comp_real_smul hSmooth ha ds]
  apply (mul_le_mul_of_nonneg_left hNorm (by positivity)).trans
  rw [mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hFactor
    (show 0 ≤ (a ^ (2 * n))⁻¹ * ∫ x in unitBall n, F x ^ 2 ∂volume0 n from
      mul_nonneg (by positivity) hIntegral)

end KEBall
