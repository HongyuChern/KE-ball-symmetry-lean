import KEBall.MoserTrudingerGibbsIteration

/-! Pointwise density bounds and exact log-density derivatives in the original normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology
namespace KEBall.MoserTrudinger

theorem normalizingIntegral_bounds_of_nonpositive_bounded {n : ℕ} (hn : 0<n)
    {γ B : ℝ} (hγ : 0≤γ) {u : E n → ℝ}
    (hu : ContinuousOn u (closedUnitBall n))
    (hB : ∀ x∈closedUnitBall n, -B≤u x ∧ u x≤0) :
    1≤normalizingIntegral γ u ∧ normalizingIntegral γ u≤Real.exp (γ*B) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let ν := (volume0 n).restrict (unitBall n)
  have hI : Integrable (fun x => Real.exp (-γ*u x)) ν :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hu)).integrableOn_of_subset_isCompact
      (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hPt (x : E n) (hx : x∈unitBall n) :
      1≤Real.exp (-γ*u x) ∧ Real.exp (-γ*u x)≤Real.exp (γ*B) := by
    obtain ⟨hl,hh⟩ := hB x (ball_subset_closedBall hx)
    constructor
    · rw [← Real.exp_zero,Real.exp_le_exp]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hh
    · apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hl hγ]
  have hAE : ∀ᵐ x∂ν, x∈unitBall n := ae_restrict_mem measurableSet_ball
  constructor
  · have h := integral_mono_ae (integrable_const (1 : ℝ)) hI (hAE.mono fun x hx => (hPt x hx).1)
    simpa only [integral_const,probReal_univ,one_smul,normalizingIntegral] using h
  · have h := integral_mono_ae hI (integrable_const (Real.exp (γ*B)))
      (hAE.mono fun x hx => (hPt x hx).2)
    simpa only [integral_const,probReal_univ,one_smul,normalizingIntegral] using h

theorem gibbsDensity_bounds_of_nonpositive_bounded {n : ℕ} (hn : 0<n)
    {γ B : ℝ} (hγ : 0≤γ) {u : E n → ℝ}
    (hu : ContinuousOn u (closedUnitBall n))
    (hB : ∀ x∈closedUnitBall n, -B≤u x ∧ u x≤0) :
    ∀ x∈closedUnitBall n, Real.exp (-(γ*B))≤gibbsDensity γ u x ∧
      gibbsDensity γ u x≤Real.exp (γ*B) := by
  have hZ := normalizingIntegral_bounds_of_nonpositive_bounded hn hγ hu hB
  have hZpos : 0<normalizingIntegral γ u := zero_lt_one.trans_le hZ.1
  intro x hx
  obtain ⟨hl,hh⟩ := hB x hx
  have hLow : 1≤Real.exp (-γ*u x) := by
    rw [← Real.exp_zero,Real.exp_le_exp]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hh
  have hHigh : Real.exp (-γ*u x)≤Real.exp (γ*B) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hl hγ]
  constructor
  · rw [gibbsDensity,Real.exp_neg,← one_div]
    exact div_le_div₀ (Real.exp_nonneg _) hLow hZpos hZ.2
  · exact (div_le_self (Real.exp_nonneg _) hZ.1).trans hHigh

theorem log_gibbsDensity_eq {n : ℕ} (hn : 0<n) (γ : ℝ)
    {u : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n)) (x : E n) :
    Real.log (gibbsDensity γ u x)=-γ*u x-Real.log (normalizingIntegral γ u) := by
  rw [gibbsDensity,Real.log_div (Real.exp_ne_zero _)
    (normalizingIntegral_pos_of_continuousOn hn hu γ).ne',Real.log_exp]

theorem fderiv_log_gibbsDensity {n : ℕ} (hn : 0<n) (γ : ℝ)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) (x : E n) :
    fderiv ℝ (fun y => Real.log (gibbsDensity γ u y)) x=(-γ) • fderiv ℝ u x := by
  have he : (fun y => Real.log (gibbsDensity γ u y))=
      (fun y => -γ*u y-Real.log (normalizingIntegral γ u)) :=
    funext (log_gibbsDensity_eq hn γ hu.continuous.continuousOn)
  rw [he,fderiv_fun_sub ((hu.differentiable (by simp) x).const_mul _) (differentiableAt_const _),
    fderiv_fun_const,Pi.zero_apply,fderiv_const_mul (hu.differentiable (by simp) x),sub_zero]

end KEBall.MoserTrudinger
