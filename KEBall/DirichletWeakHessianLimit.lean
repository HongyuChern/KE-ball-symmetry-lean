import KEBall.DirichletHessianLimitEquation
import KEBall.DirichletNormalRecovery
import KEBall.MoserTrudingerSmoothGibbsExtension

/-! The almost-everywhere limit represents the weak complex Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem smooth_integral_test_realHessian {n : ℕ} (hn : 0 < n)
    {v : E n → ℝ} (hv : SmoothNear (closedUnitBall n) v)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (a b : E n) :
    (∫ x, ψ x * realHessian v x a b ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x a * fderiv ℝ v x b ∂ν[n]) := by
  obtain ⟨w, hw, hwv⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hv
  let g (x : E n) := fderiv ℝ w x b
  have hg : ContDiff ℝ ∞ g :=
    (hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hg (contDiff_const (c := a))
  have hz (x : E n) :
      dirichletVectorDivergence (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) (fun _ => a) x = 0 := by
    simp [dirichletVectorDivergence]
  dsimp only at h
  simp only [hz, mul_zero, add_zero] at h
  have h₂ (x : E n) : fderiv ℝ g x a = realHessian w x a b := by
    have hF := (hw.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hD := hF.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
    change HasFDerivAt g _ x at hD
    rw [hD.fderiv]
    simp only [ContinuousLinearMap.comp_zero, zero_add]
    rfl
  simp only [h₂] at h
  have hLeft :
      (∫ x, ψ x * realHessian v x a b ∂ν[n]) = ∫ x, ψ x * realHessian w x a b ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have h₁ : fderiv ℝ w =ᶠ[𝓝 x] fderiv ℝ v := (hwv x (ball_subset_closedBall hx)).fderiv
    change ψ x * fderiv ℝ (fderiv ℝ v) x a b = ψ x * fderiv ℝ (fderiv ℝ w) x a b
    rw [h₁.fderiv_eq]
  have hRight :
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x a * fderiv ℝ v x b ∂ν[n]) =
        ∫ x, fderiv ℝ (ψ : E n → ℝ) x a * g x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    rw [show g x = fderiv ℝ w x b from rfl, (hwv x (ball_subset_closedBall hx)).fderiv_eq]
  rw [hLeft, hRight, h]
  simp


/-- The first-derivative pairing for one complex Hessian entry. -/
noncomputable def dirichletTestGradientHessianEntry {n : ℕ} (i j : Fin n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (G : E n → E n →L[ℝ] ℝ) (x : E n) : ℂ :=
  let D (a b : E n) : ℂ := (fderiv ℝ (ψ : E n → ℝ) x a * G x b : ℝ)
  (4 : ℂ)⁻¹ * (D (realDirection i) (realDirection j) + D (imagDirection i) (imagDirection j) +
    Complex.I * (D (realDirection i) (imagDirection j) - D (imagDirection i) (realDirection j)))

/-- Integration by parts for a smooth complex Hessian tested on the ball. -/
theorem smooth_integral_test_complexHessian {n : ℕ} (hn : 0 < n)
    {v : E n → ℝ} (hv : SmoothNear (closedUnitBall n) v)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (i j : Fin n) :
    (∫ x, (ψ x : ℂ) * complexHessian v x i j ∂ν[n]) =
      -(∫ x, dirichletTestGradientHessianEntry i j ψ (fderiv ℝ v) x ∂ν[n]) := by
  let a := realDirection i
  let b := realDirection j
  let c := imagDirection i
  let d := imagDirection j
  let L (a b : E n) (x : E n) : ℂ := (ψ x * realHessian v x a b : ℝ)
  let R (a b : E n) (x : E n) : ℂ := (fderiv ℝ (ψ : E n → ℝ) x a * fderiv ℝ v x b : ℝ)
  have hL (a b : E n) : Integrable (L a b) ν[n] := by
    obtain ⟨U, hU, hSub, hC⟩ := hv
    have hD := (((hC.fderiv_of_isOpen hU (by simp) (m := ∞)).fderiv_of_isOpen hU (by simp)
      (m := ∞)).clm_apply (contDiffOn_const (c := a))).clm_apply (contDiffOn_const (c := b))
    have hReal : ContinuousOn (fun x => ψ x * realHessian v x a b) U :=
      ψ.continuous.continuousOn.mul hD.continuousOn
    exact ((Complex.continuous_ofReal.comp_continuousOn hReal).mono hSub).integrableOn_of_subset_isCompact
      (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hR (a b : E n) : Integrable (R a b) ν[n] := by
    obtain ⟨U, hU, hSub, hC⟩ := hv
    have hD := ((hC.fderiv_of_isOpen hU (by simp) (m := ∞)).clm_apply
      (contDiffOn_const (c := b))).continuousOn
    have hTest : ContinuousOn (fun x => fderiv ℝ (ψ : E n → ℝ) x a) U := ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := a))).continuous.continuousOn
    exact ((Complex.continuous_ofReal.comp_continuousOn (hTest.mul hD)).mono hSub).integrableOn_of_subset_isCompact
      (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hEq (a b : E n) : (∫ x, L a b x ∂ν[n]) = -(∫ x, R a b x ∂ν[n]) := by
    unfold L R
    rw [integral_complex_ofReal (f := fun x => ψ x * realHessian v x a b),
      integral_complex_ofReal (f := fun x => fderiv ℝ (ψ : E n → ℝ) x a * fderiv ℝ v x b)]
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (smooth_integral_test_realHessian hn hv ψ a b)
  have hAE : (fun x => (ψ x : ℂ) * complexHessian v x i j) =ᵐ[ν[n]]
      (fun x => (4 : ℂ)⁻¹ * (L a b x + L c d x + Complex.I * (L a d x - L c b x))) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have hC : ContDiffAt ℝ 2 v x := (hv.contDiffAt (ball_subset_closedBall hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    rw [complexHessian_real_entry_C2 hC i j]
    simp only [L, a, b, c, d, Complex.ofReal_mul]
    ring
  rw [integral_congr_ae hAE]
  change (∫ x, (4 : ℂ)⁻¹ * (L a b x + L c d x + Complex.I * (L a d x - L c b x)) ∂ν[n]) =
      -(∫ x, (4 : ℂ)⁻¹ * (R a b x + R c d x + Complex.I * (R a d x - R c b x)) ∂ν[n])
  have hExpand (F : E n → ℂ) (hF : Integrable F ν[n]) (G : E n → ℂ) (hG : Integrable G ν[n])
      (P : E n → ℂ) (hP : Integrable P ν[n]) (Q : E n → ℂ) (hQ : Integrable Q ν[n]) :
      (∫ x, (4 : ℂ)⁻¹ * (F x + G x + Complex.I * (P x - Q x)) ∂ν[n]) =
        (4 : ℂ)⁻¹ * ((∫ x, F x ∂ν[n]) + (∫ x, G x ∂ν[n]) +
          Complex.I * ((∫ x, P x ∂ν[n]) - (∫ x, Q x ∂ν[n]))) := by
    rw [integral_const_mul]
    have hM : Integrable (fun x => Complex.I * (P x - Q x)) ν[n] :=
      (hP.sub hQ).const_mul Complex.I
    rw [integral_add (f := fun x => F x + G x) (g := fun x => Complex.I * (P x - Q x)) (hF.add hG) hM,
      integral_add hF hG, integral_const_mul, integral_sub hP hQ]
  rw [hExpand _ (hL a b) _ (hL c d) _ (hL a d) _ (hL c b),
    hExpand _ (hR a b) _ (hR c d) _ (hR a d) _ (hR c b),
    hEq, hEq, hEq, hEq]
  ring



theorem tendsto_integral_pairing_of_uniform_gradient {n : ℕ} [NeZero n] {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {V : E n → (E n →L[ℝ] ℝ) → A}
    (hV : Continuous (fun p : E n × (E n →L[ℝ] ℝ) => V p.1 p.2))
    {F : ℕ → E n → E n →L[ℝ] ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hContF : ∀ k, ContinuousOn (F k) (closedUnitBall n))
    (hGrad : TendstoUniformlyOn F G atTop (closedUnitBall n))
    {C : ℝ} (hEventually : ∀ᶠ k in atTop, ∀ x ∈ closedUnitBall n, ‖F k x‖ ≤ C) :
    Tendsto (fun k => ∫ x, V x (F k x) ∂ν[n]) atTop (𝓝 (∫ x, V x (G x) ∂ν[n])) := by
  let K := closedUnitBall n
  let R (k : ℕ) (x : E n) := V x (F k x)
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hAE := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : E n) 1).prod
    (isCompact_closedBall (0 : E n →L[ℝ] ℝ) C)).exists_bound_of_continuousOn hV.continuousOn
  apply tendsto_integral_filter_of_norm_le_const
  · apply Eventually.of_forall
    intro k
    have hPair : ContinuousOn (fun x : E n => (x, F k x)) K :=
      continuousOn_id.prodMk (hContF k)
    have hC : ContinuousOn (R k) K := hV.comp_continuousOn hPair
    exact (hC.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  · exact ⟨B, hEventually.mono fun k hk => hAE.mono fun x hx =>
      hB (x, F k x) ⟨ball_subset_closedBall hx, mem_closedBall_zero_iff.mpr (hk x (ball_subset_closedBall hx))⟩⟩
  · filter_upwards [hAE] with x hx
    have hF' : Tendsto (fun k => (x, F k x)) atTop (𝓝 (x, G x)) := by
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.prodMk (hGrad.tendsto_at (ball_subset_closedBall hx))
    exact (hV.tendsto (x, G x)).comp hF'

set_option maxHeartbeats 450000 in
/-- The almost-everywhere matrix limit is the distributional complex
Hessian of the potential whose gradient is the uniform limit. -/
theorem integral_test_dirichletHessianMatrix_eq_of_limits {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ k, SmoothNear (closedUnitBall n) (u k))
    {G : E n → E n →L[ℝ] ℝ} {H : E n → DirichletHessianCoordinates n}
    (hGrad : TendstoUniformlyOn (fun k => fderiv ℝ (u k)) G atTop (closedUnitBall n))
    (hH : ∀ᵐ x ∂ν[n], Tendsto (fun k => dirichletHessianCoordinates (complexHessian (u k) x))
      atTop (𝓝 (H x)))
    {D : ℝ} (hD : ∀ k x, x ∈ unitBall n → ‖complexHessian (u k) x‖ ≤ D)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (i j : Fin n) :
    (∫ x, (ψ x : ℂ) * dirichletHessianMatrix (H x) i j ∂ν[n]) =
      -(∫ x, dirichletTestGradientHessianEntry i j ψ G x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let K := closedUnitBall n
  let μ := ν[n]
  let L (k : ℕ) (x : E n) := (ψ x : ℂ) * complexHessian (u k) x i j
  let R (k : ℕ) := dirichletTestGradientHessianEntry i j ψ (fderiv ℝ (u k))
  let Dψ := fderiv ℝ (ψ : E n → ℝ)
  let F (k : ℕ) := fderiv ℝ (u k)
  have hAE := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hContF (k : ℕ) : ContinuousOn (F k) K := by
    obtain ⟨U, hU, hSub, hC⟩ := hu k
    exact ((hC.fderiv_of_isOpen hU (by simp) (m := ∞)).continuousOn.mono hSub)
  have hContψ : Continuous Dψ := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).continuous
  have hContG := hGrad.continuousOn (Eventually.of_forall hContF).frequently
  obtain ⟨Cψ, hCψ⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn ψ.continuous.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hContG
  have hEventually : ∀ᶠ k in atTop, ∀ x ∈ K, ‖F k x‖ ≤ C + 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hGrad) 1 zero_lt_one] with k hk x hx
    have h := hk x hx
    rw [dist_comm, dist_eq_norm] at h
    calc
      ‖F k x‖ = ‖F k x - G x + G x‖ := by rw [sub_add_cancel]
      _ ≤ ‖F k x - G x‖ + ‖G x‖ := norm_add_le _ _
      _ ≤ C + 1 := by linarith only [h, hC x hx]
  have hLeft : Tendsto (fun k => ∫ x, L k x ∂μ) atTop
      (𝓝 (∫ x, (ψ x : ℂ) * dirichletHessianMatrix (H x) i j ∂μ)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · apply Eventually.of_forall
      intro k
      obtain ⟨U, hU, hSub, hC⟩ := hu k
      have hC' : ContinuousOn (L k) (unitBall n) :=
        ((Complex.continuous_ofReal.comp ψ.continuous).continuousOn.mul
          (complexHessian_contDiffOn hU hC i j).continuousOn).mono (ball_subset_closedBall.trans hSub)
      exact hC'.aestronglyMeasurable measurableSet_ball
    · refine ⟨Cψ * D, Eventually.of_forall fun k => hAE.mono fun x hx => ?_⟩
      have hCψ₀ : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ x (ball_subset_closedBall hx))
      have hM : ‖complexHessian (u k) x i j‖ ≤ D :=
        (Matrix.norm_entry_le_entrywise_sup_norm _).trans (hD k x hx)
      change ‖(ψ x : ℂ) * complexHessian (u k) x i j‖ ≤ _
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hCψ x (ball_subset_closedBall hx)) hM (norm_nonneg _) hCψ₀
    · filter_upwards [hH] with x hx
      exact tendsto_const_nhds.mul (((EuclideanSpace.proj (i, j)).continuous.tendsto (H x)).comp hx)
  let V (x : E n) (P : E n →L[ℝ] ℝ) : ℂ :=
    dirichletTestGradientHessianEntry i j ψ (fun _ => P) x
  have hV : Continuous (fun p : E n × (E n →L[ℝ] ℝ) => V p.1 p.2) := by
    have hPair (a b : E n) : Continuous (fun p : E n × (E n →L[ℝ] ℝ) =>
        (Dψ p.1 a * p.2 b : ℝ)) :=
      ((hContψ.comp continuous_fst).clm_apply continuous_const).mul
        (continuous_snd.clm_apply continuous_const)
    have hTerm (a b : E n) : Continuous (fun p : E n × (E n →L[ℝ] ℝ) =>
        ((Dψ p.1 a * p.2 b : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hPair a b)
    exact (continuous_const (y := (4 : ℂ)⁻¹)).mul
      (((hTerm (realDirection i) (realDirection j)).add (hTerm (imagDirection i) (imagDirection j))).add
        ((continuous_const (y := Complex.I)).mul
          ((hTerm (realDirection i) (imagDirection j)).sub (hTerm (imagDirection i) (realDirection j)))))
  have hRight : Tendsto (fun k => ∫ x, R k x ∂μ) atTop
      (𝓝 (∫ x, dirichletTestGradientHessianEntry i j ψ G x ∂μ)) :=
    tendsto_integral_pairing_of_uniform_gradient hV hContF hGrad hEventually
  exact tendsto_nhds_unique hLeft (hRight.neg.congr fun k =>
    (smooth_integral_test_complexHessian hn (hu k) ψ i j).symm)

end KEBall
