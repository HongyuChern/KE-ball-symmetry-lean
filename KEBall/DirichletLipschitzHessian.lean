import KEBall.DirichletWeakHessianLimit
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Weak derivatives of Lipschitz gradient components on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem lipschitzWith_dirichletTest {n : ℕ}
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    ∃ C : ℝ≥0, LipschitzWith C (ψ : E n → ℝ) :=
  exists_lipschitzWith_of_contDiff_hasCompactSupport ψ.contDiff ψ.hasCompactSupport

private theorem integral_test_lineDeriv_of_lipschitz {n : ℕ}
    {f : E n → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (a : E n) :
    (∫ x, ψ x * lineDeriv ℝ f x a ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x a * f x ∂ν[n]) := by
  have : (volume0 n).IsAddHaarMeasure := by
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  obtain ⟨D, hD⟩ := lipschitzWith_dirichletTest ψ
  have hI := hf.integral_lineDeriv_mul_eq (μ := volume0 n) hD ψ.hasCompactSupport a
  have hTest (x : E n) : lineDeriv ℝ (ψ : E n → ℝ) x (-a) =
      -(fderiv ℝ (ψ : E n → ℝ) x a) := by
    rw [((ψ.contDiff.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (v := -a)).lineDeriv, map_neg]
  simp only [hTest, neg_mul, integral_neg] at hI
  have hLeft : (∫ x, ψ x * lineDeriv ℝ f x a ∂ν[n]) =
      ∫ x, lineDeriv ℝ f x a * ψ x ∂volume0 n := by
    rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ unitBall n
    · rw [indicator_of_mem hx, mul_comm]
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (ψ.tsupport_subset h)
      simp only [indicator_of_notMem hx, hz, mul_zero]
  have hRight :
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x a * f x ∂ν[n]) =
        ∫ x, fderiv ℝ (ψ : E n → ℝ) x a * f x ∂volume0 n := by
    rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ unitBall n
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hz : fderiv ℝ (ψ : E n → ℝ) x a = 0 := by
        have hNear := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (ψ.tsupport_subset h))
        simp only [hNear.fderiv_eq, fderiv_zero, Pi.zero_apply, zero_apply]
      simp only [hz, zero_mul]
  rwa [hLeft, hRight]

/-- Directional derivatives of a Lipschitz gradient satisfy the weak
integration by parts identity on the unit ball. -/
theorem integral_test_fderiv_lipschitz_gradient {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {C : ℝ≥0}
    (hG : LipschitzOnWith C G (closedUnitBall n))
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (a b : E n) :
    (∫ x, ψ x * (fderiv ℝ G x a) b ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x a * G x b ∂ν[n]) := by
  obtain ⟨W, hW, hGW⟩ := hG.extend_finite_dimension
  have hHaar : (volume0 n).IsAddHaarMeasure := by
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  let B : (E n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ b
  let f : E n → ℝ := B ∘ W
  have hf := B.lipschitz.comp hW
  have hAe := ae_restrict_of_ae (s := unitBall n) (hW.ae_differentiableAt (μ := volume0 n))
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hLeft : (fun x => ψ x * (fderiv ℝ G x a) b) =ᵐ[ν[n]]
      fun x => ψ x * lineDeriv ℝ f x a := by
    filter_upwards [hAe, hBall] with x hx hxB
    have hN : ∀ᶠ y in 𝓝 x, y ∈ unitBall n := isOpen_ball.mem_nhds hxB
    have he : G =ᶠ[𝓝 x] W := hN.mono fun y hy => hGW (ball_subset_closedBall hy)
    rw [he.fderiv_eq]
    have hD := B.hasFDerivAt.comp x hx.hasFDerivAt
    rw [(hD.hasLineDerivAt a).lineDeriv]
    rfl
  have hRight : (fun x => fderiv ℝ (ψ : E n → ℝ) x a * G x b) =ᵐ[ν[n]]
      fun x => fderiv ℝ (ψ : E n → ℝ) x a * f x := by
    filter_upwards [hBall] with x hx
    rw [hGW (ball_subset_closedBall hx)]
    rfl
  rw [integral_congr_ae hLeft, integral_congr_ae hRight]
  exact integral_test_lineDeriv_of_lipschitz hf ψ a


set_option maxHeartbeats 650000 in
/-- Distributional Hessian entries of a Lipschitz gradient agree almost
everywhere with the corresponding entries of its Fréchet derivative. -/
theorem ae_dirichletHessianMatrix_eq_complexHessianOfRealBilinear {n : ℕ}
    (hn : 0 < n) {G : E n → E n →L[ℝ] ℝ} {C : ℝ≥0}
    (hG : LipschitzOnWith C G (closedUnitBall n))
    (H : DirichletBallL2 n (DirichletHessianCoordinates n))
    (hWeak : ∀ (ψ : 𝓓(dirichletBallOpens n, ℝ)) (i j : Fin n),
      (∫ x, (ψ x : ℂ) * dirichletHessianMatrix (H x) i j ∂ν[n]) =
        -(∫ x, dirichletTestGradientHessianEntry i j ψ G x ∂ν[n])) :
    dirichletHessianMatrix ∘ H =ᵐ[ν[n]] complexHessianOfRealBilinear ∘ fderiv ℝ G := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  let A (i j : Fin n) (x : E n) := dirichletHessianMatrix (H x) i j
  let B (i j : Fin n) (x : E n) := complexHessianOfRealBilinear (fderiv ℝ G x) i j
  have hD (a b : E n) : MemLp (fun x => (fderiv ℝ G x a) b) 2 ν[n] := by
    have hMeas : Measurable (fun x => (fderiv ℝ G x a) b) :=
      (ContinuousLinearMap.measurable_apply b).comp (measurable_fderiv_apply_const ℝ G a)
    apply (memLp_top_of_bound (μ := ν[n]) hMeas.aestronglyMeasurable
      ((C : ℝ) * ‖a‖ * ‖b‖) ?_).mono_exponent (by simp)
    filter_upwards [hBall] with x hx
    have hNorm : ‖fderiv ℝ G x‖ ≤ C :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hG
    exact ((fderiv ℝ G x a).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ G x).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right hNorm (norm_nonneg _))) (norm_nonneg _))
  have hA (i j : Fin n) : MemLp (A i j) 2 ν[n] := by
    let L : DirichletHessianCoordinates n →L[ℂ] ℂ := EuclideanSpace.proj (i, j)
    change MemLp (L ∘ H) 2 ν[n]
    exact L.lipschitz.comp_memLp (L.map_zero) (Lp.memLp H)
  have hCast (a b : E n) : MemLp (fun x => ((fderiv ℝ G x a) b : ℂ)) 2 ν[n] :=
    Complex.ofRealCLM.lipschitz.comp_memLp (by simp) (hD a b)
  have hB (i j : Fin n) : MemLp (B i j) 2 ν[n] := by
    exact (((hCast (realDirection i) (realDirection j)).add
      (hCast (imagDirection i) (imagDirection j))).add
      (((hCast (realDirection i) (imagDirection j)).sub
        (hCast (imagDirection i) (realDirection j))).const_mul Complex.I)).const_mul ((4 : ℂ)⁻¹)
  have hTests (i j : Fin n) (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
      (∫ x, (ψ x : ℂ) * A i j x ∂ν[n]) = ∫ x, (ψ x : ℂ) * B i j x ∂ν[n] := by
    rw [hWeak ψ i j]
    let a := realDirection i
    let b := realDirection j
    let c := imagDirection i
    let d := imagDirection j
    let L (v w : E n) (x : E n) : ℂ := (ψ x * (fderiv ℝ G x v) w : ℝ)
    let R (v w : E n) (x : E n) : ℂ := (fderiv ℝ (ψ : E n → ℝ) x v * G x w : ℝ)
    have hL (v w : E n) : Integrable (L v w) ν[n] := by
      have hi := (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn (hD v w)).integrable
        (by norm_num)
      exact Complex.ofRealCLM.integrable_comp hi
    have hR (v w : E n) : Integrable (R v w) ν[n] := by
      have h₁ : Continuous (fun x => fderiv ℝ (ψ : E n → ℝ) x v) :=
        ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      have h₂ := hG.continuousOn.clm_apply (continuousOn_const (c := w))
      exact (Complex.continuous_ofReal.comp_continuousOn (h₁.continuousOn.mul h₂)).integrableOn_of_subset_isCompact
        (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
        (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
    have hEq (v w : E n) : (∫ x, L v w x ∂ν[n]) = -(∫ x, R v w x ∂ν[n]) := by
      unfold L R
      rw [integral_complex_ofReal (f := fun x => ψ x * (fderiv ℝ G x v) w),
        integral_complex_ofReal (f := fun x => fderiv ℝ (ψ : E n → ℝ) x v * G x w)]
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (integral_test_fderiv_lipschitz_gradient hG ψ v w)
    have he (x : E n) : (ψ x : ℂ) * B i j x =
        (4 : ℂ)⁻¹ * (L a b x + L c d x + Complex.I * (L a d x - L c b x)) := by
      simp only [B, complexHessianOfRealBilinear, L, a, b, c, d, Complex.ofReal_mul]
      ring
    simp_rw [he]
    change -(∫ x, (4 : ℂ)⁻¹ * (R a b x + R c d x + Complex.I * (R a d x - R c b x)) ∂ν[n]) = _
    have hExpand (F : E n → ℂ) (hF : Integrable F ν[n]) (G : E n → ℂ) (hG : Integrable G ν[n])
        (P : E n → ℂ) (hP : Integrable P ν[n]) (Q : E n → ℂ) (hQ : Integrable Q ν[n]) :
        (∫ x, (4 : ℂ)⁻¹ * (F x + G x + Complex.I * (P x - Q x)) ∂ν[n]) =
          (4 : ℂ)⁻¹ * ((∫ x, F x ∂ν[n]) + (∫ x, G x ∂ν[n]) +
            Complex.I * ((∫ x, P x ∂ν[n]) - (∫ x, Q x ∂ν[n]))) := by
      rw [integral_const_mul]
      have hM : Integrable (fun x => Complex.I * (P x - Q x)) ν[n] := (hP.sub hQ).const_mul Complex.I
      rw [integral_add (f := fun x => F x + G x) (g := fun x => Complex.I * (P x - Q x)) (hF.add hG) hM,
        integral_add hF hG, integral_const_mul, integral_sub hP hQ]
    rw [hExpand _ (hL a b) _ (hL c d) _ (hL a d) _ (hL c b),
      hExpand _ (hR a b) _ (hR c d) _ (hR a d) _ (hR c b), hEq, hEq, hEq, hEq]
    ring
  have hEntries (i j : Fin n) : A i j =ᵐ[ν[n]] B i j := by
    have hI (ψ : 𝓓(dirichletBallOpens n, ℝ)) {f : E n → ℂ} (hf : MemLp f 2 ν[n]) :
        Integrable (fun x => (ψ x : ℂ) * f x) ν[n] := by
      have hC : Continuous (fun x => (ψ x : ℂ)) := Complex.continuous_ofReal.comp ψ.continuous
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hC.continuousOn
      have hBound : MemLp (fun x => (ψ x : ℂ)) ⊤ ν[n] :=
        memLp_top_of_bound hC.aestronglyMeasurable M
          (hBall.mono fun x hx => hM x (ball_subset_closedBall hx))
      exact (hf.mul' (r := 2) hBound).integrable (by norm_num)
    have hRe : (fun x => (A i j x).re) =ᵐ[ν[n]] fun x => (B i j x).re := by
      have hA' : Integrable (fun x => (A i j x).re) ν[n] :=
        Complex.reCLM.integrable_comp ((hA i j).integrable (by norm_num))
      have hB' : Integrable (fun x => (B i j x).re) ν[n] :=
        Complex.reCLM.integrable_comp ((hB i j).integrable (by norm_num))
      apply ae_eq_on_unitBall_of_tests (hA'.locallyIntegrable.locallyIntegrableOn (unitBall n))
        (hB'.locallyIntegrable.locallyIntegrableOn (unitBall n))
      intro ψ
      have h := congrArg Complex.re (hTests i j ψ)
      have hI' {f : E n → ℂ} (hf : MemLp f 2 ν[n]) :
          (∫ x, ((ψ x : ℂ) * f x).re ∂ν[n]) = (∫ x, (ψ x : ℂ) * f x ∂ν[n]).re :=
        integral_re (hI ψ hf)
      rw [← hI' (hA i j), ← hI' (hB i j)] at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h
    have hIm : (fun x => (A i j x).im) =ᵐ[ν[n]] fun x => (B i j x).im := by
      have hA' : Integrable (fun x => (A i j x).im) ν[n] :=
        Complex.imCLM.integrable_comp ((hA i j).integrable (by norm_num))
      have hB' : Integrable (fun x => (B i j x).im) ν[n] :=
        Complex.imCLM.integrable_comp ((hB i j).integrable (by norm_num))
      apply ae_eq_on_unitBall_of_tests (hA'.locallyIntegrable.locallyIntegrableOn (unitBall n))
        (hB'.locallyIntegrable.locallyIntegrableOn (unitBall n))
      intro ψ
      have h := congrArg Complex.im (hTests i j ψ)
      have hI' {f : E n → ℂ} (hf : MemLp f 2 ν[n]) :
          (∫ x, ((ψ x : ℂ) * f x).im ∂ν[n]) = (∫ x, (ψ x : ℂ) * f x ∂ν[n]).im :=
        integral_im (hI ψ hf)
      rw [← hI' (hA i j), ← hI' (hB i j)] at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero] using h
    filter_upwards [hRe, hIm] with x hr hi
    exact Complex.ext hr hi
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hEntries i)] with x hx
  exact Matrix.ext hx

end KEBall
