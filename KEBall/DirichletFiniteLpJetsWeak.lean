import KEBall.DirichletAngularWordFiniteLpJets
import KEBall.DirichletSmoothRepresentative

/-! Actual finite Lp jets represent the original tested weak derivatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Distributions ENNReal Topology
namespace KEBall
local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem integral_dirichletTest_euclideanDivergence_interior {n : ℕ} (hn : 0 < n)
    (ψ : 𝓓B[n]) {V : E n → E n} (hV : ContDiffOn ℝ ∞ V (unitBall n)) :
    (∫ x, ψ x * euclideanDivergence V x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (V x) ∂ν[n]) := by
  let W (x : E n) := ψ x • V x
  have hW : ContDiff ℝ ∞ W := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ unitBall n
    · exact ψ.contDiff.contDiffAt.smul (hV.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hSupp : x ∉ tsupport (ψ : E n → ℝ) := fun hx' => hx (ψ.tsupport_subset hx')
      apply (contDiffAt_const (c := (0 : E n))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hSupp] with y hy
      change ψ y • V y = 0
      rw [hy, Pi.zero_apply, zero_smul]
  have hFlux (θ : Sphere n) : inner ℝ θ.1 (W θ.1) = 0 := by
    have hz : ψ θ.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp θ.2).ge)
        (mem_ball_zero_iff.mp (ψ.tsupport_subset hs))
    simp [W, hz]
  have hZero : (∫ x, euclideanDivergence W x ∂ν[n]) = 0 := by
    simpa only [hFlux, integral_zero, mul_zero] using
      integral_unitBall_divergence_normalized hn (hW.of_le (by simp))
  have hD (x : E n) (hx : x ∈ unitBall n) :
      euclideanDivergence W x = ψ x * euclideanDivergence V x + fderiv ℝ (ψ : E n → ℝ) x (V x) :=
    euclideanDivergence_smul (ψ.contDiff.differentiable (by simp) x)
      ((hV.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
  have hI₁ : Integrable (fun x => ψ x * euclideanDivergence V x) ν[n] := by
    have hC : ContinuousOn (euclideanDivergence V) (unitBall n) := by
      unfold euclideanDivergence
      exact continuousOn_finsetSum _ fun i _ =>
        (((EuclideanSpace.proj i : E n →L[ℝ] ℝ).contDiff.comp_contDiffOn hV).fderiv_of_isOpen
          isOpen_ball (by simp) (m := 0)).continuousOn.clm_apply continuousOn_const
    exact ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (hC.locallyIntegrableOn measurableSet_ball)
  have hI₂ : Integrable (fun x => fderiv ℝ (ψ : E n → ℝ) x (V x)) ν[n] := by
    let ψ' := TestFunction.fderivCLM ℝ ⊤ ⊤ ψ
    have he (x : E n) : ψ' x = fderiv ℝ (ψ : E n → ℝ) x :=
      congrFun (TestFunction.fderivCLM_apply_of_le (𝕜 := ℝ) (k := (⊤ : ℕ∞)) ψ (by simp)) x
    simp_rw [← he]
    exact ψ'.integrable_bilin (ContinuousLinearMap.apply ℝ ℝ (E := E n)).flip
      (hV.continuousOn.locallyIntegrableOn measurableSet_ball)
  have h := (setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball) hD).symm.trans hZero
  rw [integral_add hI₁ hI₂] at h
  linarith only [h]

theorem integral_dirichletTest_directionalDerivative_interior {n : ℕ} (hn : 0 < n)
    (ψ : 𝓓B[n]) {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f (unitBall n)) (d : E n) :
    (∫ x, ψ x * fderiv ℝ f x d ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]) := by
  let V (x : E n) := f x • d
  have hV : ContDiffOn ℝ ∞ V (unitBall n) := hf.smul contDiffOn_const
  have h := integral_dirichletTest_euclideanDivergence_interior hn ψ hV
  have hDiv (x : E n) (hx : x ∈ unitBall n) : euclideanDivergence V x = fderiv ℝ f x d := by
    rw [euclideanDivergence_smul ((hf.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      (differentiableAt_const d)]
    simp [euclideanDivergence]
  have he : (∫ x, ψ x * euclideanDivergence V x ∂ν[n]) =
      ∫ x, ψ x * fderiv ℝ f x d ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    rw [hDiv x hx]
  rw [he] at h
  simpa only [V,map_smul,smul_eq_mul,mul_comm] using h

theorem HasDirichletFiniteLpJets.weakDerivativesL2 {n k : ℕ} (hn : 0 < n)
    {f : E n → ℝ}
    (hf : HasDirichletFiniteLpJets (unitBall n) ν[n] k f) : HasDirichletWeakDerivativesL2 f k := by
  induction k generalizing f with
  | zero => exact HasDirichletWeakDerivativesL2.zero_order (hf.2 2 (by norm_num))
  | succ k ih =>
    refine hasDirichletWeakDerivativesL2_succ_iff.mpr ⟨hf.1.2 2 (by norm_num),fun d => ?_⟩
    exact ⟨_,ih (hf.2 d),fun ψ => integral_dirichletTest_directionalDerivative_interior hn ψ hf.contDiffOn d⟩

theorem hasDirichletWeakDerivativesL2_two_angularWord_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletWeakDerivativesL2 (dirichletAngularWord R u) 2 :=
  (hasDirichletFiniteLpJets_two_angularWord_of_C2_solution hn hu huS hu0 hPos hf hEq R).weakDerivativesL2 hn

end KEBall
