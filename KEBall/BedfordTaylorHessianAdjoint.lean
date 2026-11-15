import KEBall.BedfordTaylorAffineHessian

/-!
# The adjoint of the complex Hessian on real tests
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

namespace KEBall.BedfordTaylor

open PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] {U : Opens E} {μ : Measure E}

omit [MeasurableSpace E] [BorelSpace E] in
theorem tsupport_classicalComplexHessianEntry_subset
    (φ : 𝓓(U, ℝ)) (a b : E) :
    tsupport (classicalComplexHessianEntry φ a b) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hn
  apply hx
  rw [classicalComplexHessianEntry_eq_realHessian φ.contDiff.contDiffAt,
    realHessian_eq_zero_of_notMem_tsupport hn, realHessian_eq_zero_of_notMem_tsupport hn,
    realHessian_eq_zero_of_notMem_tsupport hn, realHessian_eq_zero_of_notMem_tsupport hn]
  simp

theorem integrable_classicalComplexHessianEntry_mul (φ : 𝓓(U, ℝ)) (a b : E)
    {g : E → ℂ} (hg : LocallyIntegrableOn g U μ) :
    Integrable (fun x => classicalComplexHessianEntry φ a b x * g x) μ := by
  let h := classicalComplexHessianEntry φ a b
  have hs : tsupport h ⊆ tsupport φ := tsupport_classicalComplexHessianEntry_subset φ a b
  have hd : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (contDiffOn_classicalComplexHessianEntry
      (U := ⊤) φ.contDiff.contDiffOn a b).contDiffAt (by simp)
  let ψ : 𝓓(U, ℂ) := ⟨h, hd, φ.hasCompactSupport.of_isClosed_subset isClosed_closure hs,
    hs.trans φ.tsupport_subset⟩
  exact ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hg

/-- Testing two distributional Wirtinger derivatives of a regular
density transfers both derivatives to the test function. -/
theorem wirtingerHessian_regular_apply {g : E → ℂ} (hg : LocallyIntegrableOn g U μ)
    (a b : E) (φ : 𝓓(U, ℝ)) :
    wirtingerDerivative a (Complex.I • a) (wirtingerDerivative b (-(Complex.I • b))
      (complexRegularDistribution μ g hg)) φ =
      ∫ x, classicalComplexHessianEntry φ a b x * g x ∂μ := by
  let η (v w : E) : 𝓓(U, ℝ) :=
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ)
  let f (v w : E) (x : E) := η v w x • g x
  have hf (v w : E) : Integrable (f v w) μ :=
    (η v w).integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
  let c : ℂ := 1 / 2
  have heq : wirtingerDerivative a (Complex.I • a) (wirtingerDerivative b (-(Complex.I • b))
      (complexRegularDistribution μ g hg)) φ =
      c * (c * ((∫ x, f b a x ∂μ) - Complex.I * (∫ x, f (-(Complex.I • b)) a x ∂μ)) -
        Complex.I * (c * ((∫ x, f b (Complex.I • a) x ∂μ) -
          Complex.I * (∫ x, f (-(Complex.I • b)) (Complex.I • a) x ∂μ)))) := by
    simp only [wirtingerDerivative, directionalDerivative, Distribution.lineDerivCLM_apply,
      smul_apply, sub_apply, smul_eq_mul,
      complexRegularDistribution_apply, c, f, η]
    ring
  let F (v : E) (x : E) := c * (f b v x - Complex.I * f (-(Complex.I • b)) v x)
  have hF (v : E) : Integrable (F v) μ :=
    ((hf b v).sub ((hf (-(Complex.I • b)) v).const_mul _)).const_mul _
  have hR (v : E) :
      c * ((∫ x, f b v x ∂μ) - Complex.I * (∫ x, f (-(Complex.I • b)) v x ∂μ)) =
        ∫ x, F v x ∂μ := by
    rw [← integral_const_mul (f := f (-(Complex.I • b)) v),
      ← integral_sub (hf b v) ((hf (-(Complex.I • b)) v).const_mul _), ← integral_const_mul]
  rw [heq, hR a, hR (Complex.I • a), ← integral_const_mul (f := F (Complex.I • a)),
    ← integral_sub (hF a) ((hF (Complex.I • a)).const_mul _), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hs (v w : E) : realHessian φ x v w = realHessian φ x w v := by
    rw [realHessian_eq_fderiv, realHessian_eq_fderiv]
    exact (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)).eq _ _
  have hn (v w : E) : realHessian φ x (-v) w = -realHessian φ x v w := by
    simp [realHessian_eq_fderiv]
  rw [classicalComplexHessianEntry_eq_realHessian φ.contDiff.contDiffAt]
  simp only [F, f, η, c, Complex.real_smul, testFunction_lineDerivCLM_lineDerivCLM_apply,
    hn, Complex.ofReal_neg]
  rw [hs b a, hs (Complex.I • b) a, hs b (Complex.I • a), hs (Complex.I • b) (Complex.I • a)]
  push_cast
  ring_nf
  simp
  ring

end KEBall.BedfordTaylor
