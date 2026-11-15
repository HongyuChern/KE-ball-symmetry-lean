import KEBall.DirichletWeakSobolev

/-! The lower-order part of the Leibniz rule for weak derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem dirichletTestLineDerivative_mul {n : ℕ}
    (ψ : 𝓓B[n]) (d : E n) {c : E n → ℝ} (hc : ContDiff ℝ ∞ c)
    (hc' : ContDiff ℝ ∞ (fun x => fderiv ℝ c x d)) :
    dirichletTestLineDerivative d (dirichletTestMul ψ hc) =
      dirichletTestMul (dirichletTestLineDerivative d ψ) hc + dirichletTestMul ψ hc' := by
  apply TestFunction.ext
  intro x
  change fderiv ℝ (fun y => ψ y * c y) x d =
    fderiv ℝ (ψ : E n → ℝ) x d * c x + ψ x * fderiv ℝ c x d
  rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hc.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- When a smooth multiplier is differentiated at least once, the remainder
uses one fewer derivative of the weak factor than the full derivative. -/
theorem exists_dirichletWeakDerivativeTest_mul_remainder {n : ℕ} (hn : 0 < n)
    {f c : E n → ℝ} (hc : ContDiff ℝ ∞ c)
    (d : E n) (ds : List (E n)) (k : ℕ)
    (hf : HasDirichletWeakDerivativesL2 f (k + ds.length)) :
    ∃ R : E n → ℝ, HasDirichletWeakDerivativesL2 R k ∧ ∀ ψ : 𝓓B[n],
      dirichletWeakDerivativeTest (fun x => c x * f x) (d :: ds) ψ =
        dirichletWeakDerivativeTest f (d :: ds) (dirichletTestMul ψ hc) +
          ∫ x, ψ x * R x ∂ν[n] := by
  induction ds generalizing d k with
  | nil =>
      let cd (x : E n) := fderiv ℝ c x d
      have hcd : ContDiff ℝ ∞ cd := (hc.fderiv_right (by simp)).clm_apply contDiff_const
      refine ⟨fun x => cd x * f x, hf.mul_smooth hn hcd, fun ψ => ?_⟩
      simp only [dirichletWeakDerivativeTest, dirichletTestLineDerivative_mul ψ d hc hcd]
      have : NeZero n := ⟨hn.ne'⟩
      have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
      have hI (τ : 𝓓B[n]) : Integrable (fun x => τ x * f x) ν[n] :=
        (memLp_dirichlet_mul_of_continuousOn τ.continuous.continuousOn hf.1).integrable (by norm_num)
      let τ₀ := dirichletTestMul (dirichletTestLineDerivative d ψ) hc
      let τ₁ := dirichletTestMul ψ hcd
      change -(∫ x, dirichletTestLineDerivative d ψ x * (c x * f x) ∂ν[n]) =
        -(∫ x, (τ₀ x + τ₁ x) * f x ∂ν[n]) + ∫ x, ψ x * (cd x * f x) ∂ν[n]
      simp only [add_mul, integral_add (hI τ₀) (hI τ₁)]
      simp only [τ₀, τ₁, dirichletTestMul_apply, mul_assoc]
      ring
  | cons e es ih =>
      have hf' : HasDirichletWeakDerivativesL2 f ((k + 1) + es.length) := by
        rwa [show (k + 1) + es.length = k + (e :: es).length by simp; omega]
      obtain ⟨E', hE, heE⟩ := ih e (k + 1) hf'
      obtain ⟨D, hD, heD⟩ := (hasDirichletWeakDerivativesL2_succ_iff.mp hE).2 d
      obtain ⟨F, hF, heF⟩ := hf.exists_weakDerivativeTestL2 (e :: es) k
      let cd (x : E n) := fderiv ℝ c x d
      have hcd : ContDiff ℝ ∞ cd := (hc.fderiv_right (by simp)).clm_apply contDiff_const
      have hcdF : HasDirichletWeakDerivativesL2 (fun x => cd x * F x) k := hF.mul_smooth hn hcd
      refine ⟨D + (fun x => cd x * F x), hD.add hn hcdF, fun ψ => ?_⟩
      let τ := dirichletTestLineDerivative d ψ
      have h := heE τ
      have hD' := heD ψ
      change (∫ x, ψ x * D x ∂ν[n]) = -(∫ x, τ x * E' x ∂ν[n]) at hD'
      have heT := heF (dirichletTestMul ψ hcd)
      simp only [dirichletTestMul_apply, mul_assoc] at heT
      change -dirichletWeakDerivativeTest (fun x => c x * f x) (e :: es) τ =
        -dirichletWeakDerivativeTest f (e :: es)
          (dirichletTestLineDerivative d (dirichletTestMul ψ hc)) +
          ∫ x, ψ x * (D x + cd x * F x) ∂ν[n]
      rw [dirichletTestLineDerivative_mul ψ d hc hcd, dirichletWeakDerivativeTest_add_test hn hf.1]
      have : NeZero n := ⟨hn.ne'⟩
      have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
      have hI {w : E n → ℝ} (hw : MemLp w 2 ν[n]) : Integrable (fun x => ψ x * w x) ν[n] :=
        (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hw).integrable (by norm_num)
      simp only [mul_add, integral_add (hI hD.1) (hI hcdF.1)]
      linarith only [h, hD', heT]

end KEBall
