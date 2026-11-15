import KEBall.DirichletWirtingerLog
import KEBall.GradientBridge

/-! The exact linearized logarithm identity with its inverse-Hessian gradient square. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 300000
open Matrix
open scoped ContDiff BigOperators Matrix Matrix.Norms.Elementwise
namespace KEBall
open KEBallProbe

theorem complexLaplacian_log_real {n : ℕ} (u : E n → ℝ)
    {f : E n → ℝ} {x : E n} (hf : ContDiffAt ℝ ∞ f x) (hf0 : f x≠0) :
    let w : Fin n → ℂ := fun i => partialZ i (fun y => (f y : ℂ)) x
    complexLaplacian u (fun y => Real.log (f y)) x=
      (f x)⁻¹*complexLaplacian u f x-
        (f x)⁻¹^2*(star w ⬝ᵥ ((complexHessian u x)⁻¹ *ᵥ w)).re := by
  let w : Fin n → ℂ := fun i => partialZ i (fun y => (f y : ℂ)) x
  have hH : complexHessian (fun y => Real.log (f y)) x=
      (f x)⁻¹ • complexHessian f x-(f x)⁻¹^2 • Matrix.vecMulVec w (star w) := by
    ext i j
    rw [complexHessian_log_real hf hf0,partialBar_ofReal (hf.differentiableAt (by simp))]
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply,
      Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,w]
    ring
  rw [complexLaplacian_eq_trace,hH,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_smul,
    Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_smul,Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec,dotProduct_comm]
  simp only [Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,complexLaplacian_eq_trace]
  rfl

end KEBall
