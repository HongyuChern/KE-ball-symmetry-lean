import KEBall.DirichletLogTraceInequality
import KEBall.MoserTrudingerGibbsDensityBounds

/-! The Ricci-iteration cancellation retains the actual normalized Gibbs density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000
open Filter Set Matrix
open scoped ContDiff BigOperators ComplexOrder Matrix Matrix.Norms.Elementwise Topology
namespace KEBall.MoserTrudinger

theorem complexHessian_log_gibbsDensity {n : ℕ} (hn : 0<n) (γ : ℝ)
    {q : E n → ℝ} (hq : ContDiff ℝ ∞ q) (x : E n) :
    complexHessian (fun y => Real.log (gibbsDensity γ q y)) x=
      ((-γ : ℝ) : ℂ) • complexHessian q x := by
  have he : (fun y => Real.log (gibbsDensity γ q y))=
      (fun y => (-γ)*q y-Real.log (normalizingIntegral γ q)) :=
    funext fun y => log_gibbsDensity_eq hn γ hq.continuous.continuousOn y
  rw [he,complexHessian_sub_at (contDiffAt_const.mul hq.contDiffAt) contDiffAt_const,
    complexHessian_const_mul_at hq.contDiffAt,complexHessian_const,sub_zero]

theorem complexLaplacian_log_trace_gibbs_nonneg {n : ℕ} (hn : 0<n)
    {γ : ℝ} (hγ : 0≤γ) {u q : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (huP : ∀ y∈unitBall n, (complexHessian u y).PosDef)
    (hqP : ∀ y∈unitBall n, (complexHessian q y).PosSemidef)
    (hEq : ∀ y∈unitBall n, (complexHessian u y).det.re=gibbsDensity γ q y)
    {x : E n} (hx : x∈unitBall n) :
    0≤complexLaplacian u (fun y => Real.log (complexHessian u y).trace.re+γ*q y) x := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hBase := complexLaplacian_log_trace_complexHessian_ge hn hu Metric.isOpen_ball huP hx
  have he : (fun y => Real.log (complexHessian u y).det.re)=ᶠ[𝓝 x]
      (fun y => Real.log (gibbsDensity γ q y)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    rw [hEq y hy]
  rw [complexHessian_congr_of_eventuallyEq he,complexHessian_log_gibbsDensity hn γ hq,
    Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hBase
  have hRatio := dirichlet_complexHessian_trace_ratio_le hn u q x (huP x hx) (hqP x hx)
  have hMul := mul_le_mul_of_nonpos_left hRatio (neg_nonpos.mpr hγ)
  have hBound : (-γ)*complexLaplacian u q x≤
      complexLaplacian u (fun y => Real.log (complexHessian u y).trace.re) x := by
    apply hMul.trans
    simpa only [mul_div_assoc] using hBase
  have hT := (contDiff_complexHessian_trace_real hu).contDiffAt (x := x)
  have hLog := hT.log (ne_of_gt (dirichlet_posDef_trace_re_pos (huP x hx)))
  have hFun : (fun y => Real.log (complexHessian u y).trace.re+γ*q y)=
      (fun y => Real.log (complexHessian u y).trace.re-(-γ)*q y) := by
    funext y
    ring
  rw [hFun,complexLaplacian_sub_at u hLog (contDiffAt_const.mul hq.contDiffAt),
    complexLaplacian_const_mul_at u hq.contDiffAt]
  linarith only [hBound]

end KEBall.MoserTrudinger
