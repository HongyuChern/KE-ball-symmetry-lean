import KEBall.ComplexFlux
import KEBall.LogDetConcavity

/-! The actual logarithmic chain rule, including its second Wirtinger derivative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter Set
open scoped ContDiff BigOperators Topology
namespace KEBall
open KEBallProbe
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem dirichlet_rd_real_cast {f : V → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (a : V) :
    rd a (fun y => (f y : ℂ)) x=(fderiv ℝ f x a : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  change HasFDerivAt (fun y => (f y : ℂ)) _ x at h
  rw [rd,h.fderiv]
  rfl

theorem dirichlet_dz_log_real {f : V → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hf0 : f x≠0) (a b : V) :
    dz a b (fun y => (Real.log (f y) : ℂ)) x=
      ((f x : ℂ)⁻¹)*dz a b (fun y => (f y : ℂ)) x := by
  have hRd (v : V) : rd v (fun y => (Real.log (f y) : ℂ)) x=
      (f x : ℂ)⁻¹*rd v (fun y => (f y : ℂ)) x := by
    rw [dirichlet_rd_real_cast (hf.log hf0),dirichlet_rd_real_cast hf,
      (hf.hasFDerivAt.log hf0).fderiv]
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
  simp only [dz,hRd]
  ring

theorem dirichlet_dz_inv {f : V → ℂ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hf0 : f x≠0) (a b : V) :
    dz a b (fun y => (f y)⁻¹) x=-(f x)⁻¹^2*dz a b f x := by
  have h := (hasFDerivAt_inv' (𝕜 := ℝ) hf0).comp x hf.hasFDerivAt
  change HasFDerivAt (fun y => (f y)⁻¹) _ x at h
  have hRd (v : V) : rd v (fun y => (f y)⁻¹) x=-(f x)⁻¹^2*rd v f x := by
    rw [rd,h.fderiv]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply,rd]
    ring
  simp only [dz,hRd]
  ring

theorem dirichlet_dz_dz_log_real {f : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ ∞ f x) (hf0 : f x≠0) (a b c d : V) :
    dz a b (dz c d (fun y => (Real.log (f y) : ℂ))) x=
      ((f x : ℂ)⁻¹)*dz a b (dz c d (fun y => (f y : ℂ))) x-
        ((f x : ℂ)⁻¹)^2*dz a b (fun y => (f y : ℂ)) x*
          dz c d (fun y => (f y : ℂ)) x := by
  have hc : ContDiffAt ℝ ∞ (fun y => (f y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hc0 : (f x : ℂ)≠0 := by exact_mod_cast hf0
  have hNear : dz c d (fun y => (Real.log (f y) : ℂ))=ᶠ[𝓝 x]
      (fun y => ((f y : ℂ)⁻¹)*dz c d (fun z => (f z : ℂ)) y) := by
    have hDiff := (hf.of_le (m := 1) (by simp)).eventually (by simp)
    have hNe := hf.continuousAt.eventually_ne hf0
    filter_upwards [hDiff,hNe] with y hy hn
    exact dirichlet_dz_log_real (hy.differentiableAt one_ne_zero) hn c d
  rw [LogDetAux.dz_congr_of_eventuallyEq hNear,
    dz_mul_differentiableAt ((hc.differentiableAt (by simp)).fun_inv hc0)
      ((smoothAt_dz hc c d).differentiableAt (by simp)),
    dirichlet_dz_inv (hc.differentiableAt (by simp)) hc0]
  ring

theorem complexHessian_log_real {n : ℕ} {f : E n → ℝ} {x : E n}
    (hf : ContDiffAt ℝ ∞ f x) (hf0 : f x≠0) (i j : Fin n) :
    complexHessian (fun y => Real.log (f y)) x i j=
      ((f x : ℂ)⁻¹)*complexHessian f x i j-
        ((f x : ℂ)⁻¹)^2*partialZ i (fun y => (f y : ℂ)) x*
          partialBar j (fun y => (f y : ℂ)) x :=
  dirichlet_dz_dz_log_real hf hf0 _ _ _ _

end KEBall
