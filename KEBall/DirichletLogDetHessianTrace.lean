import KEBall.DirichletLogDetSecond
import KEBall.DirichletHessianWirtingerSymmetry

/-! The exact contracted log-determinant identity for the actual complex Hessian. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000
open Filter Set Matrix
open scoped ContDiff BigOperators ComplexOrder Matrix Matrix.Norms.Elementwise Topology
namespace KEBall
open KEBallProbe

theorem complexLaplacian_trace_complexHessian_eq_logdet_trace_add {n : ℕ}
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {U : Set (E n)} (hU : IsOpen U)
    (hP : ∀ y∈U, (complexHessian u y).PosDef) {x : E n} (hx : x∈U) :
    let B : Fin n → Matrix (Fin n) (Fin n) ℂ :=
      fun k => Matrix.of fun i j => partialZ k (fun y => complexHessian u y i j) x
    complexLaplacian u (fun y => (complexHessian u y).trace.re) x=
      (complexHessian (fun y => Real.log (complexHessian u y).det.re) x).trace.re+
        ∑ k, ((complexHessian u x)⁻¹*B k*(complexHessian u x)⁻¹*(B k)ᴴ).trace.re := by
  let M := (complexHessian u x)⁻¹
  let B : Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun k => Matrix.of fun i j => partialZ k (fun y => complexHessian u y i j) x
  let C : Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun k => Matrix.of fun i j => partialZ k (partialBar k (fun y => complexHessian u y i j)) x
  have hc : ContDiff ℝ ∞ (fun y => (u y : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have hG (i j : Fin n) : ContDiff ℝ ∞ (fun y => complexHessian u y i j) :=
    smooth_dz (smooth_dz hc (realDirection j) (-imagDirection j))
      (realDirection i) (imagDirection i)
  have hB (k : Fin n) :
      (Matrix.of fun i j => partialBar k (fun y => complexHessian u y i j) x)=(B k)ᴴ := by
    ext i j
    exact partialBar_complexHessian_eq_star_partialZ hu x i j k
  have hC : ∑ k, C k=complexHessian (fun y => (complexHessian u y).trace.re) x := by
    ext i j
    simp only [Matrix.sum_apply,C,Matrix.of_apply]
    exact (complexHessian_trace_commutation hu x i j).symm
  have heach (k : Fin n) :
      complexHessian (fun y => Real.log (complexHessian u y).det.re) x k k=
        (M*C k).trace-(M*B k*M*(B k)ᴴ).trace := by
    have h := dirichlet_dz_dz_logdet hU (fun i j => (hG i j).contDiffOn) hP hx
      (realDirection k) (imagDirection k) (realDirection k) (-imagDirection k)
    change complexHessian (fun y => Real.log (complexHessian u y).det.re) x k k=
      (M*C k).trace-(M*B k*M*
        (Matrix.of fun i j => partialBar k (fun y => complexHessian u y i j) x)).trace at h
    rw [hB] at h
    exact h
  have hTrace : (complexHessian (fun y => Real.log (complexHessian u y).det.re) x).trace=
      (M*complexHessian (fun y => (complexHessian u y).trace.re) x).trace-
        ∑ k, (M*B k*M*(B k)ᴴ).trace := by
    change (∑ k, complexHessian (fun y => Real.log (complexHessian u y).det.re) x k k)=_
    simp_rw [heach]
    rw [Finset.sum_sub_distrib,← Matrix.trace_sum,← Finset.mul_sum,hC]
  have hRe := congrArg Complex.re hTrace
  rw [Complex.sub_re,Complex.re_sum] at hRe
  change complexLaplacian u (fun y => (complexHessian u y).trace.re) x=_
  rw [complexLaplacian_eq_trace]
  change (M*complexHessian (fun y => (complexHessian u y).trace.re) x).trace.re=_
  linarith only [hRe]

end KEBall
