import KEBall.DirichletLogTraceIdentity
import KEBall.DirichletLogDetHessianTrace
import KEBall.DirichletWeightedTraceCauchy

/-! Aubin--Yau's logarithmic trace inequality for the actual complex Hessian. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000
open Set Matrix
open scoped ContDiff BigOperators ComplexOrder Matrix Matrix.Norms.Elementwise
namespace KEBall
open KEBallProbe

theorem contDiff_complexHessian_trace_real {n : ℕ} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun y => (complexHessian u y).trace.re) := by
  apply Complex.reCLM.contDiff.comp
  have hc : ContDiff ℝ ∞ (fun y => (u y : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  change ContDiff ℝ ∞ (fun y => ∑ i, complexHessian u y i i)
  exact ContDiff.sum fun i _ => smooth_dz (smooth_dz hc (realDirection i) (-imagDirection i))
    (realDirection i) (imagDirection i)

theorem complexLaplacian_log_trace_complexHessian_ge {n : ℕ} (hn : 0<n)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {U : Set (E n)} (hU : IsOpen U)
    (hP : ∀ y∈U, (complexHessian u y).PosDef) {x : E n} (hx : x∈U) :
    (complexHessian (fun y => Real.log (complexHessian u y).det.re) x).trace.re /
      (complexHessian u x).trace.re ≤
      complexLaplacian u (fun y => Real.log (complexHessian u y).trace.re) x := by
  letI : NeZero n := ⟨hn.ne'⟩
  let T : E n → ℝ := fun y => (complexHessian u y).trace.re
  let B : Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun k => Matrix.of fun i j => partialZ k (fun y => complexHessian u y i j) x
  let w : Fin n → ℂ := fun i => partialZ i (fun y => (T y : ℂ)) x
  let c := (star w ⬝ᵥ ((complexHessian u x)⁻¹ *ᵥ w)).re
  let Q := ∑ k, ((complexHessian u x)⁻¹*B k*(complexHessian u x)⁻¹*(B k)ᴴ).trace.re
  let D := (complexHessian (fun y => Real.log (complexHessian u y).det.re) x).trace.re
  let L := complexLaplacian u T x
  have hT : ContDiff ℝ ∞ T := contDiff_complexHessian_trace_real hu
  have hTp : 0<T x := dirichlet_posDef_trace_re_pos (hP x hx)
  have hW : w=(fun i => ∑ k, B k i k) := by
    have he : (fun y => (T y : ℂ))=(fun y => (complexHessian u y).trace) :=
      funext fun y => complexHessian_trace_real_cast hu.contDiffAt
    funext i
    dsimp only [w]
    rw [he]
    exact partialZ_trace_complexHessian hu.contDiffAt i
  have hC : c≤T x*Q := by
    have h := dirichlet_weighted_trace_cauchy (hP x hx) B
    dsimp only at h
    rw [← hW] at h
    exact h
  have hLT : L=D+Q :=
    complexLaplacian_trace_complexHessian_eq_logdet_trace_add hu hU hP hx
  have hLog : complexLaplacian u (fun y => Real.log (T y)) x=
      (T x)⁻¹*L-(T x)⁻¹^2*c :=
    complexLaplacian_log_real u hT.contDiffAt (ne_of_gt hTp)
  change D/T x≤complexLaplacian u (fun y => Real.log (T y)) x
  rw [hLog]
  have hScale := mul_le_mul_of_nonneg_left hC (sq_nonneg ((T x)⁻¹))
  have hInv : (T x)⁻¹^2*(T x*Q)=(T x)⁻¹*Q := by
    field_simp [ne_of_gt hTp]
  rw [hInv] at hScale
  calc
    D/T x = (T x)⁻¹*L-(T x)⁻¹*Q := by rw [hLT]; ring
    _ ≤ (T x)⁻¹*L-(T x)⁻¹^2*c := sub_le_sub_left hScale _

end KEBall
