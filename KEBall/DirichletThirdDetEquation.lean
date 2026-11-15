import KEBall.DirichletNonlinearTangentEstimate
import KEBall.DirichletNormalRecovery

/-! The linearized equation for the directional derivative of the Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

open KEBallProbe

theorem cofactorTrace_realThirdDerivative_eq_fderiv {n : ℕ}
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (he : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) (v : E n) :
    ((complexHessian u x).adjugate * complexHessianOfRealBilinear (realThirdDerivative u x v)).trace.re =
      fderiv ℝ f x v := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hxU := hSub (ball_subset_closedBall hx)
  have hA : ContDiffOn ℝ ∞ (complexHessian u) U :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => complexHessian_contDiffOn hU huU i j
  have hD := ((hA.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt
  have hDet := (complex_det_differentiableAt (complexHessian u x)).hasFDerivAt.comp x hD
  have hF := Complex.reCLM.hasFDerivAt.comp x hDet
  have hf₀ : (fun y => (complexHessian u y).det.re) =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact he y hy
  have hGrad : fderiv ℝ (fun y => (complexHessian u y).det.re) x =
      (Complex.reCLM.comp ((fderiv ℝ Matrix.det (complexHessian u x)).comp
        (fderiv ℝ (complexHessian u) x))) := hF.fderiv
  have hDer : fderiv ℝ (complexHessian u) x v = complexHessianOfRealBilinear (realThirdDerivative u x v) := by
    ext i j
    let P : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) i)
    have hP : fderiv ℝ (fun y => complexHessian u y i j) x =
        P.comp (fderiv ℝ (complexHessian u) x) :=
      (P.hasFDerivAt.comp x hD).fderiv
    change P (fderiv ℝ (complexHessian u) x v) = _
    rw [← ContinuousLinearMap.comp_apply, ← hP, fderiv_complexHessian_entry hU huU hxU]
    rfl
  rw [← hf₀.fderiv_eq, hGrad, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hDer, fderiv_real_complex_det]
  rfl

/-- The normal rank-one coefficient in the linearized determinant has the
same lower ellipticity bound as the log-determinant, multiplied by the density. -/
theorem mul_norm_sq_le_quarter_hermitianRankOneDetSlope {n : ℕ}
    {u : E n → ℝ} {x v : E n} (hH : (complexHessian u x).PosDef) {d l L : ℝ}
    (hd : d ≤ (complexHessian u x).det.re) (hl : 0 < l) (hL : 0 < L)
    (hE : ∀ i, l ≤ hH.isHermitian.eigenvalues i ∧ hH.isHermitian.eigenvalues i ≤ L) :
    d * (L⁻¹ / 4) * ‖v‖ ^ 2 ≤
      hermitianRankOneDetSlope (complexHessian u x) (star (complexCoord v)) / 4 := by
  have h := (complexLaplacian_rankOne_bounds hH hl hE v).1
  have hN : 0 ≤ (L⁻¹ / 4) * ‖v‖ ^ 2 := by positivity
  have hD := posDef_det_re_pos hH
  calc
    _ = d * ((L⁻¹ / 4) * ‖v‖ ^ 2) := by ring
    _ ≤ (complexHessian u x).det.re * ((L⁻¹ / 4) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hd hN
    _ ≤ (complexHessian u x).det.re * complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x :=
      mul_le_mul_of_nonneg_left h hD.le
    _ = _ := by
      rw [hermitianRankOneDetSlope_eq hH, complexLaplacian_rankOne_quadratic]
      ring

end KEBall
