import KEBall.DirichletUniformCompactLimits
import KEBall.DirichletClosedBallEllipticity
import KEBall.DirichletPositiveMatrix

/-! Elliptic bounds retained by uniform convergence of the actual real Hessians. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

theorem eventually_dirichlet_elliptic_bounds_of_uniform_hessian {n : ℕ} {ι : Type*}
    {l : Filter ι} {v : ι → E n → ℝ}
    (hv : ∀ j, SmoothNear (closedUnitBall n) (v j))
    {H : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hH : ContinuousOn H (closedUnitBall n))
    (hConv : TendstoUniformlyOn (fun j => realHessian (v j)) H l (closedUnitBall n))
    {a b D : ℝ}
    (hPos : ∀ x ∈ closedUnitBall n, (complexHessianOfRealBilinear (H x)).PosDef)
    (hDen : ∀ x ∈ closedUnitBall n,
      a < (complexHessianOfRealBilinear (H x)).det.re ∧
        (complexHessianOfRealBilinear (H x)).det.re < b)
    (hNorm : ∀ x ∈ closedUnitBall n, ‖H x‖ < D) :
    ∀ᶠ j in l, ∀ x ∈ closedUnitBall n,
      (complexHessian (v j) x).PosDef ∧
      a < (complexHessian (v j) x).det.re ∧ (complexHessian (v j) x).det.re < b ∧
      ‖realHessian (v j) x‖ < D := by
  let C := @complexHessianOfRealBilinear n
  let P (Q : E n →L[ℝ] E n →L[ℝ] ℝ) : Prop :=
    (C Q).IsHermitian → (C Q).PosDef ∧ a < (C Q).det.re ∧ (C Q).det.re < b ∧ ‖Q‖ < D
  let O := interior {Q | P Q}
  have hC : Continuous C := contDiff_dirichlet_complexHessianOfRealBilinear.continuous
  have hDet : Continuous (fun Q => (C Q).det.re) :=
    (Complex.continuous_re.comp continuous_id.matrix_det).comp hC
  have hMaps : MapsTo H (closedUnitBall n) O := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    obtain ⟨V, hV, hxV, hVP⟩ := exists_isOpen_hermitian_posDef_nhds (hPos x hx)
    have hNear : ∀ᶠ Q in 𝓝 (H x), C Q ∈ V := hC.continuousAt (hV.mem_nhds hxV)
    have hLow := hDet.continuousAt.eventually_const_lt (hDen x hx).1
    have hHigh := hDet.continuousAt.eventually_lt_const (hDen x hx).2
    have hSmall := continuous_norm.continuousAt.eventually_lt_const (hNorm x hx)
    filter_upwards [hNear, hLow, hHigh, hSmall] with Q hQV hQL hQH hQN
    exact fun hHerm => ⟨hVP _ hQV hHerm, hQL, hQH, hQN⟩
  have hEv := dirichlet_eventually_mem_open_of_uniform_limit
    (K := closedUnitBall n) (isCompact_closedBall (0 : E n) 1) hH hConv isOpen_interior hMaps
  filter_upwards [hEv] with j hj x hx
  have hu := (hv j).contDiffAt hx
  have hEq : C (realHessian (v j) x) = complexHessian (v j) x :=
    complexHessianOfRealBilinear_eq (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hHerm : (C (realHessian (v j) x)).IsHermitian := by
    rw [hEq]
    exact MoserTrudinger.complexHessian_isHermitian_of_smooth hu
  have h : P (realHessian (v j) x) := interior_subset (hj hx)
  simpa only [hEq] using h hHerm

end KEBall
