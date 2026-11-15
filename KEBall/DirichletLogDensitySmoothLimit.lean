import KEBall.DirichletC2SolutionBoundarySmooth
import KEBall.DirichletAllMixedAngularHessianLp

/-! Smooth closed-ball limits for the actual log-density continuity path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology
namespace KEBall

theorem exists_dirichlet_closedBall_smooth_limit_of_logDensityPath
    {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ w : E n → ℝ,
      TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      ContDiffOn ℝ ∞ w (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) := by
  obtain ⟨w,hUw,hw,hwS,hw0,hP,hD,_⟩ :=
    exists_dirichlet_closedBall_limit_with_all_mixed_angular_hessian_finite_Lp
      hn hg ht hT hu hu0 huP hEq
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀*g x)) := by
    obtain ⟨U,hU,hKU,hgU⟩ := hg
    exact ⟨U,hU,hKU,(contDiffOn_const.mul hgU).exp⟩
  exact ⟨w,hUw,contDiffOn_closedUnitBall_of_C2_dirichlet_solution
    (by omega) hw hwS hw0 hP hf hD,hw0,hP,hD⟩

theorem exists_dirichlet_smoothNear_limit_of_logDensityPath
    {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ v : E n → ℝ,
      TendstoUniformlyOn u v atTop (closedUnitBall n) ∧
      SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).det.re = Real.exp (t₀ * g x)) := by
  obtain ⟨w,hUw,hw,hw0,hP,hD⟩ :=
    exists_dirichlet_closedBall_smooth_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  obtain ⟨v,hv,he⟩ := exists_smoothNear_closedUnitBall_of_contDiffOn hw
  have hH {x : E n} (hx : x ∈ unitBall n) :
      complexHessian v x=complexHessian w x := by
    apply complexHessian_congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact he (ball_subset_closedBall hy)
  have hWithin {x : E n} (hx : x ∈ unitBall n) :
      dirichletWithinComplexHessian w x=complexHessian w x := by
    exact dirichletWithinComplexHessian_eq_on_ball_of_C2 (hw.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hx
  refine ⟨v,?_,hv,fun x hx => (he (sphere_subset_closedBall hx)).trans (hw0 x hx),?_,?_⟩
  · exact hUw.congr_right (fun x hx => (he hx).symm)
  · intro x hx
    rw [hH hx,← hWithin hx]
    exact hP x (ball_subset_closedBall hx)
  · intro x hx
    rw [hH hx]
    exact hD x hx

end KEBall
