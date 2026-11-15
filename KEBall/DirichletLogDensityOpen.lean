import KEBall.DirichletLogDensityStart
import KEBall.DirichletLogDensityPath
import KEBall.DirichletClosedBallExtension
import KEBall.MoserTrudingerSmoothGibbsExtension

/-! Neighborhood solvability in the extension-invariant smooth Dirichlet class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology
namespace KEBall

theorem exists_smoothNear_dirichlet_of_contDiffOn {n : ℕ} {u f : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x=0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).det.re=f x) := by
  obtain ⟨v,hv,he⟩ := exists_smoothNear_closedUnitBall_of_contDiffOn hu
  have hH {x : E n} (hx : x ∈ unitBall n) : complexHessian v x=complexHessian u x := by
    apply complexHessian_congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact he (ball_subset_closedBall hy)
  exact ⟨v,hv,fun x hx => (he (sphere_subset_closedBall hx)).trans (hu0 x hx),
    fun x hx => (hH hx) ▸ huP x hx,fun x hx => by rw [hH hx]; exact hEq x hx⟩

theorem eventually_exists_smoothNear_dirichlet_logDensity {n : ℕ}
    (hn : 0<n) {g : E n → ℝ} (hg : ContDiff ℝ ∞ g)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=Real.exp (t*g x)) :
    ∀ᶠ s in 𝓝 t, ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x=0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).det.re=Real.exp (s*g x)) := by
  have hgN : SmoothNear (closedUnitBall n) g := ⟨univ,isOpen_univ,subset_univ _,hg.contDiffOn⟩
  obtain ⟨a,b,K,M,ha,hb,hK,hM,hBounds⟩ := exists_logDensityPath_bounds hn hgN
  obtain ⟨l,L,hl,hL,hEll⟩ := exists_uniform_ellipticity_of_dirichlet_density_bounds hn ha hb hK hM
  obtain ⟨w,hw,he⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hu
  have hwN : SmoothNear (closedUnitBall n) w := ⟨univ,isOpen_univ,subset_univ _,hw.contDiffOn⟩
  have hw0 : ∀ x ∈ unitSphere n, w x=0 := fun x hx =>
    (he x (sphere_subset_closedBall hx)).self_of_nhds.trans (hu0 x hx)
  have hH {x : E n} (hx : x ∈ unitBall n) : complexHessian w x=complexHessian u x :=
    complexHessian_congr_of_eventuallyEq (he x (ball_subset_closedBall hx))
  have hwP : ∀ x ∈ unitBall n, (complexHessian w x).PosDef := fun x hx => (hH hx) ▸ huP x hx
  have hwEq : ∀ x ∈ unitBall n, (complexHessian w x).det.re=Real.exp (t*g x) := by
    intro x hx
    rw [hH hx]
    exact hEq x hx
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t*g x)) :=
    ⟨univ,isOpen_univ,subset_univ _,(contDiff_const.mul hg).exp.contDiffOn⟩
  have hE := hEll hwN hf hw0 hwP hwEq
    (fun x hx => (hBounds t ht).1 x (ball_subset_closedBall hx))
    (fun x hx => (hBounds t ht).2.1 x (ball_subset_closedBall hx))
    (fun x hx => (hBounds t ht).2.2 x (ball_subset_closedBall hx))
  have hLocal := eventually_exists_posDef_dirichlet_logDensity_smooth hn hw hg t hw0 hwP
    (fun x hx => hwEq x hx) (pow_pos ha n) hl
    (fun x hx => by rw [hwEq x hx]; exact ((hBounds t ht).1 x (ball_subset_closedBall hx)).1)
    (fun x hx v => (hE x (ball_subset_closedBall hx) v).1)
  filter_upwards [hLocal] with s hs
  obtain ⟨v,hv,hv0,hvP,hvEq⟩ := hs
  exact exists_smoothNear_dirichlet_of_contDiffOn hv hv0 hvP (fun x hx => hvEq hx)

theorem exists_smoothNear_dirichlet_logDensity_zero {n : ℕ}
    (hn : 0<n) {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x=0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).det.re=Real.exp (0*g x)) := by
  obtain ⟨v,hv,hv0,hvP,hvEq⟩ :=
    (eventually_exists_posDef_dirichlet_logDensity_smooth_near_zero hn hg).self_of_nhds
  exact exists_smoothNear_dirichlet_of_contDiffOn hv hv0 hvP (fun x hx => hvEq hx)

end KEBall
