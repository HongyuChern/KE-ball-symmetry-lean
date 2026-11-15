import KEBall.DirichletLogDensitySolvable

/-! Unconditional smooth positive-density Dirichlet solvability on the ball. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology
namespace KEBall

theorem exists_smoothNear_dirichlet_prescribed_density {n : ℕ} (hn : 2≤n)
    {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hPos : ∀ x ∈ closedUnitBall n, 0<f x) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x=0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).det.re=f x) := by
  let U : Set (E n) := {x | 0<f x}
  have hU : IsOpen U := isOpen_lt continuous_const hf.continuous
  have hKU : closedUnitBall n ⊆ U := hPos
  have hLog : SmoothNear (closedUnitBall n) (fun x => Real.log (f x)) :=
    ⟨U,hU,hKU,hf.contDiffOn.log (fun x hx => (show 0<f x from hx).ne')⟩
  obtain ⟨g,hg,he⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hLog
  obtain ⟨v,hv,hv0,hvP,hvEq⟩ := exists_smoothNear_dirichlet_logDensity hn hg
    (show (1 : ℝ)∈Icc (0 : ℝ) 1 by constructor <;> norm_num)
  refine ⟨v,hv,hv0,hvP,?_⟩
  intro x hx
  rw [hvEq x hx,one_mul,(he x (ball_subset_closedBall hx)).self_of_nhds]
  exact Real.exp_log (hPos x (ball_subset_closedBall hx))

end KEBall

namespace KEBall.MoserTrudinger

theorem smoothGibbsDirichletSolvable_unconditional {n : ℕ} (hn : 2≤n) (γ : ℝ) :
    SmoothGibbsDirichletSolvable n γ :=
  smoothGibbsDirichletSolvable_of_prescribed_density (by omega) γ
    (fun _ hf hPos => exists_smoothNear_dirichlet_prescribed_density hn hf hPos)

end KEBall.MoserTrudinger
