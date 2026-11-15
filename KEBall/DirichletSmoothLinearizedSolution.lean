import KEBall.DirichletClassicalEquation
import KEBall.DirichletClosedBallExtension
import KEBall.RayODE

/-! Smooth neighborhood solutions of the linearized Monge–Ampère equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

/-- The closed-ball Dirichlet solution of the actual cofactor equation
can be represented by a smooth function on a neighborhood of the closed ball. -/
theorem exists_smoothNear_closedUnitBall_cofactor_solution {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G)
    (hRep : g =ᵐ[(volume0 n).restrict (unitBall n)] G) :
    ∃ (w : DirichletSobolev n) (v : E n → ℝ),
      IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      SmoothNear (closedUnitBall n) v ∧
      v =ᵐ[(volume0 n).restrict (unitBall n)] ((w : DirichletBallL2Pair n).fst : E n → ℝ) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      EqOn (MoserTrudinger.cofactorContraction u v) (fun x => -G x) (unitBall n) := by
  obtain ⟨w, v, hw, hv, hV, hBoundary, hEq⟩ :=
    exists_contDiffOn_closedUnitBall_cofactor_solution hn hu huP ha hl hDensity hElliptic g hG hRep
  obtain ⟨V, hVNear, hE⟩ := exists_smoothNear_closedUnitBall_of_contDiffOn hv
  refine ⟨w, V, hw, hVNear, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · filter_upwards [hV, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hBall
    exact (hE (ball_subset_closedBall hBall)).trans hx
  · exact (hE (sphere_subset_closedBall hx)).trans (hBoundary x hx)
  · have hNear : V =ᶠ[𝓝 x] v := Filter.Eventually.mono (isOpen_ball.mem_nhds hx)
      fun y hy => hE (ball_subset_closedBall hy)
    have hH := complexHessian_congr_of_eventuallyEq hNear
    unfold MoserTrudinger.cofactorContraction at *
    rw [hH]
    exact hEq hx

end KEBall
