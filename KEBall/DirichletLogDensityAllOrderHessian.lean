import KEBall.DirichletLogDensityClosedBallHolder
import KEBall.DirichletAllOrderHessianEstimate

/-! Every fixed-order discrete Hessian estimate holds for the same actual log-density path limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

theorem exists_dirichlet_closedBall_limit_with_all_order_discrete_hessian
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
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      ∀ S : E n →L[ℝ] E n, ∀ hS : star S = -S, ∀ k : ℕ,
        ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ s : ℝ, s ≠ 0 → |s| < δ →
          ∀ j ≤ k, (∫ x in unitBall n,
            ‖dirichletWithinRealHessian
              (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS s) s w j) x‖ ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨φ, w, G, L, α, hφ, hUw, hGrad, hwC2, hwSmooth, hDclosed, hD, hLip,
      hw0, hPos, hDet, hClosed, hRest⟩ :=
    exists_dirichlet_closedBall_C2_holder_interior_smooth_limit_of_logDensityPath
      hn hg ht hT hu hu0 huP hEq
  refine ⟨w, hUw, hwC2, hwSmooth, hw0, fun x hx => (hClosed x hx).1, hDet, ?_⟩
  intro S hS k
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀ * g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, ((contDiffOn_const.mul hgU).exp)⟩
  exact exists_dirichlet_all_order_uniform_hessian_bound
    (by omega : 0 < n) hwC2 hwSmooth hw0 (fun x hx => (hClosed x hx).1) hf hDet S hS k

end KEBall
