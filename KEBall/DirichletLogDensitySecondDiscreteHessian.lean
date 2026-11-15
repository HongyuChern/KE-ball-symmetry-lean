import KEBall.DirichletLogDensityClosedBallHolder
import KEBall.DirichletSecondDiscreteHessianEstimate

/-!
# Uniform second discrete Hessian bounds for the actual log-density path limit

The same potential is the uniform path limit, the closed-ball C2 solution,
and the argument of every normalized unitary difference below.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_dirichlet_closedBall_limit_with_uniform_second_discrete_hessian
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
      ∀ S : E n →L[ℝ] E n, ∀ hS : star S = -S,
        (∀ x, S (J x) = J (S x)) →
        ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ s : ℝ, s ≠ 0 → |s| < δ →
          (∫ x in unitBall n, ∑ i, ∑ j,
            (dirichletWithinRealHessian
              (dirichletOrthogonalDifference (orthogonalFlow S hS s) s
                (dirichletOrthogonalDifference (orthogonalFlow S hS s) s w)) x
                (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨φ, w, G, L, α, hφ, hUw, hGrad, hwC2, hwSmooth, hDclosed, hD, hLip,
      hw0, hPos, hDet, hClosed, hRest⟩ :=
    exists_dirichlet_closedBall_C2_holder_interior_smooth_limit_of_logDensityPath
      hn hg ht hT hu hu0 huP hEq
  refine ⟨w, hUw, hwC2, hwSmooth, hw0, fun x hx => (hClosed x hx).1, hDet, ?_⟩
  intro S hS hJ
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀ * g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, ((contDiffOn_const.mul hgU).exp)⟩
  exact exists_dirichlet_unitary_second_difference_uniform_hessian_bound
    (by omega : 0 < n) hwC2 hwSmooth hw0 (fun x hx => (hClosed x hx).1) hf hDet S hS hJ

end KEBall
