import KEBall.DirichletBoundaryOscillationStep
import KEBall.DirichletBoundaryPowerDecay

/-! Uniform boundary power decay for the actual smooth cofactor equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_uniform_dirichlet_boundary_quotient_power_decay {n : ℕ} (hn : 2 ≤ n)
    {c K S B : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hS : 0 ≤ S) (hB : 0 ≤ B) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
        (∀ x ∈ unitBall n, ∀ v : E n,
          c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (q : E n → ℝ), SmoothNear (closedUnitBall n) q →
        (∀ x ∈ unitSphere n, q x = 0) →
        (∀ x ∈ unitBall n, |q x / dirichletBoundaryDistanceProxy x| ≤ B) →
        (∀ x ∈ unitBall n,
          |dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x)| ≤ S) →
        ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
          ∀ r : ℝ, 0 < r → r ≤ R₀ →
            dirichletBoundaryOscillation (fun x => q x / dirichletBoundaryDistanceProxy x) p r ≤
              (D * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  obtain ⟨θ, C, hθ0, hθ1, hC, hStep⟩ :=
    exists_uniform_dirichlet_boundary_quotient_oscillation_step hn hc hK hS hB
  obtain ⟨α, D, hα0, hα1, hD, hPower⟩ :=
    exists_dirichlet_boundary_power_decay_budget (n := n) hθ0 hθ1 hC hB
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro u hu huP hNorm hEll q hq hq0 hBound hSource
  exact hPower _ hBound (hStep u hu huP hNorm hEll q hq hq0 hBound hSource)

end KEBall
