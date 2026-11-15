import KEBall.DirichletHessianOscillationMonotone
import KEBall.DirichletOscillationPower

/-! All-radius power decay for the same actual directional Hessian family. -/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped BigOperators NNReal

noncomputable section

namespace KEBall

theorem exists_dirichlet_hessian_power_decay {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hStep : ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
      dirichletHessianOscillation G v x₀ (R / 4) ≤
        θ * dirichletHessianOscillation G v x₀ R + C * R) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ (x₀ : E n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 → closedBall x₀ R₀ ⊆ unitBall n →
        ∀ r : ℝ, 0 < r → r ≤ R₀ →
          dirichletHessianOscillation G v x₀ r ≤ (D * (4 / R₀ : ℝ) ^ α) * r ^ α := by
  obtain ⟨τ, D, hτ0, hτ1, hD, hGeo⟩ :=
    exists_dirichlet_hessian_geometric_decay hG v hθ0 hθ1 hC hStep
  obtain ⟨α, hα0, hα1, hτα⟩ := exists_dirichlet_decay_exponent hτ0 hτ1
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro x₀ R₀ hR₀ hR₀1 hBall r hr hrR
  apply dirichlet_power_bound_of_geometric
    (fun s => dirichletHessianOscillation G v x₀ s) hR₀ hD hτ0.le hα0.le hτα ?_
      (fun k => (hGeo x₀ R₀ hR₀ hR₀1 hBall k).2) hr hrR
  intro a b ha hab hb
  exact dirichletHessianOscillation_mono hG v ha hab
    ((ball_subset_ball hb).trans (ball_subset_closedBall.trans hBall))

end KEBall
