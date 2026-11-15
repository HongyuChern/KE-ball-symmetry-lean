import KEBall.DirichletHessianOscillationAlgebra

/-! A uniform geometric budget for the quarter-ball oscillation recurrence. -/

set_option autoImplicit false

open Filter

namespace KEBall

theorem exists_dirichlet_oscillation_geometric_budget
    {θ E M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hE : 0 ≤ E) (hM : 0 ≤ M) :
    ∃ τ D : ℝ, 0 < τ ∧ τ < 1 ∧ 0 ≤ D ∧
      ∀ o : ℕ → ℝ, o 0 ≤ M →
        (∀ k : ℕ, o (k + 1) ≤ θ * o k + E * (1 / 4 : ℝ) ^ k) →
        ∀ k : ℕ, o k ≤ D * τ ^ k := by
  let τ : ℝ := (max θ (1 / 4 : ℝ) + 1) / 2
  have hMax : max θ (1 / 4 : ℝ) < 1 := max_lt hθ1 (by norm_num)
  have hτMax : max θ (1 / 4 : ℝ) < τ := by dsimp only [τ]; linarith
  have hθτ : θ < τ := (le_max_left _ _).trans_lt hτMax
  have hστ : (1 / 4 : ℝ) < τ := (le_max_right _ _).trans_lt hτMax
  have hτ0 : 0 < τ := by linarith
  have hτ1 : τ < 1 := by dsimp only [τ]; linarith
  have hGap : 0 < τ - θ := sub_pos.mpr hθτ
  let D : ℝ := M + E / (τ - θ)
  have hMD : M ≤ D := le_add_of_nonneg_right (div_nonneg hE hGap.le)
  have hD : 0 ≤ D := hM.trans hMD
  have hBudget : θ * D + E ≤ D * τ := by
    have h : E / (τ - θ) ≤ D := le_add_of_nonneg_left hM
    have h' := (div_le_iff₀ hGap).mp h
    nlinarith
  refine ⟨τ, D, hτ0, hτ1, hD, ?_⟩
  intro o hInitial hStep
  exact dirichlet_oscillation_geometric_bound o hθ0 (by norm_num) hστ.le hE
    (hInitial.trans hMD) hBudget hStep

end KEBall
