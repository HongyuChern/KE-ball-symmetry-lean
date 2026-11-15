import KEBall.DirichletHessianDefectEstimate
import KEBall.DirichletBallAverages

/-! The actual Hessian Harnack estimate in normalized inner-ball measure. -/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped NNReal

noncomputable section

namespace KEBall

theorem exists_dirichlet_hessian_upper_defect_average {n : ℕ} (hn : 0 < n)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {c : ℝ} (hc : 0 < c) (hH : HasDirichletHessianWeakHarnack G c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E n, ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M R : ℝ) (x₀ : E n), 0 < R → closedBall x₀ R ⊆ unitBall n →
        (∀ᵐ x ∂(volume0 n).restrict (ball x₀ R), fderiv ℝ G x v v ≤ M) →
        (∫ x, M - fderiv ℝ G x v v ∂dirichletBallProbability x₀ (R / 4)) ≤
          C * (M - essSup (fun x : E n => fderiv ℝ G x v v)
            (dirichletBallProbability x₀ (R / 4)) + a * R ^ 2) := by
  obtain ⟨C, hC, hv⟩ := exists_dirichlet_hessian_upper_defect_estimate_on_ball hn hG hc hH
  refine ⟨dirichletQuarterAverageScale n * C,
    mul_nonneg (dirichletQuarterAverageScale_pos n).le hC, ?_⟩
  intro v
  obtain ⟨a, ha, hEst⟩ := hv v
  refine ⟨a, ha, ?_⟩
  intro M R x₀ hR hBall hM
  rw [essSup_dirichletBallProbability, integral_dirichletBallProbability_quarter _ hR]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hEst M R x₀ hR hBall hM)
    (dirichletQuarterAverageScale_pos n).le

end KEBall
