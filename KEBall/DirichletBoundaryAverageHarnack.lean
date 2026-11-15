import KEBall.DirichletPointwiseSourceHarnack
import KEBall.DirichletBallAverages

/-!
# Uniform average Harnack and the two-defect alternative

The probability normalization removes radius-dependent volumes.  The
constant is at least one, so division by it in the boundary iteration is
justified.  The two-defect alternative chooses one function for the whole
inner ball, rather than choosing a different one at each point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_uniform_smooth_cofactor_source_average_harnack {n : ℕ} (hn : 2 ≤ n)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
      (∀ x ∈ unitBall n, ∀ v : E n,
        c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (q : E n → ℝ), SmoothNear (closedUnitBall n) q → ∀ S : ℝ, 0 ≤ S →
        (∀ x ∈ unitBall n,
          dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x) ≤ S) →
        ∀ (x₀ : E n) (R : ℝ), 0 < R → closedBall x₀ R ⊆ unitBall n →
          (∀ x ∈ ball x₀ R, 0 ≤ q x) → ∀ y ∈ ball x₀ (R / 4),
            (∫ x, q x ∂dirichletBallProbability x₀ (R / 4)) ≤
              C * (q y + S / (4 * n * c) * R ^ 2) := by
  obtain ⟨H, hH, hEst⟩ := exists_uniform_smooth_cofactor_source_harnack hn hc hK
  let C : ℝ := dirichletQuarterAverageScale n * H + 1
  have hC : 1 ≤ C := by
    have := mul_nonneg (dirichletQuarterAverageScale_pos n).le hH
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro u hu huP hNorm hEll q hq S hS hL x₀ R hR hBall hPos y hy
  have h := mul_le_mul_of_nonneg_left
    (hEst u hu huP hNorm hEll q hq S hS hL x₀ R hR hBall hPos y hy)
    (dirichletQuarterAverageScale_pos n).le
  rw [← integral_dirichletBallProbability_quarter x₀ hR q] at h
  have hRight : 0 ≤ q y + S / (4 * n * c) * R ^ 2 := by
    apply add_nonneg (hPos y (ball_subset_ball (by linarith) hy))
    positivity
  calc
    _ ≤ dirichletQuarterAverageScale n * (H * (q y + S / (4 * n * c) * R ^ 2)) := h
    _ ≤ C * (q y + S / (4 * n * c) * R ^ 2) := by
      dsimp [C]
      nlinarith only [hRight]

/-- A single side has a uniform lower bound on all of `s`.
The error `a * R^2 / 4` corresponds to an outer Harnack radius `R/2`. -/
theorem dirichlet_two_defects_common_lower {n : ℕ}
    {μ : Measure (E n)} [IsProbabilityMeasure μ] {s : Set (E n)}
    {w₁ w₂ : E n → ℝ} (hI₁ : Integrable w₁ μ) (hI₂ : Integrable w₂ μ)
    {osc R C a : ℝ} (hC : 0 < C)
    (hSum : ∀ᵐ x ∂μ, osc * R / 4 ≤ w₁ x + w₂ x)
    (hPos₁ : ∀ y ∈ s, 0 ≤ w₁ y) (hPos₂ : ∀ y ∈ s, 0 ≤ w₂ y)
    (hH₁ : ∀ y ∈ s, (∫ x, w₁ x ∂μ) ≤ C * (w₁ y + a * R ^ 2 / 4))
    (hH₂ : ∀ y ∈ s, (∫ x, w₂ x ∂μ) ≤ C * (w₂ y + a * R ^ 2 / 4)) :
    (∀ y ∈ s, max 0 (osc * R / (8 * C) - a * R ^ 2 / 4) ≤ w₁ y) ∨
      (∀ y ∈ s, max 0 (osc * R / (8 * C) - a * R ^ 2 / 4) ≤ w₂ y) := by
  have hAv : osc * R / 4 ≤ (∫ x, w₁ x ∂μ) + ∫ x, w₂ x ∂μ := by
    have h := integral_mono_ae (integrable_const (osc * R / 4)) (hI₁.add hI₂) hSum
    change (∫ _ : E n, osc * R / 4 ∂μ) ≤ ∫ x, w₁ x + w₂ x ∂μ at h
    rw [integral_add hI₁ hI₂] at h
    simpa using h
  have hLower (w : E n → ℝ) (hPos : ∀ y ∈ s, 0 ≤ w y)
      (hH : ∀ y ∈ s, (∫ x, w x ∂μ) ≤ C * (w y + a * R ^ 2 / 4))
      (hAvw : osc * R / 8 ≤ ∫ x, w x ∂μ) :
      ∀ y ∈ s, max 0 (osc * R / (8 * C) - a * R ^ 2 / 4) ≤ w y := by
    intro y hy
    apply max_le (hPos y hy)
    have h := hAvw.trans (hH y hy)
    have hdiv : osc * R / (8 * C) ≤ w y + a * R ^ 2 / 4 := by
      rw [← div_div]
      exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm C] using h)
    linarith only [hdiv]
  by_cases h₁ : osc * R / 8 ≤ ∫ x, w₁ x ∂μ
  · exact Or.inl (hLower w₁ hPos₁ hH₁ h₁)
  · exact Or.inr (hLower w₂ hPos₂ hH₂ (by linarith only [hAv, not_le.mp h₁]))

end KEBall
