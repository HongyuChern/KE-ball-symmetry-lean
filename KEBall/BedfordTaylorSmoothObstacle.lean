import KEBall.BedfordTaylorObstacleQuadraticSupport
import KEBall.SecondOrderMeanValue

/-!
# Uniform upper supports for smooth zero-extended potentials
-/

set_option autoImplicit false

open Metric Set
open scoped ContDiff

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)

/-- A C² nonpositive potential with zero boundary values has bounded
quadratic upper supports after extension by zero from a ball. -/
theorem exists_quadratic_upper_support_smooth_zeroExtension {n : ℕ} {R : ℝ}
    {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0)
    (huBoundary : ∀ x ∈ sphere 0 R, u x = 0) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
      let f := (ball (0 : ComplexModel n) R).indicator u
      ∀ x : ComplexModel n, ∃ p : ComplexModel n →L[ℝ] ℝ, ‖p‖ ≤ L ∧
        ∀ y, f y ≤ f x + p (y - x) + C * ‖y - x‖ ^ 2 := by
  let K := closedBall (0 : ComplexModel n) R
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨C, L, hC, hL, hbound⟩ := exists_uniform_linearization_bounds hK
    (convex_closedBall _ _) (fun _ _ => hu.contDiffAt)
  refine ⟨C, L, hC, hL, ?_⟩
  apply exists_quadratic_upper_support_zeroExtension hC hL hu₀ huBoundary
  intro x hx
  have hxK : x ∈ K := ball_subset_closedBall hx
  refine ⟨fderiv ℝ u x, (hbound x hxK).1, fun y hy => ?_⟩
  have h := (hbound x hxK).2 y hy
  rw [Real.norm_eq_abs] at h
  linarith [(le_abs_self _).trans h]

end KEBall.BedfordTaylor
