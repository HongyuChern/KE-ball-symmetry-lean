import KEBall.BedfordTaylorObstacleMaximality
import Mathlib.Topology.Order.IntermediateValue

/-!
# Quadratic upper supports for zero-extended obstacles
-/

set_option autoImplicit false

open Metric Set TopologicalSpace

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ}

/-- Quadratic upper supports on a closed ball persist under zero extension
of a nonpositive potential that vanishes on the sphere. -/
theorem exists_quadratic_upper_support_zeroExtension {R C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    {u : ComplexModel n → ℝ}
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0)
    (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hu : ∀ x ∈ ball 0 R, ∃ p : ComplexModel n →L[ℝ] ℝ, ‖p‖ ≤ L ∧
      ∀ y ∈ closedBall 0 R, u y ≤ u x + p (y - x) + C * ‖y - x‖ ^ 2) :
    let f := (ball (0 : ComplexModel n) R).indicator u
    ∀ x : ComplexModel n, ∃ p : ComplexModel n →L[ℝ] ℝ, ‖p‖ ≤ L ∧
      ∀ y, f y ≤ f x + p (y - x) + C * ‖y - x‖ ^ 2 := by
  let f := (ball (0 : ComplexModel n) R).indicator u
  have hf₀ (y : ComplexModel n) : f y ≤ 0 := by
    by_cases hy : y ∈ ball (0 : ComplexModel n) R
    · simpa only [f, indicator_of_mem hy] using hu₀ y hy
    · simp only [f, indicator_of_notMem hy, le_refl]
  change ∀ x : ComplexModel n, ∃ p : ComplexModel n →L[ℝ] ℝ, ‖p‖ ≤ L ∧
    ∀ y, f y ≤ f x + p (y - x) + C * ‖y - x‖ ^ 2
  intro x
  by_cases hx : x ∈ ball (0 : ComplexModel n) R
  · obtain ⟨p, hp, hsupport⟩ := hu x hx
    refine ⟨p, hp, fun y => ?_⟩
    rw [show f x = u x from indicator_of_mem hx _]
    by_cases hy : y ∈ ball (0 : ComplexModel n) R
    · rw [show f y = u y from indicator_of_mem hy _]
      exact hsupport y (ball_subset_closedBall hy)
    · have hxr : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using hx
      have hyr : R ≤ ‖y‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hy
      let z (t : ℝ) := x + t • (y - x)
      have hcont : Continuous (fun t : ℝ => ‖z t‖) :=
        (continuous_const.add (continuous_id.smul continuous_const)).norm
      have hzero : ‖z 0‖ = ‖x‖ := by simp [z]
      have hone : ‖z 1‖ = ‖y‖ := by
        congr 1
        simp [z]
      obtain ⟨t, ht, htz⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
        hcont.continuousOn (show R ∈ Icc ‖z 0‖ ‖z 1‖ by rw [hzero, hone]; exact ⟨hxr.le, hyr⟩)
      change ‖z t‖ = R at htz
      have htpos : 0 < t := by
        by_contra! h
        have hte : t = 0 := ht.1.antisymm' h
        rw [hte, hzero] at htz
        exact hxr.ne htz
      have hz : z t ∈ sphere (0 : ComplexModel n) R := by
        simpa only [mem_sphere, dist_zero_right] using htz
      have hq := hsupport (z t) (sphere_subset_closedBall hz)
      rw [huBoundary (z t) hz, show z t - x = t • (y - x) by dsimp only [z]; abel,
        map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, smul_eq_mul] at hq
      have hCq : 0 ≤ C * ‖y - x‖ ^ 2 := mul_nonneg hC (sq_nonneg _)
      have htq := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right htpos.le ht.2) hCq
      have htx := mul_le_of_le_one_right (neg_nonneg.mpr (hu₀ x hx)) ht.2
      rw [show f y = 0 from indicator_of_notMem hy _]
      apply nonneg_of_mul_nonneg_right _ htpos
      nlinarith only [hq, htq, htx]
  · refine ⟨0, by simpa only [norm_zero] using hL, fun y => ?_⟩
    rw [show f x = 0 from indicator_of_notMem hx _, zero_apply, add_zero, zero_add]
    exact (hf₀ y).trans (mul_nonneg hC (sq_nonneg _))

/-- A quadratic upper support bounds centered differences by the squared
displacements and the norm of their sum. -/
theorem centered_difference_le_of_quadratic_support
    {f : ComplexModel n → ℝ} {C L a b : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    {x y z : ComplexModel n}
    (hf : ∃ p : ComplexModel n →L[ℝ] ℝ, ‖p‖ ≤ L ∧
      f y ≤ f x + p (y - x) + C * ‖y - x‖ ^ 2 ∧
      f z ≤ f x + p (z - x) + C * ‖z - x‖ ^ 2)
    (ha : ‖y - x‖ ^ 2 + ‖z - x‖ ^ 2 ≤ a)
    (hb : ‖(y - x) + (z - x)‖ ≤ b) :
    f y + f z - 2 * f x ≤ L * b + C * a := by
  obtain ⟨p, hp, hy, hz⟩ := hf
  have hlinear : p (y - x) + p (z - x) ≤ L * b := by
    rw [← map_add]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact (p.le_opNorm _).trans (mul_le_mul hp hb (norm_nonneg _) hL)
  have hq := mul_le_mul_of_nonneg_left ha hC
  linarith only [hy, hz, hlinear, hq]

/-- A quadratic upper support bounds centered differences along
holomorphic self-maps by their displacements and their combined drift. -/
theorem obstacleEnvelope_centered_difference_of_quadratic_support
    {Ω : Opens (ComplexModel n)} {u f : ComplexModel n → ℝ} {C L a b : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, u x ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, w x ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    (hf : ∀ x ∈ Ω, ∃ p : ComplexModel n →L[ℝ] ℝ, ‖p‖ ≤ L ∧
      ∀ y ∈ Ω, f y ≤ f x + p (y - x) + C * ‖y - x‖ ^ 2)
    {F G : ComplexModel n → ComplexModel n} (hF : DifferentiableOn ℂ F Ω)
    (hG : DifferentiableOn ℂ G Ω) (hFmap : MapsTo F Ω Ω) (hGmap : MapsTo G Ω Ω)
    (ha : ∀ x ∈ Ω, ‖F x - x‖ ^ 2 + ‖G x - x‖ ^ 2 ≤ a)
    (hb : ∀ x ∈ Ω, ‖(F x - x) + (G x - x)‖ ≤ b) :
    ∀ x ∈ Ω, u (F x) + u (G x) - 2 * u x ≤ L * b + C * a := by
  apply obstacleEnvelope_centered_difference hu huf hgreatest hF hG hFmap hGmap
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hf x hx
  exact centered_difference_le_of_quadratic_support hC hL
    ⟨p, hp, hpx (F x) (hFmap hx), hpx (G x) (hGmap hx)⟩ (ha x hx) (hb x hx)

end KEBall.BedfordTaylor
