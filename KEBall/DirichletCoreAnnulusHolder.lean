import KEBall.DirichletCompactHolder
import KEBall.DirichletBoundaryInterpolation

/-! Gluing overlapping core and annular Holder estimates with the same exponent. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped NNReal

namespace KEBall

theorem hasDirichletHolderOn_closedBall_of_core_annulus {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {α : ℝ≥0}
    (hC : ContinuousOn f (closedUnitBall n))
    (hCore : HasDirichletHolderOn α f (closedBall (0 : E n) (3 / 4)))
    (hAnn : HasDirichletHolderOn α f (closedUnitBall n ∩ {x : E n | 1 / 2 ≤ ‖x‖})) :
    HasDirichletHolderOn α f (closedUnitBall n) := by
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hC
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBound (x : E n) (hx : x ∈ closedUnitBall n) : ‖f x‖ ≤ B :=
    (hB₀ x hx).trans (le_max_left _ _)
  obtain ⟨K, hK⟩ := hCore
  obtain ⟨L, hL⟩ := hAnn
  let C : ℝ := (K : ℝ) + (L : ℝ) + 2 * B / (1 / 4 : ℝ) ^ (α : ℝ)
  have hFarNonneg : 0 ≤ 2 * B / (1 / 4 : ℝ) ^ (α : ℝ) := by positivity
  have hCC : 0 ≤ C := by dsimp [C]; positivity
  have hKC : (K : ℝ) ≤ C := by dsimp [C]; linarith [L.coe_nonneg]
  have hLC : (L : ℝ) ≤ C := by dsimp [C]; linarith [K.coe_nonneg]
  have hFC : 2 * B / (1 / 4 : ℝ) ^ (α : ℝ) ≤ C := by
    dsimp [C]
    linarith [K.coe_nonneg, L.coe_nonneg]
  have hFar (x : E n) (hx : x ∈ closedUnitBall n) (y : E n) (hy : y ∈ closedUnitBall n)
      (hd : 1 / 4 ≤ dist x y) : ‖f x - f y‖ ≤ C * dist x y ^ (α : ℝ) := by
    have hp : (1 / 4 : ℝ) ^ (α : ℝ) ≤ dist x y ^ (α : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hd α.coe_nonneg
    calc
      _ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hBound x hx, hBound y hy])
      _ = (2 * B / (1 / 4 : ℝ) ^ (α : ℝ)) * (1 / 4 : ℝ) ^ (α : ℝ) := by
        field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4) (α : ℝ)).ne']
      _ ≤ (2 * B / (1 / 4 : ℝ) ^ (α : ℝ)) * dist x y ^ (α : ℝ) :=
        mul_le_mul_of_nonneg_left hp hFarNonneg
      _ ≤ C * dist x y ^ (α : ℝ) :=
        mul_le_mul_of_nonneg_right hFC (Real.rpow_nonneg dist_nonneg _)
  refine ⟨⟨C, hCC⟩, dirichlet_holderOnWith_of_norm_bound hCC α.coe_nonneg ?_⟩
  intro x hx y hy
  conv_rhs => rw [← dist_eq_norm]
  by_cases hxCore : ‖x‖ ≤ 3 / 4
  · by_cases hyCore : ‖y‖ ≤ 3 / 4
    · have h := hK.dist_le (mem_closedBall_zero_iff.mpr hxCore)
        (mem_closedBall_zero_iff.mpr hyCore)
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg dist_nonneg _))
    · by_cases hxAnn : 1 / 2 ≤ ‖x‖
      · have h := hL.dist_le ⟨hx, hxAnn⟩ ⟨hy, by change 1 / 2 ≤ ‖y‖; linarith⟩
        rw [dist_eq_norm] at h
        exact h.trans (mul_le_mul_of_nonneg_right hLC (Real.rpow_nonneg dist_nonneg _))
      · apply hFar x hx y hy
        have h := norm_sub_norm_le y x
        rw [← dist_eq_norm, dist_comm y x] at h
        linarith
  · by_cases hyAnn : 1 / 2 ≤ ‖y‖
    · have h := hL.dist_le ⟨hx, by change 1 / 2 ≤ ‖x‖; linarith⟩ ⟨hy, hyAnn⟩
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_right hLC (Real.rpow_nonneg dist_nonneg _))
    · apply hFar x hx y hy
      have h := norm_sub_norm_le x y
      rw [← dist_eq_norm] at h
      linarith

end KEBall
