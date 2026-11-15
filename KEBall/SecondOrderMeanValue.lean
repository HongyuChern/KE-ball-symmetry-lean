import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A uniform first-order remainder on a compact convex set
-/

set_option autoImplicit false

open Metric Set
open scoped ContDiff

namespace KEBall

/-- The first-order remainder on a convex set is bounded by the
second derivative bound times the squared displacement. -/
theorem norm_sub_linearization_le {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {K : Set X} (hK : Convex ℝ K) (hf : ∀ x ∈ K, DifferentiableAt ℝ f x)
    (hdf : ∀ x ∈ K, DifferentiableAt ℝ (fderiv ℝ f) x) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) {x y : X}
    (hx : x ∈ K) (hy : y ∈ K) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  let B := K ∩ closedBall x ‖y - x‖
  have hconvex : Convex ℝ B := hK.inter (convex_closedBall x _)
  have hxB : x ∈ B := ⟨hx, mem_closedBall_self (norm_nonneg _)⟩
  have hyB : y ∈ B := ⟨hy, by rw [mem_closedBall, dist_eq_norm]⟩
  let g (z : X) := f z - fderiv ℝ f x z
  have hg (z : X) (hz : z ∈ K) : HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f x) z :=
    (hf z hz).hasFDerivAt.sub (fderiv ℝ f x).hasFDerivAt
  have hgBound (z : X) (hz : z ∈ B) : ‖fderiv ℝ g z‖ ≤ C * ‖y - x‖ := by
    rw [(hg z hz.1).fderiv]
    have h := hK.norm_image_sub_le_of_norm_fderiv_le hdf hbound hx hz.1
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa only [mem_closedBall, dist_eq_norm] using hz.2
    exact h.trans (mul_le_mul_of_nonneg_left hz' hC)
  have h := hconvex.norm_image_sub_le_of_norm_fderiv_le (fun z hz => (hg z hz.1).differentiableAt)
    hgBound hxB hyB
  have he : g y - g x = f y - f x - fderiv ℝ f x (y - x) := by
    dsimp only [g]
    rw [map_sub]
    abel
  rw [he] at h
  simpa only [mul_assoc, pow_two] using h

theorem exists_uniform_linearization_bounds {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {K : Set X} (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 2 f x) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
      ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ L ∧
        ∀ y ∈ K, ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hdf (x : X) (hx : x ∈ K) : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    (hf x hx).fderiv_right (by norm_num)
  have hdfCont : ContinuousOn (fderiv ℝ f) K :=
    fun x hx => (hdf x hx).continuousAt.continuousWithinAt
  have hddfCont : ContinuousOn (fderiv ℝ (fderiv ℝ f)) K := by
    intro x hx
    have h : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ f)) x :=
      (hdf x hx).fderiv_right (by norm_num)
    exact h.continuousAt.continuousWithinAt
  obtain ⟨L, hL⟩ := (hK.image_of_continuousOn hdfCont.norm).bddAbove
  have hnorm : Continuous (fun g : X →L[ℝ] X →L[ℝ] Y => ‖g‖) := continuous_norm (E := X →L[ℝ] (X →L[ℝ] Y))
  have hddfNorm : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ f) x‖) K :=
    hnorm.comp_continuousOn hddfCont
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hddfNorm).bddAbove
  refine ⟨max 0 C, max 0 L, le_max_left _ _, le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
  · exact (hL ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  · intro y hy
    exact norm_sub_linearization_le hconvex
      (fun z hz => (hf z hz).differentiableAt (by norm_num))
      (fun z hz => (hdf z hz).differentiableAt (by norm_num))
      (le_max_left _ _) (fun z hz => (hC ⟨z, hz, rfl⟩).trans (le_max_right _ _)) hx hy

end KEBall
