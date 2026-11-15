import KEBall.DirichletSchauderLocalExtension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Localizing an actual C2 function with Holder Hessian

Only the Hessian Holder estimate is required as additional regularity.
The value and first derivative bounds follow from C2 regularity on a
neighborhood of the compact ball and the ordinary mean-value theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped NNReal

namespace KEBall

theorem dirichlet_closedBall_edist_le {n : ℕ} {p x y : E n} {R : ℝ≥0}
    (hx : x ∈ closedBall p R) (hy : y ∈ closedBall p R) :
    edist x y ≤ (2 * R : ℝ≥0) := by
  rw [edist_dist]
  have hd : dist x y ≤ 2 * (R : ℝ) := by
    calc
      dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
      _ ≤ (R : ℝ) + R := add_le_add (mem_closedBall.mp hx)
        (by simpa only [dist_comm] using mem_closedBall.mp hy)
      _ = 2 * R := by ring
  calc
    ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal (2 * (R : ℝ)) := ENNReal.ofReal_le_ofReal hd
    _ = (2 * R : ℝ≥0) := by
      change ENNReal.ofReal ((2 * R : ℝ≥0) : ℝ) = _
      exact ENNReal.ofReal_coe_nnreal

theorem exists_dirichlet_holderOnWith_of_C1_closedBall {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E n → F} (p : E n) (R α : ℝ≥0) (hα1 : α ≤ 1)
    (hu : ContDiffOn ℝ 1 u (closedBall p R)) :
    ∃ K : ℝ≥0, HolderOnWith K α u (closedBall p R) := by
  obtain ⟨L, hL⟩ := hu.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall p (R : ℝ)) (isCompact_closedBall p (R : ℝ))
  exact ⟨_, hL.holderOnWith.of_le (fun _ hx _ hy => dirichlet_closedBall_edist_le hx hy) hα1⟩

theorem exists_dirichlet_actual_C2_holder_extension {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E n) (r R α KH : ℝ≥0) (hrR : r < R) (hα : 0 < α) (hα1 : α ≤ 1)
    {S : Set (E n)} (hS : IsOpen S) (hSub : closedBall p (R : ℝ) ⊆ S)
    {u : E n → F} (hu : ContDiffOn ℝ 2 u S)
    (hHH : HolderOnWith KH α (fderiv ℝ (fderiv ℝ u)) (closedBall p R)) :
    ∃ (w : BoundedContinuousFunction (E n) F)
      (Dw : BoundedContinuousFunction (E n) (E n →L[ℝ] F))
      (Hw : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] F))
      (Kw KDw KHw : ℝ≥0),
      EqOn (w : E n → F) u (closedBall p r) ∧
      (∀ x, HasFDerivAt (w : E n → F) (Dw x) x) ∧
      (∀ x, HasFDerivAt (Dw : E n → E n →L[ℝ] F) (Hw x) x) ∧
      HolderWith Kw α (w : E n → F) ∧
      HolderWith KDw α (Dw : E n → E n →L[ℝ] F) ∧
      HolderWith KHw α (Hw : E n → E n →L[ℝ] E n →L[ℝ] F) := by
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) S := hu.fderiv_of_isOpen hS (by norm_num)
  obtain ⟨Ku, huH⟩ := exists_dirichlet_holderOnWith_of_C1_closedBall p R α hα1
    ((hu.of_le (by norm_num)).mono hSub)
  obtain ⟨Kdu, hDuH⟩ := exists_dirichlet_holderOnWith_of_C1_closedBall p R α hα1 (hu1.mono hSub)
  apply exists_dirichlet_C2_holder_jet_extension p r R α Ku Kdu KH hrR hα hα1
    (u := u) (Du := fderiv ℝ u) (Hu := fderiv ℝ (fderiv ℝ u))
  · intro x hx
    exact ((hu.contDiffAt (hS.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
      (by norm_num)).hasFDerivAt
  · intro x hx
    exact ((hu1.contDiffAt (hS.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
      (by norm_num)).hasFDerivAt
  · exact huH
  · exact hDuH
  · exact hHH

end KEBall
