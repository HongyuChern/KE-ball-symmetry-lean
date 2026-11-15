import KEBall.DirichletHolderExtension
import KEBall.DirichletCutoffLocalJets
import DifferentialGeometry.Analysis.Schauder.Cutoff.Elliptic.BallHessian

/-!
# Actual global C2 Holder jets agreeing with local jets on a smaller ball

The three raw Holder extensions need not be derivatives of one another
outside the original ball.  A cutoff supported in the open ball restores
the derivative relations globally.  This distinction is essential for the
hypotheses of the imported whole-space Schauder estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal Topology

namespace KEBall

theorem exists_dirichlet_C2_holder_jet_extension {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E n) (r R α Ku Kdu KH : ℝ≥0) (hrR : r < R) (hα : 0 < α) (hα1 : α ≤ 1)
    {u : E n → F} {Du : E n → E n →L[ℝ] F}
    {Hu : E n → E n →L[ℝ] E n →L[ℝ] F}
    (hu : ∀ x ∈ ball p R, HasFDerivAt u (Du x) x)
    (hDu : ∀ x ∈ ball p R, HasFDerivAt Du (Hu x) x)
    (huH : HolderOnWith Ku α u (closedBall p R))
    (hDuH : HolderOnWith Kdu α Du (closedBall p R))
    (hHH : HolderOnWith KH α Hu (closedBall p R)) :
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
  obtain ⟨g, hgEq, hgHold⟩ := exists_dirichlet_bounded_holder_extension p R Ku α hα huH
  obtain ⟨Dg, hDgEq, hDgHold⟩ := exists_dirichlet_bounded_holder_extension p R Kdu α hα hDuH
  obtain ⟨Hg, hHgEq, hHgHold⟩ := exists_dirichlet_bounded_holder_extension p R KH α hα hHH
  have hSub : closedBall p (r : ℝ) ⊆ ball p R := closedBall_subset_ball (by exact_mod_cast hrR)
  obtain ⟨U, χ, Dχ, Hχ, Kχ, KDχ, KHχ, Klap, hU, hKU, hOne, hSupp, hRange,
      hχ, hDχ, hχH, hDχH, hHχH, _⟩ :=
    exists_schauder_cutoff_with_hessian (isCompact_closedBall p (r : ℝ))
      isOpen_ball hSub hα.le hα1
  have hgDer (x : E n) (hx : x ∈ tsupport (χ : E n → ℝ)) :
      HasFDerivAt (g : E n → F) (Dg x) x := by
    have hxB := hSupp hx
    rw [hDgEq (ball_subset_closedBall hxB)]
    apply (hu x hxB).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hxB] with y hy
    exact hgEq (ball_subset_closedBall hy)
  have hDgDer (x : E n) (hx : x ∈ tsupport (χ : E n → ℝ)) :
      HasFDerivAt (Dg : E n → E n →L[ℝ] F) (Hg x) x := by
    have hxB := hSupp hx
    rw [hHgEq (ball_subset_closedBall hxB)]
    apply (hDu x hxB).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hxB] with y hy
    exact hDgEq (ball_subset_closedBall hy)
  let w := cutoffValue χ g
  let Dw := cutoffJet1 χ Dχ g Dg
  let Hw := cutoffJet2 χ Dχ Hχ g Dg Hg
  have hwDer (x : E n) : HasFDerivAt (w : E n → F) (Dw x) x :=
    dirichlet_cutoffValue_hasFDerivAt_of_local χ Dχ g Dg hχ hgDer x
  have hDwDer (x : E n) : HasFDerivAt (Dw : E n → E n →L[ℝ] F) (Hw x) x :=
    dirichlet_cutoffJet1_hasFDerivAt_of_local χ Dχ Hχ g Dg Hg hχ hDχ hgDer hDgDer x
  let Kw : ℝ≥0 := max (2 * ‖w‖₊) ‖Dw‖₊
  let KDw : ℝ≥0 := max (2 * ‖Dw‖₊) ‖Hw‖₊
  have hwHold : HolderWith Kw α (w : E n → F) :=
    holderWith_of_hasFDerivAt_of_norm_le hα.le hα1 hwDer
      (fun x => w.norm_coe_le_norm x) (fun x => Dw.norm_coe_le_norm x)
  have hDwHold : HolderWith KDw α (Dw : E n → E n →L[ℝ] F) :=
    holderWith_of_hasFDerivAt_of_norm_le hα.le hα1 hDwDer
      (fun x => Dw.norm_coe_le_norm x) (fun x => Hw.norm_coe_le_norm x)
  let KHw := cutoffJet2HolderConst Kχ KDχ KHχ Ku Kdu KH
    ‖χ‖₊ ‖Dχ‖₊ ‖Hχ‖₊ ‖g‖₊ ‖Dg‖₊ ‖Hg‖₊
  have hHwHold : HolderWith KHw α (Hw : E n → E n →L[ℝ] E n →L[ℝ] F) :=
    cutoffJet2_holderWith χ Dχ Hχ g Dg Hg hχH hDχH hHχH hgHold hDgHold hHgHold
      (fun x => χ.norm_coe_le_norm x) (fun x => Dχ.norm_coe_le_norm x)
      (fun x => Hχ.norm_coe_le_norm x) (fun x => g.norm_coe_le_norm x)
      (fun x => Dg.norm_coe_le_norm x) (fun x => Hg.norm_coe_le_norm x)
  refine ⟨w, Dw, Hw, Kw, KDw, KHw, ?_, hwDer, hDwDer, hwHold, hDwHold, hHwHold⟩
  intro x hx
  change χ x • g x = u x
  rw [hOne x (hKU hx), one_smul, hgEq (ball_subset_closedBall (hSub hx))]

end KEBall
