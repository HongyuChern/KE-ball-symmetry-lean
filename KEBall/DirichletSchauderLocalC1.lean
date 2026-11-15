import KEBall.DirichletSchauderLocalC2

/-!
# C1 Holder extension for the density

The density only needs a Holder first derivative.  In particular, a C2
density is enough here; no C3 regularity of a Gibbs density is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal Topology

namespace KEBall

theorem exists_dirichlet_C1_holder_jet_extension {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E n) (r R α Ku Kdu : ℝ≥0) (hrR : r < R) (hα : 0 < α) (hα1 : α ≤ 1)
    {u : E n → F} {Du : E n → E n →L[ℝ] F}
    (hu : ∀ x ∈ ball p R, HasFDerivAt u (Du x) x)
    (huH : HolderOnWith Ku α u (closedBall p R))
    (hDuH : HolderOnWith Kdu α Du (closedBall p R)) :
    ∃ (w : BoundedContinuousFunction (E n) F)
      (Dw : BoundedContinuousFunction (E n) (E n →L[ℝ] F)) (Kw KDw : ℝ≥0),
      EqOn (w : E n → F) u (closedBall p r) ∧
      (∀ x, HasFDerivAt (w : E n → F) (Dw x) x) ∧
      HolderWith Kw α (w : E n → F) ∧
      HolderWith KDw α (Dw : E n → E n →L[ℝ] F) := by
  obtain ⟨g, hgEq, hgHold⟩ := exists_dirichlet_bounded_holder_extension p R Ku α hα huH
  obtain ⟨Dg, hDgEq, hDgHold⟩ := exists_dirichlet_bounded_holder_extension p R Kdu α hα hDuH
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
  let w := cutoffValue χ g
  let Dw := cutoffJet1 χ Dχ g Dg
  have hwDer (x : E n) : HasFDerivAt (w : E n → F) (Dw x) x :=
    dirichlet_cutoffValue_hasFDerivAt_of_local χ Dχ g Dg hχ hgDer x
  have hleft : HolderWith (‖χ‖₊ * Kdu + ‖Dg‖₊ * Kχ) α
      (fun x => χ x • Dg x) :=
    holderWith_smul_of_norm_le hχH hDgHold
      (fun x => χ.norm_coe_le_norm x) (fun x => Dg.norm_coe_le_norm x)
  have hright : HolderWith (‖Dχ‖₊ * Ku + ‖g‖₊ * KDχ) α
      (fun x => (Dχ x).smulRight (g x)) :=
    holderWith_bilinear_of_opNorm_le_one (ContinuousLinearMap.smulRightL ℝ (E n) F)
      ContinuousLinearMap.norm_smulRightL_le hDχH hgHold
      (fun x => Dχ.norm_coe_le_norm x) (fun x => g.norm_coe_le_norm x)
  refine ⟨w, Dw, max (2 * ‖w‖₊) ‖Dw‖₊,
    (‖χ‖₊ * Kdu + ‖Dg‖₊ * Kχ) + (‖Dχ‖₊ * Ku + ‖g‖₊ * KDχ), ?_, hwDer, ?_, ?_⟩
  · intro x hx
    change χ x • g x = u x
    rw [hOne x (hKU hx), one_smul, hgEq (ball_subset_closedBall (hSub hx))]
  · exact holderWith_of_hasFDerivAt_of_norm_le hα.le hα1 hwDer
      (fun x => w.norm_coe_le_norm x) (fun x => Dw.norm_coe_le_norm x)
  · simpa only [Pi.add_apply] using! hleft.add hright

theorem exists_dirichlet_C1_holder_extension_of_C2 {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E n) (r R α : ℝ≥0) (hrR : r < R) (hα : 0 < α) (hα1 : α ≤ 1)
    {S : Set (E n)} (hS : IsOpen S) (hSub : closedBall p (R : ℝ) ⊆ S)
    {u : E n → F} (hu : ContDiffOn ℝ 2 u S) :
    ∃ (w : BoundedContinuousFunction (E n) F)
      (Dw : BoundedContinuousFunction (E n) (E n →L[ℝ] F)) (Kw KDw : ℝ≥0),
      EqOn (w : E n → F) u (closedBall p r) ∧
      (∀ x, HasFDerivAt (w : E n → F) (Dw x) x) ∧
      HolderWith Kw α (w : E n → F) ∧
      HolderWith KDw α (Dw : E n → E n →L[ℝ] F) := by
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) S := hu.fderiv_of_isOpen hS (by norm_num)
  obtain ⟨Ku, huH⟩ := exists_dirichlet_holderOnWith_of_C1_closedBall p R α hα1
    ((hu.of_le (by norm_num)).mono hSub)
  obtain ⟨Kdu, hDuH⟩ := exists_dirichlet_holderOnWith_of_C1_closedBall p R α hα1 (hDu.mono hSub)
  exact exists_dirichlet_C1_holder_jet_extension p r R α Ku Kdu hrR hα hα1
    (fun x hx => ((hu.contDiffAt (hS.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
      (by norm_num)).hasFDerivAt) huH hDuH

end KEBall
