import KEBall.DirichletSchauderUniformEstimate
import KEBall.DirichletDifferenceQuotientLimit

/-!
# Reading the actual Hessian estimate from the imported gauge

The currying map between the iterated derivative and the bilinear Hessian
is an isometry.  No dimension factor or change of exponent is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal

namespace KEBall

theorem dirichlet_hessian_holderOnWith_of_schauder_gauge {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E n → F} {S : Set (E n)}
    {α C : ℝ≥0} (h : eContDiffHolderGaugeOn 2 α S u ≤ C) :
    HolderOnWith C α (fderiv ℝ (fderiv ℝ u)) S := by
  have hH : HolderOnWith C α (iteratedFDeriv ℝ 2 u) S :=
    HolderWith.restrict_iff.mp (topSpatialJet_holderWith_restrict h)
  intro x hx y hy
  rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
    ← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
    (hessianCurryEquiv (E n) F).isometry.edist_eq]
  exact hH x hx y hy

theorem dirichlet_hessian_norm_le_of_schauder_gauge {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E n → F} {S : Set (E n)}
    {α C : ℝ≥0} (h : eContDiffHolderGaugeOn 2 α S u ≤ C) {x : E n} (hx : x ∈ S) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C := by
  rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv, LinearIsometryEquiv.norm_map]
  exact spatialJet_norm_le h (by norm_num : 2 ≤ 2) hx

theorem dirichlet_actual_second_jet_holderOnWith_of_schauder_gauge {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E n → F} {Du : E n → E n →L[ℝ] F} {Hu : E n → E n →L[ℝ] E n →L[ℝ] F}
    (hu : ∀ x, HasFDerivAt u (Du x) x) (hDu : ∀ x, HasFDerivAt Du (Hu x) x)
    {S : Set (E n)} {α C : ℝ≥0} (h : eContDiffHolderGaugeOn 2 α S u ≤ C) :
    HolderOnWith C α Hu S := by
  have hFirst : fderiv ℝ u = Du := funext fun x => (hu x).fderiv
  have hSecond : fderiv ℝ Du = Hu := funext fun x => (hDu x).fderiv
  simpa only [hFirst, hSecond] using dirichlet_hessian_holderOnWith_of_schauder_gauge h

end KEBall
