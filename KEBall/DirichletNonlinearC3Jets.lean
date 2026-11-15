import KEBall.DirichletSchauderDifferenceLimit

/-!
# C3 at an interior point from the actual positive determinant equation

The radius in the quotient estimate may depend on the direction.  The
finite-dimensional pointwise CLM criterion removes any need to assume a
common neighborhood for infinitely many directions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

theorem dirichlet_C3At_of_positive_determinant_C2_holder_jets {n : ℕ} (hn : 0 < n)
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    {KDu KH KDf α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDuH : HolderWith KDu α (Du : E n → E n →L[ℝ] ℝ))
    (hHH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDfH : HolderWith KDf α (Df : E n → E n →L[ℝ] ℝ))
    (p : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).PosDef)
    (hEq : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).det.re = f x) :
    ContDiffAt ℝ 3 (u : E n → ℝ) p := by
  have hHC1 : ContDiffAt ℝ 1 (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ) p := by
    apply dirichlet_contDiffAt_clm_apply.mpr
    intro v
    obtain ⟨r, hr, _, C, hBound⟩ :=
      exists_dirichlet_uniform_normalized_quotient_schauder_bound hn u Du Hu f Df hu hDu hf
        hα hα1 hDuH hHH hDfH p v R hR hPos hEq
    obtain ⟨h, hh, hlim, hStep⟩ := exists_dirichlet_admissible_quotient_sequence v R hR
    exact dirichlet_C1_directional_hessian_of_normalized_schauder_bound u Du Hu hu hDu
      hα hHH p v r hr hh hlim (fun i => hBound (h i) (hh i) (hStep i))
  have hDC2 : ContDiffAt ℝ 2 (Du : E n → E n →L[ℝ] ℝ) p :=
    (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
      ⟨Hu, ⟨univ, Filter.univ_mem, fun x _ => hDu x⟩, hHC1⟩
  exact (contDiffAt_succ_iff_hasFDerivAt (n := 2)).mpr
    ⟨Du, ⟨univ, Filter.univ_mem, fun x _ => hu x⟩, hDC2⟩

end KEBall
