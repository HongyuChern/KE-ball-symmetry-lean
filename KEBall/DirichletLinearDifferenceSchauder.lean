import KEBall.DirichletLinearDifferenceSource
import KEBall.DirichletEllipticFamilySchauder

/-!
# A step-independent Schauder bound for linear difference quotients

The coefficient field is evaluated at the unshifted point.  Its derivative
and the derivative of the source control the inhomogeneous terms uniformly
over the admissible nonzero steps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal

namespace KEBall

theorem exists_dirichlet_uniform_linear_quotient_schauder_bound {n : ℕ} (hn : 0 < n)
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (DA : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] E n))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    (hA : ∀ x, HasFDerivAt (A : E n → E n →L[ℝ] E n) (DA x) x)
    {KDu KH KDf KA KDA α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDuH : HolderWith KDu α (Du : E n → E n →L[ℝ] ℝ))
    (hHH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDfH : HolderWith KDf α (Df : E n → E n →L[ℝ] ℝ))
    (hAH : HolderWith KA α (A : E n → E n →L[ℝ] E n))
    (hDAH : HolderWith KDA α (DA : E n → E n →L[ℝ] E n →L[ℝ] E n))
    (p v : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : (dirichletSchauderMatrix (A p)).PosDef)
    {l : ℝ} (hl : 0 < l) (hEll : ∀ z, l * ‖z‖ ^ 2 ≤ inner ℝ (A p z) z)
    (hEq : ∀ x ∈ closedBall p (2 * R), dirichletContractionCLM n (A x) (Hu x) = f x) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧ ∃ C : ℝ≥0,
      ∀ h : ℝ, h ≠ 0 → |h| * ‖v‖ ≤ R →
        eContDiffHolderGaugeOn 2 α (closedBall (0 : E n) (1 / 2))
          (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient u v h) p r 0 : E n → ℝ) ≤ C := by
  obtain ⟨B, K, hSourceBound⟩ := exists_dirichlet_uniform_linear_difference_source_bounds
    A DA Hu f Df hA hf hDAH hHH hDfH v
  let I := {h : ℝ // h ≠ 0 ∧ |h| * ‖v‖ ≤ R}
  let ui (i : I) := dirichletBoundedDifferenceQuotient u v i.val
  let dui (i : I) := dirichletBoundedDifferenceQuotient Du v i.val
  let Hui (i : I) := dirichletBoundedDifferenceQuotient Hu v i.val
  let fi (i : I) := dirichletLinearDifferenceSource A Hu f v i.val
  have hSource (i : I) (x : E n) (hx : x ∈ ball p R) :
      dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
        (A x) (Hui i x) = fi i x := by
    have hxR : x ∈ closedBall p (R : ℝ) := ball_subset_closedBall hx
    have hx2 : x ∈ closedBall p (2 * R) :=
      closedBall_subset_closedBall (by linarith [R.coe_nonneg] : (R : ℝ) ≤ 2 * R) hxR
    have hShift : x + i.val • v ∈ closedBall p (2 * R) :=
      dirichlet_add_mem_double_closedBall hxR
        (by simpa only [norm_smul, Real.norm_eq_abs] using i.property.2)
    exact dirichlet_linear_difference_equation A Hu f v x i.val (hEq x hx2) (hEq _ hShift)
  obtain ⟨r, hr, hrR, C, hBound⟩ :=
    exists_dirichlet_uniform_schauder_bound_for_elliptic_family hn ui dui Hui fi (fun _ => A)
      (fun i => hasFDerivAt_dirichletBoundedDifferenceQuotient hu v i.val)
      (fun i => hasFDerivAt_dirichletBoundedDifferenceQuotient hDu v i.val)
      p R KA ‖A‖₊ (KDu * ‖v‖₊) (KH * ‖v‖₊) K (‖Du‖₊ * ‖v‖₊) (‖Hu‖₊ * ‖v‖₊) B α
      hR hα hα1 (fun _ => hAH.holderOnWith _)
      (fun _ x _ => A.norm_coe_le_norm x) (fun _ => hPos) hl (fun _ => hEll) hSource
      (fun i => holderWith_dirichletDifferenceQuotient_of_holder_derivative hu hDuH v i.property.1)
      (fun i => holderWith_dirichletDifferenceQuotient_of_holder_derivative hDu hHH v i.property.1)
      (fun i => ⟨_, holderWith_dirichletDifferenceQuotient hHH v i.val⟩)
      (fun i => (hSourceBound i.val i.property.1).2)
      (fun i => nnnorm_dirichletBoundedDifferenceQuotient_le hu v i.property.1)
      (fun i => nnnorm_dirichletBoundedDifferenceQuotient_le hDu v i.property.1)
      (fun i => (hSourceBound i.val i.property.1).1)
  exact ⟨r, hr, hrR, C, fun h hh hStep => hBound ⟨h, hh, hStep⟩⟩

end KEBall
