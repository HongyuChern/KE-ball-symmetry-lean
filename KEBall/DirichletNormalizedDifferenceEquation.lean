import KEBall.DirichletBoundedAffineScale
import KEBall.DirichletComplexHessianHolder

/-!
# The actual determinant difference equation on the normalized unit ball

The Hessian jet and the density quotient both acquire the factor r^2.
The averaged cofactor is evaluated at the two original physical points.
All ball inclusions and both endpoint equations are retained explicitly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal

namespace KEBall

theorem dirichlet_realHessian_eq_of_jets {n : ℕ}
    {u : E n → ℝ} {Du : E n → E n →L[ℝ] ℝ} {Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hu : ∀ x, HasFDerivAt u (Du x) x) (hDu : ∀ x, HasFDerivAt Du (Hu x) x)
    (x : E n) : realHessian u x = Hu x := by
  have hFirst : fderiv ℝ u = Du := funext fun y => (hu y).fderiv
  rw [realHessian, hFirst, (hDu x).fderiv]

theorem dirichlet_normalized_difference_quotient_equation {n : ℕ}
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (p v : E n) (R r : ℝ≥0) (hrR : r ≤ R) (h : ℝ) (hh : |h| * ‖v‖ ≤ R)
    (hEq : ∀ z ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) z).det.re = f z)
    (a : Fin (2 * n) → Fin (2 * n) → BoundedContinuousFunction (E n) ℝ)
    (ha : ∀ i j x, x ∈ closedBall (0 : E n) 1 → a i j x =
      dirichletSchauderMatrix
        (dirichletMeanCofactor (complexHessian (u : E n → ℝ) (p + (r : ℝ) • x))
          (complexHessian (u : E n → ℝ) (p + (r : ℝ) • x + h • v))) i j)
    (x : E n) (hx : x ∈ closedBall (0 : E n) 1) :
    variableMatrixLap a
      (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient Hu v h) p r 2) x =
      dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient f v h) p r 2 x := by
  let z := p + (r : ℝ) • x
  have hz : z ∈ closedBall p R := by
    rw [mem_closedBall, dist_eq_norm]
    simp only [z, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg r.coe_nonneg]
    exact (mul_le_of_le_one_right r.coe_nonneg (mem_closedBall_zero_iff.mp hx)).trans hrR
  have hSub : closedBall p (R : ℝ) ⊆ closedBall p (2 * R) :=
    closedBall_subset_closedBall (by nlinarith [R.coe_nonneg])
  have hzShift : z + h • v ∈ closedBall p (2 * R) :=
    dirichlet_add_mem_double_closedBall hz (by simpa only [norm_smul, Real.norm_eq_abs] using hh)
  have hC := contDiff_two_of_hasFDerivAt u Du Hu hu hDu
  have hQH : realHessian (dirichletDifferenceQuotient (u : E n → ℝ) v h) z =
      dirichletDifferenceQuotient (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ) v h z :=
    dirichlet_realHessian_eq_of_jets
      (fun y => hasFDerivAt_dirichletDifferenceQuotient v h y (hu y) (hu _))
      (fun y => hasFDerivAt_dirichletDifferenceQuotient v h y (hDu y) (hDu _)) z
  have hRaw := dirichlet_difference_quotient_det_linearization v z h
    (hC.contDiffAt (x := z)) (hC.contDiffAt (x := z + h • v))
  rw [hQH, hEq _ hzShift, hEq _ (hSub hz)] at hRaw
  rw [dirichlet_variableMatrixLap_eq_contraction a _ _ (fun i j => ha i j x hx),
    dirichletBoundedScaledJet_apply, dirichletBilinearContraction_smul_right,
    dirichletBoundedScaledJet_apply, smul_eq_mul]
  exact congrArg (fun t : ℝ => (r : ℝ) ^ 2 * t) hRaw

end KEBall
