import KEBall.DirichletAveragedCofactor
import KEBall.DirichletDifferenceQuotientHolder
import KEBall.DirichletCompactComparison
import KEBall.DirichletDirectionalLogDet

/-!
# The exact elliptic equation of a C2 determinant difference quotient

Only C2 regularity at the two translated points is used.  The coefficient
is the integral of the actual cofactors on their Hessian segment, and the
right-hand side is the corresponding quotient of the prescribed density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators

namespace KEBall

theorem dirichlet_realHessian_comp_add_right {n : ℕ} (u : E n → ℝ) (a x : E n) :
    realHessian (fun y => u (y + a)) x = realHessian u (x + a) := by
  have hD : fderiv ℝ (fun y => u (y + a)) = fun y => fderiv ℝ u (y + a) := by
    funext y
    exact fderiv_comp_add_right a
  rw [realHessian, hD, fderiv_comp_add_right]
  rfl

theorem contDiffAt_dirichletDifferenceQuotient {n : ℕ}
    {u : E n → ℝ} (v x : E n) (h : ℝ)
    (hx : ContDiffAt ℝ 2 u x) (hxh : ContDiffAt ℝ 2 u (x + h • v)) :
    ContDiffAt ℝ 2 (dirichletDifferenceQuotient u v h) x := by
  have ht : ContDiffAt ℝ 2 (fun y => u (y + h • v)) x :=
    hxh.comp x (contDiffAt_id.add contDiffAt_const)
  exact (ht.sub hx).const_smul h⁻¹

theorem realHessian_dirichletDifferenceQuotient {n : ℕ}
    {u : E n → ℝ} (v x : E n) (h : ℝ)
    (hx : ContDiffAt ℝ 2 u x) (hxh : ContDiffAt ℝ 2 u (x + h • v)) :
    realHessian (dirichletDifferenceQuotient u v h) x =
      h⁻¹ • (realHessian u (x + h • v) - realHessian u x) := by
  let q (y : E n) := u (y + h • v)
  have hq : ContDiffAt ℝ 2 q x := hxh.comp x (contDiffAt_id.add contDiffAt_const)
  change realHessian (h⁻¹ • (q - u)) x = _
  rw [dirichlet_realHessian_smul_C2 (u := q - u) (hq.sub hx),
    dirichlet_realHessian_sub_C2 (u := q) (v := u) hq hx]
  rw [show realHessian q x = realHessian u (x + h • v) from
    dirichlet_realHessian_comp_add_right u (h • v) x]

theorem dirichletBilinearContraction_smul_right {n : ℕ}
    (A : E n →L[ℝ] E n) (D : E n →L[ℝ] E n →L[ℝ] ℝ) (c : ℝ) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) A (c • D) =
      c * dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) A D := by
  simp only [dirichletBilinearContraction, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem dirichlet_difference_quotient_det_linearization {n : ℕ}
    {u : E n → ℝ} (v x : E n) (h : ℝ)
    (hx : ContDiffAt ℝ 2 u x) (hxh : ContDiffAt ℝ 2 u (x + h • v)) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletMeanCofactor (complexHessian u x) (complexHessian u (x + h • v)))
      (realHessian (dirichletDifferenceQuotient u v h) x) =
      h⁻¹ * ((complexHessian u (x + h • v)).det.re - (complexHessian u x).det.re) := by
  rw [realHessian_dirichletDifferenceQuotient v x h hx hxh,
    dirichletBilinearContraction_smul_right]
  congr 1
  apply dirichletBilinearContraction_meanCofactor
  rw [complexHessianOfRealBilinear_sub, complexHessianOfRealBilinear_eq hxh,
    complexHessianOfRealBilinear_eq hx]

theorem dirichlet_difference_quotient_determinant_equation {n : ℕ}
    {u f : E n → ℝ} {S : Set (E n)} (hS : IsOpen S)
    (hu : ContDiffOn ℝ 2 u S)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = f x)
    (v : E n) (h : ℝ) {x : E n} (hx : x ∈ S) (hxh : x + h • v ∈ S) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletMeanCofactor (complexHessian u x) (complexHessian u (x + h • v)))
      (realHessian (dirichletDifferenceQuotient u v h) x) =
      dirichletDifferenceQuotient f v h x := by
  rw [dirichlet_difference_quotient_det_linearization v x h
      (hu.contDiffAt (hS.mem_nhds hx)) (hu.contDiffAt (hS.mem_nhds hxh)),
    hEq _ hxh, hEq _ hx]
  rfl

end KEBall
