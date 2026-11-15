import KEBall.BoundaryGeometry
import KEBall.BoundarySchur

/-!
# The actual boundary Hessian as a scalar horizontal block

The matrix decomposition is derived entrywise from the proved sphere
Hessian, with no assumed unitary covariance or normal frame.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

theorem sphere_realHessian_decomposition {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) (v w : E n) :
    realHessian u x v w =
      2 * boundarySlope u x * inner ℝ v w +
      2 * inner ℝ x v * fderiv ℝ (boundarySlope u) x w +
      2 * inner ℝ x w * fderiv ℝ (boundarySlope u) x v -
      (2 * fderiv ℝ (boundarySlope u) x x + 4 * boundarySlope u x) *
        inner ℝ x v * inner ℝ x w := by
  let a := inner ℝ x v
  let b := inner ℝ x w
  let vT := v - a • x
  let wT := w - b • x
  have hvT : inner ℝ x vT = 0 := by
    simp only [vT, inner_sub_right, real_inner_smul_right, sphere_inner_self hx,
      mul_one, a, sub_self]
  have hwT : inner ℝ x wT = 0 := by
    simp only [wT, inner_sub_right, real_inner_smul_right, sphere_inner_self hx,
      mul_one, b, sub_self]
  have hv : vT + a • x = v := by simp only [vT, sub_add_cancel]
  have hw : wT + b • x = w := by simp only [wT, sub_add_cancel]
  have hcomm : inner ℝ v x = inner ℝ x v := real_inner_comm _ _
  have hinner : inner ℝ vT wT = inner ℝ v w - a * b := by
    simp only [vT, wT, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, sphere_inner_self hx, hcomm]
    dsimp [a, b]
    ring
  have hxx : realHessian u x x x =
      2 * fderiv ℝ (boundarySlope u) x x - 2 * boundarySlope u x := by
    have ht := fderiv_boundarySlope (hu.contDiffAt (Metric.sphere_subset_closedBall hx)) x
    dsimp [boundarySlope] at ht ⊢
    linarith
  calc
    realHessian u x v w = realHessian u x (vT + a • x) (wT + b • x) := by rw [hv, hw]
    _ = realHessian u x vT wT + b * realHessian u x vT x +
        a * realHessian u x x wT + a * b * realHessian u x x x := by
      simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      rw [sphere_tangent_hessian hu hzero hx hvT hwT,
        sphere_mixed_hessian hu hzero hx hvT,
        realHessian_symm (hu.contDiffAt (Metric.sphere_subset_closedBall hx)) x wT,
        sphere_mixed_hessian hu hzero hx hwT, hinner, hxx]
      simp only [vT, wT, map_sub, map_smul, smul_eq_mul, a, b]
      ring

noncomputable def boundaryNormalComplex {n : ℕ} (x : E n) : Fin n → ℂ :=
  star (complexCoord x)

noncomputable def boundaryMixedComplex {n : ℕ} (u : E n → ℝ) (x : E n) : Fin n → ℂ :=
  (2 : ℂ)⁻¹ • star (complexCoord (horizontalGradient (boundarySlope u) x))

noncomputable def boundaryNormalEntry {n : ℕ} (u : E n → ℝ) (x : E n) : ℂ :=
  (fderiv ℝ (boundarySlope u) x x / 2 : ℝ)

theorem sphere_complexHessian_block {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) :
    complexHessian u x =
      borderedScalarMatrix (boundarySlope u x : ℂ) (boundaryNormalEntry u x)
        (boundaryNormalComplex x) (star (boundaryNormalComplex x))
        (boundaryMixedComplex u x) (star (boundaryMixedComplex u x)) := by
  ext i j
  rw [complexHessian_real_entry (hu.contDiffAt (Metric.sphere_subset_closedBall hx))]
  simp only [sphere_realHessian_decomposition hu hzero hx]
  simp only [borderedScalarMatrix, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, boundaryNormalComplex, boundaryMixedComplex, boundaryNormalEntry,
    Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_star, star_mul,
    horizontalGradient, _root_.sub_apply, _root_.smul_apply, inner_euclideanGradient,
    complexCoord, euclideanGradient_realIndex, euclideanGradient_imagIndex,
    J_realIndex, J_imagIndex]
  by_cases hij : i = j
  · subst j
    apply Complex.ext <;>
      simp [realDirection, imagDirection, EuclideanSpace.inner_single_right,
        EuclideanSpace.inner_single_left, Pi.single_apply, Complex.mul_re, Complex.mul_im,
        euclideanGradient_realIndex, euclideanGradient_imagIndex] <;> ring
  · apply Complex.ext <;>
      simp [realDirection, imagDirection, EuclideanSpace.inner_single_right,
        EuclideanSpace.inner_single_left, Pi.single_apply, hij, Ne.symm hij,
        Complex.mul_re, Complex.mul_im, euclideanGradient_realIndex,
        euclideanGradient_imagIndex] <;> ring

#print axioms sphere_realHessian_decomposition
#print axioms sphere_complexHessian_block

end KEBall
