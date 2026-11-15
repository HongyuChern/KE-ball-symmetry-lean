import KEBall.RealHessian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Complex coordinates for the Euclidean ball

The interleaved real model and the complex Euclidean model carry the same
real metric and Lebesgue measure under the standard coordinate map.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace KEBall

private noncomputable def toComplexCoordinates (n : ℕ) (x : E n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (complexCoord x)

private noncomputable def fromComplexCoordinates (n : ℕ) (z : EuclideanSpace ℂ (Fin n)) : E n :=
  WithLp.toLp 2 (fun k =>
    let p := (interleavedEquiv n).symm k
    if p.2 = 0 then (z p.1).re else (z p.1).im)

@[simp] private theorem fromComplexCoordinates_real (n : ℕ) (z : EuclideanSpace ℂ (Fin n))
    (j : Fin n) : fromComplexCoordinates n z (realIndex j) = (z j).re := by
  have hj : (interleavedEquiv n).symm (realIndex j) = (j, 0) :=
    (interleavedEquiv n).symm_apply_eq.mpr (interleavedEquiv_zero j).symm
  change (if ((interleavedEquiv n).symm (realIndex j)).2 = 0 then
    (z ((interleavedEquiv n).symm (realIndex j)).1).re else
    (z ((interleavedEquiv n).symm (realIndex j)).1).im) = _
  simp [hj]

@[simp] private theorem fromComplexCoordinates_imag (n : ℕ) (z : EuclideanSpace ℂ (Fin n))
    (j : Fin n) : fromComplexCoordinates n z (imagIndex j) = (z j).im := by
  have hj : (interleavedEquiv n).symm (imagIndex j) = (j, 1) :=
    (interleavedEquiv n).symm_apply_eq.mpr (interleavedEquiv_one j).symm
  change (if ((interleavedEquiv n).symm (imagIndex j)).2 = 0 then
    (z ((interleavedEquiv n).symm (imagIndex j)).1).re else
    (z ((interleavedEquiv n).symm (imagIndex j)).1).im) = _
  simp [hj]

/-- The coordinate map with the real directions ordered as
`(x₀,y₀,x₁,y₁, ...)`. -/
noncomputable def complexCoordinates (n : ℕ) : E n ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun := toComplexCoordinates n
  invFun := fromComplexCoordinates n
  left_inv x := by
    apply complexCoord_injective
    funext j
    simp [complexCoord, toComplexCoordinates]
  right_inv z := by
    ext j
    simpa [toComplexCoordinates, complexCoord, mul_comm] using Complex.re_add_im (z j)
  map_add' x y := by
    ext j
    change complexCoord (x + y) j = complexCoord x j + complexCoord y j
    exact (complexCoordCLM j).map_add x y
  map_smul' c x := by
    ext j
    change complexCoord (c • x) j = c • complexCoord x j
    exact (complexCoordCLM j).map_smul c x
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, norm_sq_interleaved]
    apply Finset.sum_congr rfl
    intro j _
    change ‖complexCoord x j‖ ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [complexCoord, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

@[simp] theorem complexCoordinates_apply (n : ℕ) (x : E n) (j : Fin n) :
    complexCoordinates n x j = complexCoord x j := rfl

@[simp] theorem complexCoordinates_realDirection (n : ℕ) (j : Fin n) :
    complexCoordinates n (realDirection j) = EuclideanSpace.single j (1 : ℂ) := by
  ext k
  simp [eq_comm]

@[simp] theorem complexCoordinates_imagDirection (n : ℕ) (j : Fin n) :
    complexCoordinates n (imagDirection j) = Complex.I • EuclideanSpace.single j (1 : ℂ) := by
  ext k
  simp [eq_comm]

theorem complexCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (complexCoordinates n) volume volume :=
  (complexCoordinates n).measurePreserving

#print axioms complexCoordinates
#print axioms complexCoordinates_measurePreserving

end KEBall
