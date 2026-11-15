import KEBall.BoundarySchurValues
import Drafts.KEBall.BoundaryThirdJet

/-!
# The actual boundary inverse and its trace contraction

SOURCE_DRAFT_UNCOMPILED. The candidate inverse is multiplied by the actual
bordered scalar matrix, then identified with `Matrix.nonsing_inv`. The
boundary endpoints discharge every algebraic hypothesis from `IsSolution`.
The trace and realification formulas do not require a Hermitian hypothesis
on the test matrix: they are identities after taking real parts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

namespace BoundaryInverseSplitAux

theorem complexCoord_smul {n : ℕ} (r : ℝ) (v : E n) :
    complexCoord (r • v) = (r : ℂ) • complexCoord v := by
  ext i
  change ((r * v (realIndex i) : ℝ) : ℂ) +
      Complex.I * ((r * v (imagIndex i) : ℝ) : ℂ) =
    (r : ℂ) * ((v (realIndex i) : ℂ) + Complex.I * (v (imagIndex i) : ℂ))
  push_cast
  ring

theorem complexCoord_sub {n : ℕ} (v w : E n) :
    complexCoord (v - w) = complexCoord v - complexCoord w := by
  ext i
  change ((v (realIndex i) - w (realIndex i) : ℝ) : ℂ) +
      Complex.I * ((v (imagIndex i) - w (imagIndex i) : ℝ) : ℂ) =
    ((v (realIndex i) : ℂ) + Complex.I * (v (imagIndex i) : ℂ)) -
      ((w (realIndex i) : ℂ) + Complex.I * (w (imagIndex i) : ℂ))
  push_cast
  ring

theorem mul_vecMulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v w : Fin n → ℂ) :
    A * vecMulVec v w = vecMulVec (A.mulVec v) w := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem trace_vecMulVec_mul {n : ℕ} (v w : Fin n → ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) :
    (vecMulVec v w * H).trace = w ⬝ᵥ H.mulVec v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end BoundaryInverseSplitAux

/-- The inverse of a scalar horizontal block, without requiring a selected
unitary frame. `d,e` are independent dual vectors in this algebraic lemma. -/
theorem borderedScalarMatrix_inv_split {n : ℕ} (hn : 1 ≤ n) {t a : ℂ}
    (ht : t ≠ 0) {c d b e : Fin n → ℂ}
    (hdc : d ⬝ᵥ c = 1) (hdb : d ⬝ᵥ b = 0) (hec : e ⬝ᵥ c = 0)
    (hσ : a - (e ⬝ᵥ b) / t ≠ 0) :
    (borderedScalarMatrix t a c d b e)⁻¹ =
      t⁻¹ • (1 - vecMulVec c d) +
        (a - (e ⬝ᵥ b) / t)⁻¹ •
          vecMulVec (c - t⁻¹ • b) (d - t⁻¹ • e) := by
  let A := borderedScalarMatrix t a c d b e
  let S : Matrix (Fin n) (Fin n) ℂ :=
    t⁻¹ • (1 - vecMulVec c d) +
      (a - (e ⬝ᵥ b) / t)⁻¹ •
        vecMulVec (c - t⁻¹ • b) (d - t⁻¹ • e)
  have hnum : t * a - (e ⬝ᵥ b) ≠ 0 := by
    have heq : a - (e ⬝ᵥ b) / t = (t * a - (e ⬝ᵥ b)) / t := by
      field_simp [ht] <;> ring
    intro hz
    apply hσ
    rw [heq, hz, zero_div]
  have hc : A.mulVec c = b + a • c := by
    dsimp [A, borderedScalarMatrix]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.vecMulVec_mulVec, hdc, hec, op_smul_eq_smul, one_smul, zero_smul,
      add_zero]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hw : A.mulVec (c - t⁻¹ • b) = (a - (e ⬝ᵥ b) / t) • c :=
    borderedScalarMatrix_mulVec_normal ht hdc hdb hec
  have hprod : A * S = 1 := by
    dsimp [S]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
      BoundaryInverseSplitAux.mul_vecMulVec, hc, Matrix.mul_smul,
      BoundaryInverseSplitAux.mul_vecMulVec, hw]
    ext i j
    simp only [A, borderedScalarMatrix, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp [ht, hσ, hnum]
    <;> ring
  have hdet : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    dsimp [A]
    rw [borderedScalarMatrix_det hn ht hdc hdb hec]
    exact mul_ne_zero (pow_ne_zero _ ht) hσ
  change A⁻¹ = S
  calc
    A⁻¹ = A⁻¹ * 1 := (Matrix.mul_one _).symm
    _ = A⁻¹ * (A * S) := by rw [hprod]
    _ = S := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- The actual Schur complement as a complex scalar. -/
theorem IsSolution.boundary_schur_complement_complex {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    boundaryNormalEntry u x -
      (star (boundaryMixedComplex u x) ⬝ᵥ boundaryMixedComplex u x) /
        (boundarySlope u x : ℂ) =
      (μ / boundarySlope u x ^ (n - 1) : ℝ) := by
  calc
    _ = ((fderiv ℝ (boundarySlope u) x x / 2 -
        ‖horizontalGradient (boundarySlope u) x‖ ^ 2 /
          (4 * boundarySlope u x) : ℝ) : ℂ) := by
      rw [boundaryMixedComplex_normSq]
      unfold boundaryNormalEntry
      push_cast
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    _ = _ := by rw [hu.boundary_schur_complement hn hx]

/-- The corrected complex normal in the rank-one term of the inverse. -/
noncomputable def boundaryInverseNormal {n : ℕ} (u : E n → ℝ) (x : E n) :
    Fin n → ℂ :=
  boundaryNormalComplex x - (boundarySlope u x : ℂ)⁻¹ • boundaryMixedComplex u x

/-- The real vector associated with the actual inverse normal. The scalar
in the denominator is the boundary Schur complement. -/
noncomputable def boundaryInverseDirection {n : ℕ} (u : E n → ℝ) (μ : ℝ)
    (x : E n) : E n :=
  (μ / boundarySlope u x ^ (n - 1))⁻¹ •
    (boundarySlope u x • x - (1 / 2 : ℝ) • horizontalGradient (boundarySlope u) x)

theorem IsSolution.boundary_inverse_split {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    (complexHessian u x)⁻¹ =
      (boundarySlope u x : ℂ)⁻¹ •
        (1 - vecMulVec (boundaryNormalComplex x) (star (boundaryNormalComplex x))) +
      ((boundarySlope u x ^ (n - 1) / μ : ℝ) : ℂ) •
        vecMulVec (boundaryInverseNormal u x) (star (boundaryInverseNormal u x)) := by
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hu.boundarySlope_pos hn hx)
  have hσ : boundaryNormalEntry u x -
      (star (boundaryMixedComplex u x) ⬝ᵥ boundaryMixedComplex u x) /
        (boundarySlope u x : ℂ) ≠ 0 := by
    rw [hu.boundary_schur_complement_complex hn hx]
    exact_mod_cast div_ne_zero (ne_of_gt hu.1)
      (pow_ne_zero _ (ne_of_gt (hu.boundarySlope_pos hn hx)))
  rw [sphere_complexHessian_block hu.2.1 hu.2.2.2.2 hx,
    borderedScalarMatrix_inv_split (by omega) ht (boundaryNormalComplex_unit hx)
      (boundaryMixedComplex_orthogonal u hx)
      (boundaryMixedComplex_orthogonal_reverse u hx) hσ,
    hu.boundary_schur_complement_complex hn hx]
  have hd : star (boundaryInverseNormal u x) =
      star (boundaryNormalComplex x) -
        (boundarySlope u x : ℂ)⁻¹ • star (boundaryMixedComplex u x) := by
    ext i
    simp [boundaryInverseNormal, star_sub, star_mul] <;> ring
  rw [hd]
  ext i j
  simp [boundaryInverseNormal, Matrix.smul_apply, smul_eq_mul, inv_div]

/-- An explicit action of the actual inverse on the boundary complex
gradient. The right side equals the conjugated complex coordinates of V. -/
theorem IsSolution.boundary_inverse_times_boundary_gradient {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    (complexHessian u x)⁻¹.mulVec
        ((boundarySlope u x : ℂ) • boundaryNormalComplex x) =
      ((boundarySlope u x * (boundarySlope u x ^ (n - 1) / μ) : ℝ) : ℂ) •
        boundaryInverseNormal u x := by
  have hstar : star (boundaryInverseNormal u x) ⬝ᵥ boundaryNormalComplex x = 1 := by
    simp only [boundaryInverseNormal, star_sub, star_smul, smul_dotProduct,
      sub_dotProduct, boundaryNormalComplex_unit hx,
      boundaryMixedComplex_orthogonal_reverse u hx, smul_zero, sub_zero]
  rw [hu.boundary_inverse_split hn hx]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_smul,
    boundaryNormalComplex_unit hx, hstar, smul_eq_mul, mul_one,
    op_smul_eq_smul, sub_self, smul_zero, zero_add, smul_smul]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem IsSolution.boundary_inverse_trace_split {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n)
    (H : Matrix (Fin n) (Fin n) ℂ) :
    ((complexHessian u x)⁻¹ * H).trace.re =
      (boundarySlope u x)⁻¹ *
        (H.trace.re - (star (boundaryNormalComplex x) ⬝ᵥ
          H.mulVec (boundaryNormalComplex x)).re) +
      (boundarySlope u x ^ (n - 1) / μ) *
        (star (boundaryInverseNormal u x) ⬝ᵥ
          H.mulVec (boundaryInverseNormal u x)).re := by
  rw [hu.boundary_inverse_split hn hx]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
    BoundaryInverseSplitAux.trace_vecMulVec_mul]
  rw [show (boundarySlope u x : ℂ)⁻¹ =
    ((boundarySlope u x)⁻¹ : ℝ) by simp]
  simp only [smul_eq_mul, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Quadratic contraction against a conjugated complex coordinate vector.
This is the factor 1/2 in the real metric normalization. -/
theorem complexHessian_conjugate_quadratic_eq_realMetricForm {n : ℕ}
    (h : E n → ℝ) (x v : E n) :
    (star (star (complexCoord v)) ⬝ᵥ
      (complexHessian h x).mulVec (star (complexCoord v))).re =
        realMetricForm h x v v / 2 := by
  have he : star (star (complexCoord v)) ⬝ᵥ
      (complexHessian h x).mulVec (star (complexCoord v)) =
      ∑ i : Fin n, ∑ j : Fin n,
        complexHessian h x i j * complexCoord v i * star (complexCoord v j) := by
    simp only [star_star, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, realMetricForm]
  ring

/-- Identification of the inverse normal with the actual real direction.
All divisions are justified by the original boundary positivity. -/
theorem IsSolution.boundaryInverseNormal_eq_scaled_coord {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    boundaryInverseNormal u x =
      ((μ / boundarySlope u x ^ (n - 1) / boundarySlope u x : ℝ) : ℂ) •
        star (complexCoord (boundaryInverseDirection u μ x)) := by
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hu.boundarySlope_pos hn hx)
  have hμ : (μ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  simp only [boundaryInverseDirection, BoundaryInverseSplitAux.complexCoord_smul,
    BoundaryInverseSplitAux.complexCoord_sub, star_smul, star_sub]
  ext i
  simp only [boundaryInverseNormal, boundaryNormalComplex, boundaryMixedComplex,
    Pi.sub_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast
  field_simp [ht, hμ]
  <;> ring

theorem IsSolution.boundary_inverse_gradient_complex {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    (complexHessian u x)⁻¹.mulVec
        ((boundarySlope u x : ℂ) • boundaryNormalComplex x) =
      star (complexCoord (boundaryInverseDirection u μ x)) := by
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hu.boundarySlope_pos hn hx)
  have hμ : (μ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  rw [hu.boundary_inverse_times_boundary_gradient hn hx,
    hu.boundaryInverseNormal_eq_scaled_coord hn hx, smul_smul]
  have hc : ((boundarySlope u x * (boundarySlope u x ^ (n - 1) / μ) : ℝ) : ℂ) *
      ((μ / boundarySlope u x ^ (n - 1) / boundarySlope u x : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [ht, hμ]
  rw [hc, one_smul]

/-- The transposed inverse coefficients in the project's Wirtinger
convention give the unconjugated coordinates of the same real vector. -/
theorem IsSolution.boundary_inverseCoefficient_partialBar {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) (i : Fin n) :
    (∑ j : Fin n, inverseCoefficient u x i j *
      partialBar j (fun y => (u y : ℂ)) x) =
        complexCoord (boundaryInverseDirection u μ x) i := by
  have hHerm := (hu.hessian_posDef_closedBall (Metric.sphere_subset_closedBall hx)).inv.isHermitian
  have he := congrArg (fun v : Fin n → ℂ => star (v i))
    (hu.boundary_inverse_gradient_complex hn hx)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.star_apply,
    boundaryNormalComplex, smul_eq_mul, star_sum, star_mul, star_star] at he
  rw [← he]
  simp only [inverseCoefficient, sphere_partialBar hu.2.1 hu.2.2.2.2 hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [hHerm.apply j i]
  simp <;> ring

theorem IsSolution.boundary_complexLaplacian_split {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) (h : E n → ℝ) :
    complexLaplacian u h x =
      frozenHorizontalComplexTrace h x x / boundarySlope u x +
      (μ / boundarySlope u x ^ (n - 1)) / (2 * boundarySlope u x ^ 2) *
        realMetricForm h x (boundaryInverseDirection u μ x)
          (boundaryInverseDirection u μ x) := by
  have ht : boundarySlope u x ≠ 0 := ne_of_gt (hu.boundarySlope_pos hn hx)
  have hμ : μ ≠ 0 := ne_of_gt hu.1
  have hhorizontal : (complexHessian h x).trace.re -
      (star (boundaryNormalComplex x) ⬝ᵥ
        (complexHessian h x).mulVec (boundaryNormalComplex x)).re =
        frozenHorizontalComplexTrace h x x := by
    unfold frozenHorizontalComplexTrace
    rw [Complex.sub_re]
    congr 1
    · congr 1
      simp only [boundaryNormalComplex, star_star, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hquadratic : (star (boundaryInverseNormal u x) ⬝ᵥ
      (complexHessian h x).mulVec (boundaryInverseNormal u x)).re =
      (μ / boundarySlope u x ^ (n - 1) / boundarySlope u x) ^ 2 *
        (realMetricForm h x (boundaryInverseDirection u μ x)
          (boundaryInverseDirection u μ x) / 2) := by
    rw [hu.boundaryInverseNormal_eq_scaled_coord hn hx]
    simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [complexHessian_conjugate_quadratic_eq_realMetricForm]
    ring
  rw [complexLaplacian_eq_trace, hu.boundary_inverse_trace_split hn hx,
    hhorizontal, hquadratic]
  field_simp [ht, hμ]
  <;> ring

#print axioms borderedScalarMatrix_inv_split
#print axioms IsSolution.boundary_inverse_split
#print axioms IsSolution.boundary_inverse_times_boundary_gradient
#print axioms IsSolution.boundary_inverse_trace_split
#print axioms IsSolution.boundary_inverseCoefficient_partialBar
#print axioms IsSolution.boundary_complexLaplacian_split

end KEBall
