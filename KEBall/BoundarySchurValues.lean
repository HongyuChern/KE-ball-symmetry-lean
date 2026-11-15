import KEBall.BoundaryConormal

/-! The true boundary Schur complement and metric gradient norm values,
computed from the actual Hessian block and actual inverse matrix. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

theorem boundaryMixedComplex_normSq {n : ℕ} (u : E n → ℝ) (x : E n) :
    star (boundaryMixedComplex u x) ⬝ᵥ boundaryMixedComplex u x =
      (‖horizontalGradient (boundarySlope u) x‖ ^ 2 / 4 : ℝ) := by
  simp only [boundaryMixedComplex, star_smul, star_inv, star_ofNat,
    smul_dotProduct, dotProduct_smul, star_star, smul_eq_mul]
  rw [dotProduct_comm]
  rw [show star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ by norm_num]
  change (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ *
    (∑ i : Fin n, star (complexCoord (horizontalGradient (boundarySlope u) x) i) *
      complexCoord (horizontalGradient (boundarySlope u) x) i)) = _
  rw [sum_star_complexCoord_mul]
  push_cast
  ring

theorem IsSolution.boundary_schur_complement {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    fderiv ℝ (boundarySlope u) x x / 2 -
      ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / (4 * boundarySlope u x) =
      μ / boundarySlope u x ^ (n - 1) := by
  have htR := hu.boundarySlope_pos hn hx
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt htR
  have hblock := sphere_complexHessian_block hu.2.1 hu.2.2.2.2 hx
  have hd := borderedScalarMatrix_det (a := boundaryNormalEntry u x) (by omega : 1 ≤ n) ht
    (boundaryNormalComplex_unit hx) (boundaryMixedComplex_orthogonal u hx)
    (boundaryMixedComplex_orthogonal_reverse u hx)
  rw [← hblock, hu.det_eq_on_sphere hx, boundaryMixedComplex_normSq,
    boundaryNormalEntry] at hd
  push_cast at hd
  have hreal : μ = boundarySlope u x ^ (n - 1) *
      (fderiv ℝ (boundarySlope u) x x / 2 -
        ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / (4 * boundarySlope u x)) := by
    apply Complex.ofReal_injective
    push_cast
    convert hd using 1 <;> ring
  apply (eq_div_iff (pow_ne_zero _ (ne_of_gt htR))).mpr
  nlinarith [hreal]

theorem IsSolution.boundary_inverse_normal_pairing {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    star (boundaryNormalComplex x) ⬝ᵥ
      ((complexHessian u x)⁻¹.mulVec (boundaryNormalComplex x)) =
        (boundarySlope u x : ℂ) ^ (n - 1) / (μ : ℂ) := by
  have hunit := hu.det_isUnit_closedBall (Metric.sphere_subset_closedBall hx)
  have ha : (complexHessian u x).det • (complexHessian u x)⁻¹ =
      (complexHessian u x).adjugate := by
    rw [Matrix.nonsing_inv_apply _ hunit, smul_smul, hunit.mul_val_inv, one_smul]
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ =>
    star (boundaryNormalComplex x) ⬝ᵥ A.mulVec (boundaryNormalComplex x)) ha
  rw [Matrix.smul_mulVec, dotProduct_smul, hu.boundary_adjugate_normal hn hx,
    dotProduct_smul, dotProduct_sub, dotProduct_smul,
    boundaryNormalComplex_unit hx, boundaryMixedComplex_orthogonal u hx,
    smul_zero, sub_zero] at he
  simp only [smul_eq_mul, mul_one, hu.det_eq_on_sphere hx] at he
  apply (eq_div_iff (show (μ : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hu.1)).mpr
  simpa only [mul_comm] using he

theorem IsSolution.gradientNormSq_on_sphere {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    gradientNormSq u x = boundarySlope u x ^ (n + 1) / μ := by
  have hpair := hu.boundary_inverse_normal_pairing hn hx
  have he : (∑ i : Fin n, ∑ j : Fin n,
      inverseCoefficient u x i j * partialZ i (fun y => (u y : ℂ)) x *
        partialBar j (fun y => (u y : ℂ)) x) =
      (boundarySlope u x : ℂ) ^ 2 *
        (star (boundaryNormalComplex x) ⬝ᵥ
          ((complexHessian u x)⁻¹.mulVec (boundaryNormalComplex x))) := by
    simp only [inverseCoefficient, sphere_partialZ hu.2.1 hu.2.2.2.2 hx,
      sphere_partialBar hu.2.1 hu.2.2.2.2 hx, boundaryNormalComplex, star_star,
      Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [gradientNormSq, he, hpair]
  have hp : (boundarySlope u x : ℂ) ^ 2 *
      (boundarySlope u x : ℂ) ^ (n - 1) = (boundarySlope u x : ℂ) ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← mul_div_assoc, hp]
  norm_cast

#print axioms IsSolution.boundary_schur_complement
#print axioms IsSolution.boundary_inverse_normal_pairing
#print axioms IsSolution.gradientNormSq_on_sphere

end KEBall
