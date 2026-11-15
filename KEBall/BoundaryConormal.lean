import KEBall.BoundaryHessianBlock

/-!
# The exact conormal flux from the actual boundary Hessian

Every algebraic input to the normal adjugate is discharged from the
concrete sphere geometry. The resulting pointwise identity is substituted
into the already proved nonzero-boundary cofactor Green formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Matrix MeasureTheory
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

@[simp] theorem complexVectorReal_complexCoord {n : ℕ} (v : E n) :
    complexVectorReal (complexCoord v) = v :=
  complexCoord_injective (complexCoord_complexVectorReal _)

theorem complexCoord_pairing {n : ℕ} (x v : E n) :
    (star (complexCoord x)) ⬝ᵥ complexCoord v =
      (inner ℝ x v : ℂ) + Complex.I * (inner ℝ (J x) v : ℂ) := by
  have hr : ((star (complexCoord x)) ⬝ᵥ complexCoord v).re = inner ℝ x v := by
    simpa only [dotProduct, Pi.star_apply, complexVectorReal_complexCoord] using
      (inner_complexVectorReal x (complexCoord v)).symm
  have hJ : inner ℝ (J x) v =
      (-Complex.I * ((star (complexCoord x)) ⬝ᵥ complexCoord v)).re := by
    rw [← complexVectorReal_complexCoord v, inner_complexVectorReal]
    simp only [complexCoord_complexVectorReal, complexCoord_J, star_mul,
      Complex.star_def, Complex.conj_I, dotProduct, Pi.star_apply, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hi : ((star (complexCoord x)) ⬝ᵥ complexCoord v).im = inner ℝ (J x) v := by
    simpa only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
      Complex.neg_im, Complex.I_im, neg_mul, one_mul, zero_sub, neg_neg] using hJ.symm
  apply Complex.ext
  · simpa using hr
  · simpa using hi

theorem boundaryNormalComplex_unit {n : ℕ} {x : E n} (hx : x ∈ unitSphere n) :
    star (boundaryNormalComplex x) ⬝ᵥ boundaryNormalComplex x = 1 := by
  have hnorm : ‖x‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  simp only [boundaryNormalComplex, star_star]
  rw [dotProduct_comm]
  change (∑ i : Fin n, star (complexCoord x i) * complexCoord x i) = 1
  rw [sum_star_complexCoord_mul, hnorm]
  norm_num

theorem boundaryMixedComplex_orthogonal {n : ℕ} (u : E n → ℝ) {x : E n}
    (hx : x ∈ unitSphere n) :
    star (boundaryNormalComplex x) ⬝ᵥ boundaryMixedComplex u x = 0 := by
  have hp : star (complexCoord x) ⬝ᵥ
      complexCoord (horizontalGradient (boundarySlope u) x) = 0 := by
    rw [complexCoord_pairing, horizontalGradient_inner_normal _ hx,
      horizontalGradient_inner_hopf _ hx]
    simp
  simp only [boundaryMixedComplex, boundaryNormalComplex, star_star, dotProduct_smul]
  have hd : complexCoord x ⬝ᵥ
      star (complexCoord (horizontalGradient (boundarySlope u) x)) = 0 := by
    rw [dotProduct_comm, star_dotProduct, hp]
    simp only [star_zero]
  rw [hd, smul_zero]

theorem boundaryMixedComplex_orthogonal_reverse {n : ℕ} (u : E n → ℝ) {x : E n}
    (hx : x ∈ unitSphere n) :
    star (boundaryMixedComplex u x) ⬝ᵥ boundaryNormalComplex x = 0 := by
  rw [star_dotProduct, boundaryMixedComplex_orthogonal u hx]
  simp only [star_zero]

theorem IsSolution.boundary_adjugate_normal {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    (complexHessian u x).adjugate.mulVec (boundaryNormalComplex x) =
      (boundarySlope u x : ℂ) ^ (n - 1) •
        (boundaryNormalComplex x - (boundarySlope u x : ℂ)⁻¹ • boundaryMixedComplex u x) := by
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hu.boundarySlope_pos hn hx))
  have hblock := sphere_complexHessian_block hu.2.1 hu.2.2.2.2 hx
  have hd : (complexHessian u x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (hu.det_isUnit_closedBall (Metric.sphere_subset_closedBall hx))
  rw [hblock] at hd ⊢
  exact borderedScalarMatrix_adjugate_normal (by omega) ht
    (boundaryNormalComplex_unit hx) (boundaryMixedComplex_orthogonal u hx)
    (boundaryMixedComplex_orthogonal_reverse u hx) hd

theorem wirtinger_flux_direction {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (v : E n) :
    (∑ i : Fin n, star (complexCoord v i) * partialBar i (fun y => (h y : ℂ)) x).re =
      fderiv ℝ h x v / 2 := by
  have he : (∑ i : Fin n, star (complexCoord v i) *
      partialBar i (fun y => (h y : ℂ)) x) =
      star (∑ i : Fin n, partialZ i (fun y => (h y : ℂ)) x * complexCoord v i) := by
    simp only [partialBar_ofReal hh, star_sum, star_mul]
  rw [he, Complex.star_def, Complex.conj_re, fderiv_eq_wirtinger hh v]
  ring

theorem IsSolution.boundary_cofactor_conormal {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u h : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n)
    (hh : DifferentiableAt ℝ h x) :
    (∑ i : Fin n, ∑ j : Fin n, star (complexCoord x i) *
      (complexHessian u x).adjugate j i * partialBar j (fun y => (h y : ℂ)) x).re =
      (1 / 2 : ℝ) * ((boundarySlope u x) ^ (n - 1) * conormalDerivative u h x) := by
  have he : (∑ i : Fin n, ∑ j : Fin n, star (complexCoord x i) *
      (complexHessian u x).adjugate j i * partialBar j (fun y => (h y : ℂ)) x) =
      ∑ j : Fin n, ((complexHessian u x).adjugate.mulVec (boundaryNormalComplex x)) j *
        partialBar j (fun y => (h y : ℂ)) x := by
    rw [Finset.sum_comm]
    simp only [Matrix.mulVec, dotProduct, boundaryNormalComplex, Pi.star_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hm : (∑ j : Fin n, boundaryMixedComplex u x j *
      partialBar j (fun y => (h y : ℂ)) x).re =
      fderiv ℝ h x (horizontalGradient (boundarySlope u) x) / 4 := by
    simp only [boundaryMixedComplex, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
    rw [show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [wirtinger_flux_direction hh]
    ring
  have hdn : (∑ j : Fin n, boundaryNormalComplex x j *
      partialBar j (fun y => (h y : ℂ)) x).re = fderiv ℝ h x x / 2 :=
    wirtinger_flux_direction hh x
  have hinner : fderiv ℝ h x (horizontalGradient (boundarySlope u) x) =
      inner ℝ (horizontalGradient (boundarySlope u) x) (horizontalGradient h x) := by
    rw [real_inner_comm]
    exact (inner_horizontalGradient h (horizontalGradient_inner_normal _ hx)
      (horizontalGradient_inner_hopf _ hx)).symm
  rw [he, hu.boundary_adjugate_normal hn hx]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [show (boundarySlope u x : ℂ) ^ (n - 1) =
      ((boundarySlope u x ^ (n - 1) : ℝ) : ℂ) by simp,
    show (boundarySlope u x : ℂ)⁻¹ = ((boundarySlope u x)⁻¹ : ℝ) by simp]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, mul_zero, add_zero]
  rw [hdn, hm, hinner]
  unfold conormalDerivative
  ring

theorem IsSolution.conormalGreen {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u h : E n → ℝ} (hu : IsSolution n μ u) (hh : SmoothNear (closedUnitBall n) h) :
    (∫ x in unitBall n, complexLaplacian u h x * (complexHessian u x).det.re ∂volume0 n) =
      (n : ℝ) / 2 * ∫ x : Sphere n,
        boundarySlope u x.1 ^ (n - 1) * conormalDerivative u h x.1 ∂sphere0 n := by
  rw [hu.cofactorGreen (by omega) hh]
  have he : (fun x : Sphere n => (∑ i : Fin n, ∑ j : Fin n,
      star (complexCoord x.1 i) * (complexHessian u x.1).adjugate j i *
        partialBar j (fun y => (h y : ℂ)) x.1).re) =
      fun x : Sphere n => (1 / 2 : ℝ) *
        (boundarySlope u x.1 ^ (n - 1) * conormalDerivative u h x.1) := by
    funext x
    exact hu.boundary_cofactor_conormal hn x.2
      ((hh.contDiffAt (Metric.sphere_subset_closedBall x.2)).differentiableAt (by simp))
  rw [he, integral_const_mul]
  ring

#print axioms complexCoord_pairing
#print axioms IsSolution.boundary_adjugate_normal
#print axioms IsSolution.boundary_cofactor_conormal
#print axioms IsSolution.conormalGreen

end KEBall
