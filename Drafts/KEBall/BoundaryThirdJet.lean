import KEBall.SphereDifferential
import KEBall.BoundaryHessianBlock
import KEBall.ComplexMaximum
import Drafts.KEBall.AuxiliaryPRegularity

/-!
# Actual boundary third jets and fixed horizontal traces

SOURCE_DRAFT_UNCOMPILED. All derivatives are actual Frechet derivatives.
The first derivative of the PDE is proved in the open ball and extended
continuously to the closed ball. The boundary determinant restriction is
never differentiated in a transverse direction.

The horizontal trace below keeps the base point and horizontal plane fixed
while its Hessian evaluation point varies. No unitary frame is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace

namespace KEBall

theorem boundarySlope_eq_half_eulerDerivative {n : ℕ} (u : E n → ℝ) :
    boundarySlope u = fun y => (1 / 2 : ℝ) * eulerDerivative u y := by
  funext y
  unfold boundarySlope eulerDerivative
  ring

/-- The actual radial third jet, obtained from the already differentiated
Euler field and the frozen extension t(y)=Du_y(y)/2. -/
theorem fderiv_complexHessian_radial_eq_boundarySlope {n : ℕ}
    {u : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U) (i j : Fin n) :
    fderiv ℝ (fun y => complexHessian u y i j) x x =
      2 * complexHessian (boundarySlope u) x i j - 2 * complexHessian u x i j := by
  have hR : ContDiffAt ℝ ∞ (eulerDerivative u) x :=
    (eulerDerivative_contDiffOn hU hu).contDiffAt (hU.mem_nhds hx)
  have hhalf := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j)
    (complexHessian_const_mul_at hR (1 / 2 : ℝ))
  rw [← boundarySlope_eq_half_eulerDerivative u] at hhalf
  simp only [Matrix.smul_apply, smul_eq_mul] at hhalf
  rw [complexHessian_eulerDerivative hU hu hx] at hhalf
  push_cast at hhalf
  linear_combination -(2 : ℂ) * hhalf

theorem realMetricForm_const_mul_at {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (c : ℝ) (v w : E n) :
    realMetricForm (fun y => c * h y) x v w = c * realMetricForm h x v w := by
  unfold realMetricForm
  rw [complexHessian_const_mul_at hh]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The differentiated actual real metric, before substituting t=Ru/2. -/
theorem realMetricForm_eulerDerivative {n : ℕ} {u : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    realMetricForm (eulerDerivative u) x v w =
      fderiv ℝ (fun y => realMetricForm u y v w) x x +
        2 * realMetricForm u x v w := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hR := (eulerDerivative_contDiffOn hU hu).contDiffAt (hU.mem_nhds hx)
  rw [realMetricForm_eq_average_hessian hR,
    realHessian_eulerDerivative hU hu hx,
    realHessian_eulerDerivative hU hu hx,
    fderiv_realMetricForm hU hu hx,
    realMetricForm_eq_average_hessian huAt]
  ring

/-- Actual radial metric derivative used in the q-normal derivative.
The vectors v,w are fixed while the evaluation point varies. -/
theorem fderiv_realMetricForm_radial_eq_boundarySlope {n : ℕ}
    {u : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U) (v w : E n) :
    fderiv ℝ (fun y => realMetricForm u y v w) x x =
      2 * realMetricForm (boundarySlope u) x v w - 2 * realMetricForm u x v w := by
  have hR := (eulerDerivative_contDiffOn hU hu).contDiffAt (hU.mem_nhds hx)
  rw [boundarySlope_eq_half_eulerDerivative u,
    realMetricForm_const_mul_at hR, realMetricForm_eulerDerivative hU hu hx]
  ring

/-- Continuity of the inverse coefficient at the boundary follows from
the adjugate quotient and the actual nonzero boundary determinant. -/
theorem IsSolution.inverseCoefficient_continuousOn_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) (i j : Fin n) :
    ContinuousOn (fun x => inverseCoefficient u x i j) (closedUnitBall n) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hG (r s : Fin n) :
      ContDiffOn ℝ ∞ (fun x => complexHessian u x r s) (closedUnitBall n) :=
    (complexHessian_contDiffOn hU huU r s).mono hKU
  have hdet (x : E n) (hx : x ∈ closedUnitBall n) :
      (complexHessian u x).det ≠ 0 := isUnit_iff_ne_zero.mp (hu.det_isUnit_closedBall hx)
  have hquot := (matrixField_adjugate_contDiffOn hG j i).continuousOn.div
    (matrixField_det_contDiffOn hG).continuousOn hdet
  apply hquot.congr
  intro x hx
  exact AuxiliaryPRegularity.inverse_entry_eq_adjugate_div_det
    (complexHessian u x) (hdet x hx) j i

/-- The differentiated PDE extends by continuity; this statement does not
follow by differentiating only the equality restricted to the sphere. -/
theorem IsSolution.euler_hessian_contraction_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      fderiv ℝ (fun y => complexHessian u y i j) x x) =
      -(eulerDerivative u x : ℂ) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hD (i j : Fin n) : ContinuousOn
      (fun y => fderiv ℝ (fun z => complexHessian u z i j) y y)
      (closedUnitBall n) :=
    (((complexHessian_contDiffOn hU huU i j).fderiv_of_isOpen (m := 0) hU (by simp)).clm_apply
      contDiffOn_id).continuousOn.mono hKU
  have hleft : ContinuousOn (fun y => ∑ i : Fin n, ∑ j : Fin n,
      inverseCoefficient u y i j *
        fderiv ℝ (fun z => complexHessian u z i j) y y) (closedUnitBall n) := by
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    exact (hu.inverseCoefficient_continuousOn_closedBall i j).mul (hD i j)
  have hright : ContinuousOn (fun y => -(eulerDerivative u y : ℂ))
      (closedUnitBall n) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (eulerDerivative_contDiffOn hU huU)).neg.continuousOn.mono hKU
  have heq : EqOn
      (fun y => ∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u y i j *
        fderiv ℝ (fun z => complexHessian u z i j) y y)
      (fun y => -(eulerDerivative u y : ℂ)) (unitBall n) := by
    intro y hy
    exact hu.euler_hessian_contraction hy
  apply heq.of_subset_closure hleft hright Metric.ball_subset_closedBall ?_ hx
  rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
  exact Set.Subset.rfl

theorem IsSolution.complexLaplacian_eulerDerivative_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    complexLaplacian u (eulerDerivative u) x = (2 * n : ℝ) - eulerDerivative u x := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hs : (∑ i : Fin n, ∑ j : Fin n,
      inverseCoefficient u x i j * complexHessian (eulerDerivative u) x i j) =
      (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        fderiv ℝ (fun y => complexHessian u y i j) x x) +
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * complexHessian u x i j) := by
    simp only [complexHessian_eulerDerivative hU huU (hKU hx), mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [complexLaplacian, hs, hu.euler_hessian_contraction_closedBall hx]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    show (2 : ℂ).re = 2 by rfl, show (2 : ℂ).im = 0 by rfl, zero_mul, sub_zero]
  change -eulerDerivative u x + 2 * complexLaplacian u u x = _
  rw [hu.complexLaplacian_self hx]
  ring

/-- This boundary extension uses the exact ambient t, not an arbitrary
extension of the boundary slope. -/
theorem IsSolution.complexLaplacian_boundarySlope_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    complexLaplacian u (boundarySlope u) x = (n : ℝ) - boundarySlope u x := by
  have hR := hu.2.1.eulerDerivative.contDiffAt hx
  rw [boundarySlope_eq_half_eulerDerivative u,
    complexLaplacian_const_mul_at u hR, hu.complexLaplacian_eulerDerivative_closedBall hx]
  ring

/-- The trace in the fixed horizontal complex plane at x, evaluated at y.
Only the Hessian evaluation point y varies. On the unit sphere the subtracted
rank-one projection is the actual normal complex line. -/
noncomputable def frozenHorizontalComplexTrace {n : ℕ} (h : E n → ℝ)
    (x y : E n) : ℝ :=
  ((∑ i : Fin n, complexHessian h y i i) -
    ∑ i : Fin n, ∑ j : Fin n, complexHessian h y i j *
      complexCoord x i * star (complexCoord x j)).re

theorem complexHessian_trace_re_eq_realHessian_trace {n : ℕ}
    {h : E n → ℝ} {y : E n} (hh : ContDiffAt ℝ ∞ h y) :
    (∑ i : Fin n, complexHessian h y i i).re =
      (∑ a : Fin (2 * n), realHessian h y
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)) / 4 := by
  rw [← (interleavedEquiv n).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    interleavedEquiv_zero, interleavedEquiv_one]
  simp only [Complex.re_sum, complexHessian_real_entry hh, Complex.mul_re,
    Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [EuclideanSpace.basisFun_apply, realDirection, imagDirection,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  ring

/-- The conversion to real horizontal trace fixes the factor 1/4. -/
theorem frozenHorizontalComplexTrace_eq_real {n : ℕ}
    {h : E n → ℝ} {x y : E n} (hh : ContDiffAt ℝ ∞ h y) :
    frozenHorizontalComplexTrace h x y =
      ((∑ a : Fin (2 * n), realHessian h y
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)) -
        realHessian h y x x - realHessian h y (J x) (J x)) / 4 := by
  have hnormal := realMetricForm_eq_average_hessian hh x x
  unfold realMetricForm at hnormal
  unfold frozenHorizontalComplexTrace
  rw [Complex.sub_re, complexHessian_trace_re_eq_realHessian_trace hh]
  linarith

/-- The curvature correction is explicit. In particular the fixed trace
is not the derivative of the restricted boundary trace. -/
theorem frozenHorizontalComplexTrace_self {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) :
    frozenHorizontalComplexTrace h x x = horizontalLaplacian h x / 4 +
      ((n : ℝ) - 1) / 2 * fderiv ℝ h x x := by
  rw [frozenHorizontalComplexTrace_eq_real hh]
  unfold horizontalLaplacian
  ring

namespace BoundaryThirdJetAux

theorem sum_basis_inner_mul_apply {n : ℕ} (v : E n) (l : E n →L[ℝ] ℝ) :
    (∑ a : Fin (2 * n),
      inner ℝ (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a) v *
        l (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)) = l v := by
  have h := congrArg l ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr v)
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr] at h
  have he (a : Fin (2 * n)) :
      inner ℝ (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a) v = v a := by
    rw [real_inner_comm, EuclideanSpace.inner_basisFun_real]
  simpa only [he] using h

/-- A trace of the actual horizontal projection. Applying it in one slot
is enough: on the sphere it is an orthogonal projection. -/
theorem projected_bilinear_trace {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (x : E n) :
    (∑ a : Fin (2 * n), B
      (horizontalProjection x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a))
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)) =
      (∑ a : Fin (2 * n), B
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)) - B x x - B (J x) (J x) := by
  simp only [horizontalProjection, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
  rw [sum_basis_inner_mul_apply x (B x), sum_basis_inner_mul_apply (J x) (B (J x))]

end BoundaryThirdJetAux

/-- Explicit identification with the frozen real horizontal projection,
without introducing a normal unitary coordinate frame. -/
theorem frozenHorizontalComplexTrace_eq_horizontalProjection {n : ℕ}
    {h : E n → ℝ} {x y : E n} (hh : ContDiffAt ℝ ∞ h y) :
    frozenHorizontalComplexTrace h x y =
      (∑ a : Fin (2 * n), realHessian h y
        (horizontalProjection x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a))
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)) / 4 := by
  rw [BoundaryThirdJetAux.projected_bilinear_trace,
    frozenHorizontalComplexTrace_eq_real hh]

#print axioms IsSolution.euler_hessian_contraction_closedBall
#print axioms IsSolution.complexLaplacian_boundarySlope_closedBall
#print axioms frozenHorizontalComplexTrace_self

end KEBall
