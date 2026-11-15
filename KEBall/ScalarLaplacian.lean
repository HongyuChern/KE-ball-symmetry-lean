import KEBall.MetricHessian
import KEBall.EquationBasics
import KEBall.LocalMetric
import PoincareLib.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

/-! The scalar Laplacian of the actual real Hessian metric is twice the
complex Laplacian, with both the inverse-matrix and derivative conventions
fixed by `Domain`. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators ComplexOrder

namespace KEBall

theorem J_realDirection {n : ℕ} (i : Fin n) :
    J (realDirection i) = imagDirection i := by
  apply complexCoord_injective
  funext j
  simp [complexCoord_J, complexCoord_realDirection, complexCoord_imagDirection,
    mul_ite]

theorem J_imagDirection {n : ℕ} (i : Fin n) :
    J (imagDirection i) = -realDirection i := by
  rw [← J_realDirection, J_sq]

theorem hermitianRealification_dual_vector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (p : Fin n → ℂ) (w : E n)
    (hw : ∀ v : E n, hermitianRealification A w v =
      2 * (∑ i : Fin n, p i * complexCoord v i).re) :
    complexCoord w = A⁻¹.transpose.mulVec (star p) := by
  have hrow : A.transpose.mulVec (complexCoord w) = star p := by
    funext j
    exact hermitianRealification_dual_coordinates A p w hw j
  have ht := congrArg (A⁻¹.transpose.mulVec) hrow
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv A hA, Matrix.transpose_one, Matrix.one_mulVec] at ht
  exact ht

theorem metric_inverse_imagDirection {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i : Fin n) :
    (g.inner x).inverse (EuclideanSpace.proj (imagIndex i)) =
      J ((g.inner x).inverse (EuclideanSpace.proj (realIndex i))) := by
  apply (g.inner_isInvertible x).injective
  ext v
  change E n at v
  rw [(g.inner_isInvertible x).self_apply_inverse]
  change v (imagIndex i) = _
  rw [hg, realMetricForm_J_skew hu, ← hg,
    (g.inner_isInvertible x).self_apply_inverse]
  change v (imagIndex i) = -(J v) (realIndex i)
  simp

theorem metric_inverse_realDirection_coordinates {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n}
    (hA : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i j : Fin n) :
    complexCoord ((g.inner x).inverse (EuclideanSpace.proj (realIndex i))) j =
      (2 : ℂ)⁻¹ * (complexHessian u x)⁻¹ i j := by
  classical
  let p : Fin n → ℂ := Pi.single i (2 : ℂ)⁻¹
  have hw (v : E n) : hermitianRealification (complexHessian u x)
      ((g.inner x).inverse (EuclideanSpace.proj (realIndex i))) v =
      2 * (∑ k : Fin n, p k * complexCoord v k).re := by
    rw [← realMetricForm_eq, ← hg,
      (g.inner_isInvertible x).self_apply_inverse]
    simp [p, Pi.single_apply, complexCoord]
    rfl
  have hc := congrFun (hermitianRealification_dual_vector
    (complexHessian u x) hA p _ hw) j
  rw [hc]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, p, Pi.single_apply,
    Pi.star_apply, apply_ite, mul_comm]

theorem realMetricForm_metric_inverse_pair {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u h : E n → ℝ} {x : E n}
    (hA : (complexHessian u x).IsHermitian)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i : Fin n) :
    realMetricForm h x (realDirection i)
      ((g.inner x).inverse (EuclideanSpace.proj (realIndex i))) =
      (∑ j : Fin n, inverseCoefficient u x i j * complexHessian h x i j).re := by
  classical
  simp only [realMetricForm, complexCoord_realDirection]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [metric_inverse_realDirection_coordinates hdet hg,
    star_mul, star_inv₀, star_ofNat, hA.inv.apply, Complex.re_sum, Finset.mul_sum,
    inverseCoefficient]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem laplacian_eq_twice_complexLaplacian {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u h : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U)
    (hA : (complexHessian u x).IsHermitian)
    (hdet : IsUnit (complexHessian u x).det)
    (hh : ContDiffAt ℝ ∞ h x) :
    D.laplacian h x = 2 * complexLaplacian u h x := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  rw [D.laplacian_eq_sum_hessian_inverse hh, ← (interleavedEquiv n).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    interleavedEquiv_zero, interleavedEquiv_one, EuclideanSpace.basisFun_apply]
  change (∑ i : Fin n,
    (D.hessian h x (realDirection i)
        ((g.inner x).inverse (EuclideanSpace.proj (realIndex i))) +
      D.hessian h x (imagDirection i)
        ((g.inner x).inverse (EuclideanSpace.proj (imagIndex i))))) = _
  simp only [metric_inverse_imagDirection huAt (hg x hx)]
  have hp (i : Fin n) := hessian_J_pair_eq_twice_realMetricForm D hU hu hg hx hh
    (realDirection i) ((g.inner x).inverse (EuclideanSpace.proj (realIndex i)))
  simp only [J_realDirection] at hp
  simp_rw [hp, realMetricForm_metric_inverse_pair hA hdet (hg x hx)]
  simp only [complexLaplacian, Complex.re_sum, Finset.mul_sum]

/-- Both the metric and its scalar-operator identification are obtained from
the original solution. No operator identity is supplied as a hypothesis. -/
theorem IsSolution.exists_local_complex_laplacian {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ h : E n → ℝ, ContDiffAt ℝ ∞ h x →
        D.laplacian h x = 2 * complexLaplacian u h x) ∧
      (∀ x ∈ V, D.laplacian u x = 2 * (n : ℝ)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg⟩ := hu.exists_local_metric hp
  have huV := hu.contDiffOn_ball.mono hVB
  have hOp (x : E n) (hx : x ∈ V) (h : E n → ℝ) (hh : ContDiffAt ℝ ∞ h x) :
      D.laplacian h x = 2 * complexLaplacian u h x :=
    laplacian_eq_twice_complexLaplacian D hV huV hg hx
      (hu.2.2.1 x (hVB hx)).isHermitian
      (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx))) hh
  refine ⟨g, D, V, hV, hpV, hVB, hg, hOp, ?_⟩
  intro x hx
  rw [hOp x hx u (huV.contDiffAt (hV.mem_nhds hx)),
    hu.complexLaplacian_self (Metric.ball_subset_closedBall (hVB hx))]

end KEBall
