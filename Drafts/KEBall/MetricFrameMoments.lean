import KEBall.ScalarLaplacian
import Drafts.KEBall.ComplexTensorContraction

/-!
# Complex moments of the actual real metric's orthonormal basis

Stage03 source draft; no current kernel receipt. The pointwise orthonormal
basis is never differentiated. Its two complex moments are derived from
Parseval and the already explicit inverse-metric coordinate formulas.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- Covector Parseval, for the actual metric used by the retained library. -/
theorem metric_frame_covector_pair {n : ℕ}
    (g : PoincareMT.RiemannianMetric (2 * n) (E n)) (x : E n)
    (L K : E n →L[ℝ] ℝ) :
    (∑ a, L (g.orthonormalBasis x a) * K (g.orthonormalBasis x a)) =
      L ((g.inner x).inverse K) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (2 * n)) : E n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hL (v : E n) : g.inner x ((g.inner x).inverse L) v = L v := by
    rw [(g.inner_isInvertible x).self_apply_inverse]
    rfl
  have hK (v : E n) : g.inner x v ((g.inner x).inverse K) = K v := by
    rw [show g.inner x v ((g.inner x).inverse K) =
        g.inner x ((g.inner x).inverse K) v from g.symm x v ((g.inner x).inverse K)]
    rw [(g.inner_isInvertible x).self_apply_inverse]
    rfl
  have h := (g.orthonormalBasis x).sum_inner_mul_inner
    ((g.inner x).inverse L) ((g.inner x).inverse K)
  change (∑ a, g.inner x ((g.inner x).inverse L) (g.orthonormalBasis x a) *
    g.inner x (g.orthonormalBasis x a) ((g.inner x).inverse K)) =
      g.inner x ((g.inner x).inverse L) ((g.inner x).inverse K) at h
  simpa only [hL, hK] using h

/-- All four real-coordinate second moments, in one fixed metric frame. -/
theorem metric_frame_four_moments {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i j : Fin n) :
    (∑ a, (g.orthonormalBasis x a).ofLp (realIndex i) *
        (g.orthonormalBasis x a).ofLp (realIndex j)) =
        (inverseCoefficient u x i j).re / 2 ∧
    (∑ a, (g.orthonormalBasis x a).ofLp (realIndex i) *
        (g.orthonormalBasis x a).ofLp (imagIndex j)) =
        -(inverseCoefficient u x i j).im / 2 ∧
    (∑ a, (g.orthonormalBasis x a).ofLp (imagIndex i) *
        (g.orthonormalBasis x a).ofLp (realIndex j)) =
        (inverseCoefficient u x i j).im / 2 ∧
    (∑ a, (g.orthonormalBasis x a).ofLp (imagIndex i) *
        (g.orthonormalBasis x a).ofLp (imagIndex j)) =
        (inverseCoefficient u x i j).re / 2 := by
  have hc := metric_inverse_realDirection_coordinates hdet hg j i
  have hre : ((g.inner x).inverse (EuclideanSpace.proj (realIndex j))).ofLp
      (realIndex i) = (inverseCoefficient u x i j).re / 2 := by
    have h := congrArg Complex.re hc
    norm_num [complexCoord, inverseCoefficient] at h ⊢
    linarith
  have him : ((g.inner x).inverse (EuclideanSpace.proj (realIndex j))).ofLp
      (imagIndex i) = (inverseCoefficient u x i j).im / 2 := by
    have h := congrArg Complex.im hc
    norm_num [complexCoord, inverseCoefficient] at h ⊢
    linarith
  have hrr := metric_frame_covector_pair g x
    (EuclideanSpace.proj (realIndex i)) (EuclideanSpace.proj (realIndex j))
  have hri := metric_frame_covector_pair g x
    (EuclideanSpace.proj (realIndex i)) (EuclideanSpace.proj (imagIndex j))
  have hir := metric_frame_covector_pair g x
    (EuclideanSpace.proj (imagIndex i)) (EuclideanSpace.proj (realIndex j))
  have hii := metric_frame_covector_pair g x
    (EuclideanSpace.proj (imagIndex i)) (EuclideanSpace.proj (imagIndex j))
  change (∑ a, (g.orthonormalBasis x a).ofLp (realIndex i) *
    (g.orthonormalBasis x a).ofLp (realIndex j)) = _ at hrr
  change (∑ a, (g.orthonormalBasis x a).ofLp (realIndex i) *
    (g.orthonormalBasis x a).ofLp (imagIndex j)) = _ at hri
  change (∑ a, (g.orthonormalBasis x a).ofLp (imagIndex i) *
    (g.orthonormalBasis x a).ofLp (realIndex j)) = _ at hir
  change (∑ a, (g.orthonormalBasis x a).ofLp (imagIndex i) *
    (g.orthonormalBasis x a).ofLp (imagIndex j)) = _ at hii
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hrr.trans hre
  · rw [hri, metric_inverse_imagDirection hu hg]
    change (J ((g.inner x).inverse (EuclideanSpace.proj (realIndex j))))
      (realIndex i) = _
    rw [J_realIndex, him]
    ring
  · exact hir.trans him
  · rw [hii, metric_inverse_imagDirection hu hg]
    change (J ((g.inner x).inverse (EuclideanSpace.proj (realIndex j))))
      (imagIndex i) = _
    rw [J_imagIndex, hre]

/-- The mixed complex moment is exactly the manuscript's inverseCoefficient,
not the opposite transpose. -/
theorem metric_frame_complex_moment {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i j : Fin n) :
    (∑ a, complexCoord (g.orthonormalBasis x a) i *
      star (complexCoord (g.orthonormalBasis x a) j)) = inverseCoefficient u x i j := by
  obtain ⟨hrr, hri, hir, hii⟩ := metric_frame_four_moments hu hdet hg i j
  apply Complex.ext
  · simp only [Complex.re_sum, complexCoord, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, zero_mul, one_mul, mul_zero, zero_add, add_zero,
      sub_zero, mul_neg, sub_neg_eq_add, Finset.sum_add_distrib]
    linarith
  · simp only [Complex.im_sum, complexCoord, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, zero_mul, one_mul, mul_zero, zero_add, add_zero,
      sub_zero, mul_neg, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    linarith

/-- The holomorphic second moment vanishes. No smooth choice of frame is used. -/
theorem metric_frame_holomorphic_moment {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i j : Fin n) :
    (∑ a, complexCoord (g.orthonormalBasis x a) i *
      complexCoord (g.orthonormalBasis x a) j) = 0 := by
  obtain ⟨hrr, hri, hir, hii⟩ := metric_frame_four_moments hu hdet hg i j
  apply Complex.ext
  · simp only [Complex.re_sum, complexCoord, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, zero_mul, one_mul,
      mul_zero, zero_add, add_zero, sub_zero, Finset.sum_sub_distrib]
    linarith
  · simp only [Complex.im_sum, complexCoord, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_im, zero_mul, one_mul,
      mul_zero, zero_add, add_zero, sub_zero, Finset.sum_add_distrib]
    linarith

end KEBall
