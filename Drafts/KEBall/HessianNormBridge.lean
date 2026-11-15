import Drafts.KEBall.HessianDefect
import Drafts.KEBall.MetricFrameMoments

/-!
# The real Hessian-defect norm equals twice the complex tensor norm

Stage03 source draft, not kernel checked. Norms use their actual separate
constructions: the retained real metric's orthonormal basis on the left,
and the frozen inverseCoefficient twice on the right. The real metric is
G = 2 Re(g), so both covariant slots and the factor 2 are essential.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- The paper's complex (2,0)-tensor norm, using its inverse transpose. -/
noncomputable def complexTensorNormSq {n : ℕ} (u : E n → ℝ) (x : E n)
    (S : Fin n → Fin n → ℂ) : ℝ :=
  (∑ i, ∑ j, ∑ k, ∑ l,
    inverseCoefficient u x i k * inverseCoefficient u x j l *
      S i j * star (S k l)).re

/-- Every real anti-J bilinear form is twice the real part of its (2,0) part.
This is a pointwise bilinear identity, not an assumed connection property. -/
theorem antiJ_bilinear_reconstruction {n : ℕ}
    (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hJ : ∀ v w, B (J v) (J w) = -B v w) (v w : E n) :
    B v w = 2 * (∑ i, ∑ j,
      complexify20 (fun a b => B a b) i j * complexCoord v i * complexCoord w j).re := by
  have hyy (i j : Fin n) : B (imagDirection i) (imagDirection j) =
      -B (realDirection i) (realDirection j) := by
    simpa only [J_realDirection_eq_imag] using hJ (realDirection i) (realDirection j)
  have hyx (i j : Fin n) : B (imagDirection i) (realDirection j) =
      B (realDirection i) (imagDirection j) := by
    have h := hJ (realDirection i) (imagDirection j)
    simp only [J_realDirection_eq_imag, J_imagDirection_eq_neg, map_neg] at h
    linarith
  rw [realBilinear_interleaved]
  simp only [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [hyy, hyx, complexify20]
  norm_num [complexCoord, Complex.mul_re, Complex.mul_im]
  ring

/-- A bundled realization of the ACTUAL covariant Hessian defect. -/
noncomputable def retainedHessianDefectBilinear {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (u : E n → ℝ) (x : E n) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  let A : E n →L[ℝ] E n := D.connection (D.gradient u) x
  (g.euclideanCoefficients x).comp A -
    g.euclideanCoefficients x

theorem retainedHessianDefectBilinear_apply {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    retainedHessianDefectBilinear D u x v w = hessianDefect D u x v w := by
  have hm : ContMDiffAt (𝓡 (2 * n)) 𝓘(ℝ, ℝ) ∞ u x :=
    contMDiffAt_iff_contDiffAt.mpr hu
  rw [hessianDefect, D.hessian_eq_inner_connection_gradient hm]
  rfl

theorem complexify20_sub {n : ℕ} (A B : E n → E n → ℝ) (i j : Fin n) :
    complexify20 (fun v w => A v w - B v w) i j =
      complexify20 A i j - complexify20 B i j := by
  simp only [complexify20]
  push_cast
  ring

/-- The real Hermitian metric has no (2,0) part. -/
theorem complexify20_metric_eq_zero {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i j : Fin n) : complexify20 (fun (v w : E n) => g.inner x v w) i j = 0 := by
  have hyy : g.inner x (imagDirection i) (imagDirection j) =
      g.inner x (realDirection i) (realDirection j) := by
    rw [← J_realDirection_eq_imag i, ← J_realDirection_eq_imag j,
      hg, realMetricForm_J_J hu, ← hg]
  have hyx : g.inner x (imagDirection i) (realDirection j) =
      -g.inner x (realDirection i) (imagDirection j) := by
    rw [← J_realDirection_eq_imag i, hg, realMetricForm_J_skew hu,
      J_realDirection_eq_imag, ← hg]
  simp only [complexify20, hyy, hyx]
  push_cast
  ring

/-- Complete pointwise norm identification for the actual selected connection.
No frame-moment, norm, or Einstein identity is an input hypothesis. -/
theorem hessianDefectNormSq_eq_twice_complexTensorNormSq {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hdet : IsUnit (complexHessian u x).det) :
    hessianDefectNormSq D u x =
      2 * complexTensorNormSq u x (covariantHessian20 u x) := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  let B := retainedHessianDefectBilinear D u x
  have hB (v w : E n) : B v w = hessianDefect D u x v w :=
    retainedHessianDefectBilinear_apply D huAt v w
  have hBJ (v w : E n) : B (J v) (J w) = -B v w := by
    rw [hB, hB]
    exact hessianDefect_J_J D hU hu hg hx v w
  have h20 (i j : Fin n) : complexify20 (fun v w => B v w) i j =
      covariantHessian20 u x i j := by
    have heq : (fun (v w : E n) => B v w) =
        (fun (v w : E n) => D.hessian u x v w - g.inner x v w) := by
      funext v w
      exact hB v w
    rw [heq, complexify20_sub (fun (v w : E n) => D.hessian u x v w)
      (fun (v w : E n) => g.inner x v w) i j,
      complexify20_metric_eq_zero huAt (hg x hx), sub_zero]
    exact (covariantHessian20_eq_hessian_complexification D hU hu hg hx hdet i j).symm
  have hrec (v w : E n) : hessianDefect D u x v w =
      2 * (∑ i, ∑ j, covariantHessian20 u x i j *
        complexCoord v i * complexCoord w j).re := by
    rw [← hB v w, antiJ_bilinear_reconstruction B hBJ]
    simp_rw [h20]
  unfold hessianDefectNormSq
  simp_rw [hrec]
  exact complex_tensor_real_norm_of_moments
    (fun a => complexCoord (g.orthonormalBasis x a))
    (inverseCoefficient u x) (covariantHessian20 u x)
    (metric_frame_complex_moment huAt hdet (hg x hx))
    (metric_frame_holomorphic_moment huAt hdet (hg x hx))

end KEBall
