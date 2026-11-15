import Drafts.KEBall.HessianNormBridge
import Drafts.KEBall.GradientRegularity

/-!
# First differential of the actual complex gradient norm

UNCOMPILED_DRAFT. Neither this file nor its inherited source-draft dependencies
have been promoted by the present source-only continuation. The endpoint
keeps the original IsSolution predicate and derives the first derivative of
q from metric compatibility, the concrete gradient dual, and the actual
(2,0)-Hessian bridge. No desired differential identity is an input field.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- The complex coordinates of the actual real metric gradient. -/
theorem metric_gradient_complex_coordinates {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (i : Fin n) :
    complexCoord (D.gradient u x) i =
      ∑ l : Fin n, inverseCoefficient u x i l *
        partialBar l (fun y => (u y : ℂ)) x := by
  have hd (v : E n) : g.inner x (D.gradient u x) v = fderiv ℝ u x v := by
    rw [D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    rfl
  have hw (v : E n) : hermitianRealification (complexHessian u x)
      (D.gradient u x) v =
      2 * (∑ k : Fin n,
        partialZ k (fun y => (u y : ℂ)) x * complexCoord v k).re := by
    rw [← realMetricForm_eq, ← hg, hd, fderiv_eq_wirtinger hu]
  have hc := congrFun (hermitianRealification_dual_vector
    (complexHessian u x) hdet
    (fun k => partialZ k (fun y => (u y : ℂ)) x) (D.gradient u x) hw) i
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Pi.star_apply, inverseCoefficient, partialBar_ofReal hu] using hc

/-- Reconstruction of the actual anti-J Hessian defect, with precisely the
paper's concrete (2,0) tensor. -/
theorem hessianDefect_eq_complex_reconstruction {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hdet : IsUnit (complexHessian u x).det)
    (v w : E n) :
    hessianDefect D u x v w =
      2 * (∑ i : Fin n, ∑ j : Fin n, covariantHessian20 u x i j *
        complexCoord v i * complexCoord w j).re := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  let B := retainedHessianDefectBilinear D u x
  have hB (a b : E n) : B a b = hessianDefect D u x a b :=
    retainedHessianDefectBilinear_apply D huAt a b
  have hBJ (a b : E n) : B (J a) (J b) = -B a b := by
    rw [hB, hB]
    exact hessianDefect_J_J D hU hu hg hx a b
  have h20 (i j : Fin n) : complexify20 (fun a b => B a b) i j =
      covariantHessian20 u x i j := by
    have heq : (fun (a b : E n) => B a b) =
        (fun (a b : E n) => D.hessian u x a b - g.inner x a b) := by
      funext a b
      exact hB a b
    rw [heq, complexify20_sub (fun (a b : E n) => D.hessian u x a b)
      (fun (a b : E n) => g.inner x a b) i j,
      complexify20_metric_eq_zero huAt (hg x hx), sub_zero]
    exact (covariantHessian20_eq_hessian_complexification D hU hu hg hx hdet i j).symm
  rw [← hB v w, antiJ_bilinear_reconstruction B hBJ]
  simp_rw [h20]

/-- Differentiating the proved local identity |grad_G u|²=2q gives dq(v)
= Hess_G u(v,grad_G u). The factor two cancels on both sides. -/
theorem fderiv_gradientNormSq_eq_hessian {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {U : Set (E n)}
    (hU : IsOpen U) (hUB : U ⊆ unitBall n)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v : E n) :
    fderiv ℝ (gradientNormSq u) x v = D.hessian u x v (D.gradient u x) := by
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hx))
  have hm : ContMDiffAt (𝓡 (2 * n)) 𝓘(ℝ, ℝ) ∞ u x :=
    contMDiffAt_iff_contDiffAt.mpr huAt
  have hNorm : (fun y => g.inner y (D.gradient u y) (D.gradient u y)) =ᶠ[𝓝 x]
      (fun y => 2 * gradientNormSq u y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact gradient_normSq_eq_twice_complex D
      ((hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hy))).differentiableAt
        (by simp))
      (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hUB hy))) (hg y hy)
  have hd := D.mvfderiv_gradient_normSq hm v
  simp only [mvfderiv, mfderiv_eq_fderiv] at hd
  change fderiv ℝ (fun y => g.inner y (D.gradient u y) (D.gradient u y)) x v =
    2 * D.hessian u x v (D.gradient u x) at hd
  rw [hNorm.fderiv_eq, fderiv_const_mul
    ((hu.gradientNormSq_contDiffAt (hUB hx)).differentiableAt (by simp))] at hd
  simp only [smul_apply, smul_eq_mul] at hd
  linarith

/-- The full real differential, expressed using the paper's tensor S. -/
theorem fderiv_gradientNormSq_eq_complex_contraction {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {U : Set (E n)}
    (hU : IsOpen U) (hUB : U ⊆ unitBall n)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v : E n) :
    fderiv ℝ (gradientNormSq u) x v = fderiv ℝ u x v +
      2 * (∑ i : Fin n, ∑ j : Fin n, covariantHessian20 u x i j *
        complexCoord v i * complexCoord (D.gradient u x) j).re := by
  have hrec := hessianDefect_eq_complex_reconstruction D hU
    (hu.contDiffOn_ball.mono hUB) hg hx
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hUB hx)))
    v (D.gradient u x)
  have hdu : g.inner x v (D.gradient u x) = fderiv ℝ u x v := by
    rw [g.symm x, D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    rfl
  rw [fderiv_gradientNormSq_eq_hessian hu D hU hUB hg hx]
  dsimp only [hessianDefect] at hrec
  rw [hdu] at hrec
  linarith

/-- First Wirtinger differential in a locally realized actual metric. -/
theorem partialZ_gradientNormSq_local {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {U : Set (E n)}
    (hU : IsOpen U) (hUB : U ⊆ unitBall n)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (j : Fin n) :
    partialZ j (fun y => (gradientNormSq u y : ℂ)) x =
      partialZ j (fun y => (u y : ℂ)) x +
        ∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
          covariantHessian20 u x j i * partialBar l (fun y => (u y : ℂ)) x := by
  let C : ℂ := ∑ i : Fin n,
    covariantHessian20 u x j i * complexCoord (D.gradient u x) i
  have hr : fderiv ℝ (gradientNormSq u) x (realDirection j) =
      fderiv ℝ u x (realDirection j) + 2 * C.re := by
    have h := fderiv_gradientNormSq_eq_complex_contraction hu D hU hUB hg hx
      (realDirection j)
    simpa [C, complexCoord_realDirection, mul_ite, ite_mul] using h
  have hsumI : (∑ i : Fin n, ∑ k : Fin n, covariantHessian20 u x i k *
      complexCoord (imagDirection j) i * complexCoord (D.gradient u x) k) =
      Complex.I * C := by
    calc
      _ = ∑ k : Fin n, covariantHessian20 u x j k * Complex.I *
          complexCoord (D.gradient u x) k := by
        simp [complexCoord_imagDirection, mul_ite, ite_mul]
      _ = _ := by
        simp only [C, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hi : fderiv ℝ (gradientNormSq u) x (imagDirection j) =
      fderiv ℝ u x (imagDirection j) - 2 * C.im := by
    have h := fderiv_gradientNormSq_eq_complex_contraction hu D hU hUB hg hx
      (imagDirection j)
    rw [hsumI] at h
    simpa [Complex.mul_re, Complex.I_re, Complex.I_im, sub_eq_add_neg] using h
  have huAt := (hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hx))).differentiableAt
    (by simp)
  have hqAt := (hu.gradientNormSq_contDiffAt (hUB hx)).differentiableAt (by simp)
  have hfirst : partialZ j (fun y => (gradientNormSq u y : ℂ)) x =
      partialZ j (fun y => (u y : ℂ)) x + C := by
    rw [partialZ_ofReal hqAt, partialZ_ofReal huAt, hr, hi]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hfirst]
  congr 1
  dsimp only [C]
  simp_rw [metric_gradient_complex_coordinates D huAt
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hUB hx))) (hg x hx)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The actual original solution satisfies q_j = u_j + g^{i bar l} S_{ji}u_bar_l.
All auxiliary metric witnesses are constructed and eliminated internally. -/
theorem IsSolution.partialZ_gradientNormSq {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) (j : Fin n) :
    partialZ j (fun y => (gradientNormSq u y : ℂ)) x =
      partialZ j (fun y => (u y : ℂ)) x +
        ∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
          covariantHessian20 u x j i * partialBar l (fun y => (u y : ℂ)) x := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  exact partialZ_gradientNormSq_local hu D hU hUB hg hxU j

end KEBall
