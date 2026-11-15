import KEBall.HermitianRealification
import KEBall.RadialCoordinates
import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient

/-!
# The gradient normalization for the actual Hessian metric

The real directional derivative and the metric dual determine the complex
coordinates of the gradient. No norm-identification hypothesis is assumed.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Manifold

namespace KEBall
open KEBallProbe

theorem interleaved_decomposition {n : ℕ} (v : E n) :
    (∑ i : Fin n, (v (realIndex i) • realDirection i +
      v (imagIndex i) • imagDirection i)) = v := by
  have h := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr v
  rw [← (interleavedEquiv n).sum_comp] at h
  simpa [Fintype.sum_prod_type, Fin.sum_univ_two, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, realDirection, imagDirection] using h

theorem rd_ofReal {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (v : E n) :
    rd v (fun y => (u y : ℂ)) x = (fderiv ℝ u x v : ℝ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => (u y : ℂ)) _ x at h
  rw [rd, h.fderiv]
  rfl

theorem partialZ_ofReal {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    partialZ i (fun y => (u y : ℂ)) x =
      (2 : ℂ)⁻¹ * ((fderiv ℝ u x (realDirection i) : ℝ) -
        Complex.I * (fderiv ℝ u x (imagDirection i) : ℝ)) := by
  simp only [partialZ, dz, rd_ofReal hu]

theorem partialBar_ofReal {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    partialBar i (fun y => (u y : ℂ)) x =
      star (partialZ i (fun y => (u y : ℂ)) x) := by
  simp only [partialBar, dz, rd_ofReal hu, map_neg, partialZ_ofReal hu]
  simp

theorem fderiv_eq_wirtinger {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (v : E n) :
    fderiv ℝ u x v =
      2 * (∑ i : Fin n, partialZ i (fun y => (u y : ℂ)) x * complexCoord v i).re := by
  nth_rw 1 [← interleaved_decomposition v]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, Complex.re_sum,
    Finset.mul_sum, partialZ_ofReal hu]
  apply Finset.sum_congr rfl
  intro i _
  simp [complexCoord, Complex.mul_re, Complex.mul_im]
  ring

theorem hermitianRealification_realDirection {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : E n) (j : Fin n) :
    hermitianRealification A v (realDirection j) =
      2 * (∑ i : Fin n, A i j * complexCoord v i).re := by
  rw [hermitianRealification_apply]
  simp [complexCoord_realDirection]

theorem hermitianRealification_imagDirection {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : E n) (j : Fin n) :
    hermitianRealification A v (imagDirection j) =
      2 * (∑ i : Fin n, A i j * complexCoord v i).im := by
  rw [hermitianRealification_apply]
  simp only [complexCoord_imagDirection]
  simp [apply_ite, ← Finset.sum_mul]

theorem hermitianRealification_dual_coordinates {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (p : Fin n → ℂ) (w : E n)
    (hw : ∀ v : E n, hermitianRealification A w v =
      2 * (∑ i : Fin n, p i * complexCoord v i).re) (j : Fin n) :
    (∑ i : Fin n, A i j * complexCoord w i) = star (p j) := by
  have hr := hw (realDirection j)
  have hi := hw (imagDirection j)
  rw [hermitianRealification_realDirection] at hr
  rw [hermitianRealification_imagDirection] at hi
  simp [complexCoord_realDirection] at hr
  simp [complexCoord_imagDirection, Complex.mul_re, Complex.mul_im] at hi
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    simpa only [Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib] using hr
  · simp only [Complex.star_def, Complex.conj_im]
    simp only [Complex.im_sum, Complex.mul_im]
    linarith

theorem hermitianRealification_dual_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (p : Fin n → ℂ) (w : E n)
    (hw : ∀ v : E n, hermitianRealification A w v =
      2 * (∑ i : Fin n, p i * complexCoord v i).re) :
    hermitianRealification A w w =
      2 * (∑ i : Fin n, ∑ j : Fin n, A⁻¹ j i * p i * star (p j)).re := by
  have hrow : A.transpose.mulVec (complexCoord w) = star p := by
    funext j
    exact hermitianRealification_dual_coordinates A p w hw j
  have hcoord : complexCoord w = A⁻¹.transpose.mulVec (star p) := by
    have ht := congrArg (A⁻¹.transpose.mulVec) hrow
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv A hA, Matrix.transpose_one, Matrix.one_mulVec] at ht
    exact ht
  rw [hw w, hcoord]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.star_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gradient_normSq_eq_twice_complex {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w) :
    g.inner x (D.gradient u x) (D.gradient u x) = 2 * gradientNormSq u x := by
  have hd (v : E n) : g.inner x (D.gradient u x) v = fderiv ℝ u x v := by
    rw [D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    rfl
  have hdual (v : E n) : hermitianRealification (complexHessian u x)
      (D.gradient u x) v =
      2 * (∑ i : Fin n, partialZ i (fun y => (u y : ℂ)) x * complexCoord v i).re := by
    rw [← realMetricForm_eq, ← hg, hd, fderiv_eq_wirtinger hu]
  have h := hermitianRealification_dual_norm (complexHessian u x) hdet
    (fun i => partialZ i (fun y => (u y : ℂ)) x) (D.gradient u x) hdual
  rw [hg, realMetricForm_eq, h]
  simp only [gradientNormSq, inverseCoefficient, partialBar_ofReal hu]

end KEBall
