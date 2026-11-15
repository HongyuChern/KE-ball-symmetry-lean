import Drafts.KEBall.AuxiliaryPAlgebra
import Drafts.KEBall.HessianNormBridge

/-!
# Kato contraction in the manuscript's inverse-metric convention

Stage06 source draft: NOT compiled and NOT kernel checked.
The generic result uses a Gram factor C(i,k)=Σa c(a,i) conj(c(a,k)).
The concrete metric corollary derives this factor from the actual real
orthonormal frame through `metric_frame_complex_moment`. No normal
holomorphic coordinates, target norm identity, or Kato bound is assumed.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff
noncomputable section

namespace KEBall

def hermitianCovectorNormSq {ι : Type*} [Fintype ι]
    (C : ι → ι → ℂ) (p : ι → ℂ) : ℝ :=
  (∑ i, ∑ k, C i k * p i * star (p k)).re

def hermitianTensorNormSq {ι : Type*} [Fintype ι]
    (C T : ι → ι → ℂ) : ℝ :=
  (∑ i, ∑ j, ∑ k, ∑ l,
    C i k * C j l * T i j * star (T k l)).re

def hermitianTensorContract {ι : Type*} [Fintype ι]
    (C T : ι → ι → ℂ) (p : ι → ℂ) (j : ι) : ℂ :=
  ∑ i, ∑ l, C i l * T j i * star (p l)

def hermitianTensorRankOnePairing {ι : Type*} [Fintype ι]
    (C S : ι → ι → ℂ) (p : ι → ℂ) : ℝ :=
  (∑ j, ∑ l, C j l * hermitianTensorContract C S p j * star (p l)).re

def gramFrameCovector {α ι : Type*} [Fintype ι]
    (c : α → ι → ℂ) (p : ι → ℂ) (a : α) : ℂ := ∑ i, p i * c a i

def gramFrameTensor {α ι : Type*} [Fintype ι]
    (c : α → ι → ℂ) (T : ι → ι → ℂ) (a b : α) : ℂ :=
  ∑ i, ∑ j, T i j * c a i * c b j

theorem complex_norm_sq_eq_re_mul_star (z : ℂ) :
    ‖z‖ ^ 2 = (z * star z).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A Gram identity, not an assumed isometry of covector norms. -/
theorem gramFrameCovector_normSq {α ι : Type*} [Fintype α] [Fintype ι]
    (C : ι → ι → ℂ) (c : α → ι → ℂ) (p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    AuxiliaryPAlgebra.vectorNormSq (gramFrameCovector c p) =
      hermitianCovectorNormSq C p := by
  classical
  have hstar (a : α) : star (∑ i, p i * c a i) =
      ∑ i, star (p i) * star (c a i) := by
    simp only [star_sum, star_mul, mul_comm]
  have h := sum_mul_linear_forms p (fun i => star (p i)) c
    (fun a i => star (c a i))
  simp only [hC] at h
  unfold AuxiliaryPAlgebra.vectorNormSq gramFrameCovector hermitianCovectorNormSq
  simp_rw [complex_norm_sq_eq_re_mul_star, hstar]
  rw [← Complex.re_sum, h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The unprojected complex contraction is real. This is needed before
factoring a rank-one tensor in the formula for the actual derivative of P. -/
theorem gram_covector_sum_eq_real {α ι : Type*} [Fintype α] [Fintype ι]
    (C : ι → ι → ℂ) (c : α → ι → ℂ) (p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    (∑ i, ∑ k, C i k * p i * star (p k)) =
      (hermitianCovectorNormSq C p : ℂ) := by
  classical
  have him (z : ℂ) : (z * star z).im = 0 := by
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hstar (a : α) : star (∑ i, p i * c a i) =
      ∑ i, star (p i) * star (c a i) := by
    simp only [star_sum, star_mul, mul_comm]
  have h := sum_mul_linear_forms p (fun i => star (p i)) c
    (fun a i => star (c a i))
  simp only [hC] at h
  have hs : (∑ i, ∑ k, C i k * p i * star (p k)) =
      ∑ a, (∑ i, p i * c a i) * star (∑ i, p i * c a i) := by
    simp_rw [hstar]
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply Complex.ext
  · rfl
  · rw [hs]
    simp only [Complex.im_sum, him, Finset.sum_const_zero, Complex.ofReal_im]

/-- Sesquilinear Gram transport, with the first covector unconjugated. -/
theorem gramFrameCovector_pair {α ι : Type*} [Fintype α] [Fintype ι]
    (C : ι → ι → ℂ) (c : α → ι → ℂ) (r p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    (∑ a, gramFrameCovector c r a * star (gramFrameCovector c p a)) =
      ∑ i, ∑ k, C i k * r i * star (p k) := by
  classical
  have hs (a : α) : star (gramFrameCovector c p a) =
      ∑ k, star (p k) * star (c a k) := by
    simp only [gramFrameCovector, star_sum, star_mul, mul_comm]
  have h := sum_mul_linear_forms r (fun k => star (p k)) c
    (fun a k => star (c a k))
  simp only [hC] at h
  simp_rw [hs]
  unfold gramFrameCovector
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The tensor norm is the product-frame square sum, with both inverse
indices in the exact order C(i,k) C(j,l) used by the frozen specification. -/
theorem gramFrameTensor_normSq {α ι : Type*} [Fintype α] [Fintype ι]
    (C : ι → ι → ℂ) (c : α → ι → ℂ) (T : ι → ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    (∑ a, ∑ b, ‖gramFrameTensor c T a b‖ ^ 2) =
      hermitianTensorNormSq C T := by
  classical
  let d : (α × α) → (ι × ι) → ℂ := fun a i => c a.1 i.1 * c a.2 i.2
  let B : (ι × ι) → (ι × ι) → ℂ := fun i k => C i.1 k.1 * C i.2 k.2
  have hd (i k : ι × ι) :
      (∑ a : α × α, d a i * star (d a k)) = B i k := by
    calc
      _ = ∑ a : α × α, (c a.1 i.1 * star (c a.1 k.1)) *
          (c a.2 i.2 * star (c a.2 k.2)) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [d]
        rw [map_mul]
        ring
      _ = _ := by
        rw [sum_prod_pair_factor (fun a => c a i.1 * star (c a k.1))
          (fun a => c a i.2 * star (c a k.2)), hC, hC]
  have h := gramFrameCovector_normSq B d (fun i => T i.1 i.2) hd
  simpa only [AuxiliaryPAlgebra.vectorNormSq, gramFrameCovector,
    hermitianCovectorNormSq, hermitianTensorNormSq, gramFrameTensor,
    Fintype.sum_prod_type, d, B, mul_assoc] using h

/-- Defect formation commutes with the actual Gram frame, including both
covariant tensor slots. This has no Gram hypothesis because it is linear. -/
theorem gramFrameTensor_defect {α ι : Type*} [Fintype ι]
    (c : α → ι → ℂ) (S : ι → ι → ℂ) (p : ι → ℂ) (k : ℝ) (a b : α) :
    gramFrameTensor c (AuxiliaryPAlgebra.defect S p k) a b =
      AuxiliaryPAlgebra.defect (gramFrameTensor c S) (gramFrameCovector c p) k a b := by
  classical
  simp only [gramFrameTensor, gramFrameCovector, AuxiliaryPAlgebra.defect,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hermitianTensorDefect_normSq_of_gram {α ι : Type*}
    [Fintype α] [Fintype ι] (C : ι → ι → ℂ) (c : α → ι → ℂ)
    (S : ι → ι → ℂ) (p : ι → ℂ) (k : ℝ)
    (hC : ∀ i l, (∑ a, c a i * star (c a l)) = C i l) :
    hermitianTensorNormSq C (AuxiliaryPAlgebra.defect S p k) =
      AuxiliaryPAlgebra.tensorNormSq
        (AuxiliaryPAlgebra.defect (gramFrameTensor c S) (gramFrameCovector c p) k) := by
  rw [← gramFrameTensor_normSq C c _ hC]
  simp_rw [gramFrameTensor_defect]
  unfold AuxiliaryPAlgebra.tensorNormSq
  exact Finset.sum_comm

/-- The actual coordinate contraction transforms to the Euclidean frame
contraction. The proof expands all sums; it assumes only the Gram identity. -/
theorem gramFrameCovector_contract {α ι : Type*} [Fintype α] [Fintype ι]
    (C : ι → ι → ℂ) (c : α → ι → ℂ) (T : ι → ι → ℂ) (p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) (a : α) :
    gramFrameCovector c (hermitianTensorContract C T p) a =
      ∑ b, gramFrameTensor c T a b * star (gramFrameCovector c p b) := by
  classical
  let q : ι → ℂ := fun i => ∑ j, T j i * c a j
  have ht (b : α) : gramFrameTensor c T a b = ∑ i, q i * c b i := by
    dsimp [gramFrameTensor, q]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hp (b : α) : star (gramFrameCovector c p b) =
      ∑ l, star (p l) * star (c b l) := by
    simp only [gramFrameCovector, star_sum, star_mul, mul_comm]
  have h := sum_mul_linear_forms q (fun l => star (p l)) c
    (fun b l => star (c b l))
  simp only [hC] at h
  calc
    _ = ∑ i, ∑ l, q i * star (p l) * C i l := by
      dsimp [gramFrameCovector, hermitianTensorContract, q]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simpa only [ht, hp] using h.symm

theorem gramFrameTensor_rankOnePairing {α ι : Type*}
    [Fintype α] [Fintype ι] (C : ι → ι → ℂ) (c : α → ι → ℂ)
    (S : ι → ι → ℂ) (p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    AuxiliaryPAlgebra.rankOnePairing (gramFrameTensor c S) (gramFrameCovector c p) =
      hermitianTensorRankOnePairing C S p := by
  classical
  unfold hermitianTensorRankOnePairing
  rw [← gramFrameCovector_pair C c (hermitianTensorContract C S p) p hC]
  simp_rw [gramFrameCovector_contract C c S p hC]
  simp only [AuxiliaryPAlgebra.rankOnePairing, Finset.sum_mul, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [star_mul]
  ring

/-- Coordinate defect expansion, with the cross term expressed using the
same row contraction that occurs in the differential formula for q_j. -/
theorem hermitianTensorDefect_expansion_of_gram {α ι : Type*}
    [Fintype α] [Fintype ι] (C : ι → ι → ℂ) (c : α → ι → ℂ)
    (S : ι → ι → ℂ) (p : ι → ℂ) (k : ℝ)
    (hC : ∀ i l, (∑ a, c a i * star (c a l)) = C i l) :
    hermitianTensorNormSq C (AuxiliaryPAlgebra.defect S p k) =
      hermitianTensorNormSq C S - 2 * k⁻¹ * hermitianTensorRankOnePairing C S p +
        k⁻¹ ^ 2 * hermitianCovectorNormSq C p ^ 2 := by
  have hT : AuxiliaryPAlgebra.tensorNormSq (gramFrameTensor c S) =
      hermitianTensorNormSq C S := by
    unfold AuxiliaryPAlgebra.tensorNormSq
    rw [Finset.sum_comm]
    exact gramFrameTensor_normSq C c S hC
  rw [hermitianTensorDefect_normSq_of_gram C c S p k hC,
    AuxiliaryPAlgebra.defect_normSq, hT,
    gramFrameTensor_rankOnePairing C c S p hC, gramFrameCovector_normSq C c p hC]

theorem hermitianCovectorNormSq_nonneg_of_gram {α ι : Type*}
    [Fintype α] [Fintype ι] (C : ι → ι → ℂ) (c : α → ι → ℂ) (p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    0 ≤ hermitianCovectorNormSq C p := by
  rw [← gramFrameCovector_normSq C c p hC]
  exact AuxiliaryPAlgebra.vectorNormSq_nonneg _

theorem hermitianTensorNormSq_nonneg_of_gram {α ι : Type*}
    [Fintype α] [Fintype ι] (C : ι → ι → ℂ) (c : α → ι → ℂ) (T : ι → ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    0 ≤ hermitianTensorNormSq C T := by
  rw [← gramFrameTensor_normSq C c T hC]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Sharp Kato inequality for an arbitrary complex Gram matrix. No strict
positivity or rank condition is needed once the Gram factor is supplied. -/
theorem hermitianTensorContract_kato_of_gram {α ι : Type*}
    [Fintype α] [Fintype ι] (C : ι → ι → ℂ) (c : α → ι → ℂ)
    (T : ι → ι → ℂ) (p : ι → ℂ)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k) :
    hermitianCovectorNormSq C (hermitianTensorContract C T p) ≤
      hermitianTensorNormSq C T * hermitianCovectorNormSq C p := by
  classical
  calc
    _ = ∑ a, ‖∑ b, gramFrameTensor c T a b *
        star (gramFrameCovector c p b)‖ ^ 2 := by
      rw [← gramFrameCovector_normSq C c _ hC]
      unfold AuxiliaryPAlgebra.vectorNormSq
      simp_rw [gramFrameCovector_contract C c T p hC]
    _ ≤ ∑ a, (∑ b, ‖gramFrameTensor c T a b‖ ^ 2) *
        AuxiliaryPAlgebra.vectorNormSq (gramFrameCovector c p) := by
      apply Finset.sum_le_sum
      intro a _
      exact AuxiliaryPAlgebra.complex_sum_sq_le (gramFrameTensor c T a)
        (gramFrameCovector c p)
    _ = (∑ a, ∑ b, ‖gramFrameTensor c T a b‖ ^ 2) *
        AuxiliaryPAlgebra.vectorNormSq (gramFrameCovector c p) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [gramFrameTensor_normSq C c T hC, gramFrameCovector_normSq C c p hC]

/-- Application to the actual metric, preserving the inverse transpose.
The frame moment is derived from g rather than supplied as an extra input. -/
theorem inverseCoefficient_tensor_kato {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (T : Fin n → Fin n → ℂ) (p : Fin n → ℂ) :
    hermitianCovectorNormSq (inverseCoefficient u x)
        (hermitianTensorContract (inverseCoefficient u x) T p) ≤
      complexTensorNormSq u x T * hermitianCovectorNormSq (inverseCoefficient u x) p := by
  exact hermitianTensorContract_kato_of_gram (inverseCoefficient u x)
    (fun a => complexCoord (g.orthonormalBasis x a)) T p
    (metric_frame_complex_moment hu hdet hg)

/-- Positivity of the actual tensor norm, for every tensor, not only Hessians. -/
theorem complexTensorNormSq_nonneg {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w)
    (T : Fin n → Fin n → ℂ) : 0 ≤ complexTensorNormSq u x T := by
  exact hermitianTensorNormSq_nonneg_of_gram (inverseCoefficient u x)
    (fun a => complexCoord (g.orthonormalBasis x a)) T
    (metric_frame_complex_moment hu hdet hg)

/-- Complex-valued identity with q, before taking real parts. -/
theorem inverseCoefficient_gradient_pairing_eq {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w) :
    (∑ i, ∑ k, inverseCoefficient u x i k *
      partialZ i (fun y => (u y : ℂ)) x *
      star (partialZ k (fun y => (u y : ℂ)) x)) = (gradientNormSq u x : ℂ) := by
  have h := gram_covector_sum_eq_real (inverseCoefficient u x)
    (fun a => complexCoord (g.orthonormalBasis x a))
    (fun i => partialZ i (fun y => (u y : ℂ)) x)
    (metric_frame_complex_moment hu hdet hg)
  simpa only [hermitianCovectorNormSq, gradientNormSq,
    partialBar_ofReal (hu.differentiableAt (by simp))] using h

end KEBall
