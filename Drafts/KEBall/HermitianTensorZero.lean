import Drafts.KEBall.AuxiliaryPLaplacian

/-!
# Vanishing of the actual positive-metric tensor norm

SOURCE_DRAFT_UNCOMPILED. The Gram frame is injective because the transpose
of its Gram matrix is strictly positive definite. Both tensor slots are
recovered by this injectivity. No such claim is made for a merely positive
semidefinite Gram matrix. The actual IsSolution endpoints construct the
frame and obtain positivity from the original complex Hessian.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff ComplexOrder
noncomputable section

namespace KEBall

/-- The index transpose in the manuscript's covector norm is explicit. -/
theorem hermitianCovectorNormSq_eq_transpose_pairing {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℂ) (p : ι → ℂ) :
    hermitianCovectorNormSq C p = (star p ⬝ᵥ (C.transpose.mulVec p)).re := by
  unfold hermitianCovectorNormSq
  rw [Finset.sum_comm]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum,
    Pi.star_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hermitianCovectorNormSq_pos_of_transpose_posDef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℂ) (hpos : C.transpose.PosDef) (p : ι → ℂ) (hp : p ≠ 0) :
    0 < hermitianCovectorNormSq C p := by
  rw [hermitianCovectorNormSq_eq_transpose_pairing]
  exact hpos.re_dotProduct_pos hp

/-- A vanishing Gram-frame covector has zero original coordinates only
under strict positivity. The Gram identity alone does not imply this. -/
theorem gramFrameCovector_eq_zero_of_posDef {α ι : Type*}
    [Fintype α] [Fintype ι] (C : Matrix ι ι ℂ) (c : α → ι → ℂ)
    (hpos : C.transpose.PosDef)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k)
    (p : ι → ℂ) (hp : ∀ a, gramFrameCovector c p a = 0) : p = 0 := by
  classical
  by_contra hp0
  have hstrict := hermitianCovectorNormSq_pos_of_transpose_posDef C hpos p hp0
  have hzero : hermitianCovectorNormSq C p = 0 := by
    rw [← gramFrameCovector_normSq C c p hC]
    simp [AuxiliaryPAlgebra.vectorNormSq, hp]
  rw [hzero] at hstrict
  exact (lt_irrefl (0 : ℝ)) hstrict

/-- Recover both slots of an arbitrary complex tensor from its frame.
There is no symmetry hypothesis on T. -/
theorem hermitianTensorNormSq_eq_zero_iff_of_gram {α ι : Type*}
    [Fintype α] [Fintype ι] (C : Matrix ι ι ℂ) (c : α → ι → ℂ)
    (hpos : C.transpose.PosDef)
    (hC : ∀ i k, (∑ a, c a i * star (c a k)) = C i k)
    (T : ι → ι → ℂ) :
    hermitianTensorNormSq C T = 0 ↔ ∀ i j, T i j = 0 := by
  classical
  constructor
  · intro hzero
    have hframeNorm : AuxiliaryPAlgebra.tensorNormSq (gramFrameTensor c T) = 0 := by
      unfold AuxiliaryPAlgebra.tensorNormSq
      rw [Finset.sum_comm, gramFrameTensor_normSq C c T hC]
      exact hzero
    have hframe := (AuxiliaryPAlgebra.tensorNormSq_eq_zero_iff
      (gramFrameTensor c T)).mp hframeNorm
    have hrow (a : α) : (fun j => ∑ i, T i j * c a i) = 0 := by
      apply gramFrameCovector_eq_zero_of_posDef C c hpos hC
      intro b
      have hid : gramFrameCovector c (fun j => ∑ i, T i j * c a i) b =
          gramFrameTensor c T a b := by
        unfold gramFrameCovector gramFrameTensor
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hid]
      exact hframe a b
    intro i j
    have hcol : (fun i => T i j) = 0 := by
      apply gramFrameCovector_eq_zero_of_posDef C c hpos hC
      intro a
      exact congrFun (hrow a) j
    exact congrFun hcol i
  · intro hzero
    simp only [hermitianTensorNormSq, hzero, zero_mul, mul_zero,
      star_zero, Finset.sum_const_zero, Complex.zero_re]

/-- The actual inverse-metric tensor norm detects all tensor coefficients.
Strict positivity and the Gram frame come from the original solution. -/
theorem IsSolution.complexTensorNormSq_eq_zero_iff {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (T : Fin n → Fin n → ℂ) :
    complexTensorNormSq u x T = 0 ↔ ∀ i j, T i j = 0 := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  have hm := metric_frame_complex_moment huAt
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)) (hg x hxU)
  have hpos : (Matrix.transpose (inverseCoefficient u x)).PosDef := by
    change ((complexHessian u x)⁻¹).PosDef
    exact (hu.2.2.1 x hx).inv
  exact hermitianTensorNormSq_eq_zero_iff_of_gram (inverseCoefficient u x)
    (fun a => complexCoord (g.orthonormalBasis x a)) hpos hm T

/-- Pointwise zero of the actual log-Laplacian kills each actual defect
coefficient. This theorem does not assume a zero integral. -/
theorem IsSolution.auxiliaryW_zero_forces_auxiliaryDefectTensor_zero {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n)
    (hz : complexLaplacian u (auxiliaryW u) x = 0) :
    ∀ i j, auxiliaryDefectTensor u x i j = 0 := by
  exact (hu.complexTensorNormSq_eq_zero_iff hx (auxiliaryDefectTensor u x)).mp
    (hu.auxiliaryW_zero_forces_defect_norm_zero hn hx hz)

/-- The exact pointwise Hessian identity in the frozen Proposition 3.1,
including the complex inverse and the original multiplication order. -/
theorem IsSolution.auxiliaryW_zero_forces_hessian_identity {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n)
    (hz : complexLaplacian u (auxiliaryW u) x = 0) (i j : Fin n) :
    covariantHessian20 u x i j = (n + 1 : ℂ)⁻¹ *
      partialZ i (fun y => (u y : ℂ)) x * partialZ j (fun y => (u y : ℂ)) x := by
  have h := hu.auxiliaryW_zero_forces_auxiliaryDefectTensor_zero hn hx hz i j
  unfold auxiliaryDefectTensor at h
  have hk : (((n + 1 : ℝ)⁻¹ : ℝ) : ℂ) = (n + 1 : ℂ)⁻¹ := by
    push_cast <;> rfl
  simpa only [hk, mul_assoc] using (sub_eq_zero.mp h)

#print axioms IsSolution.complexTensorNormSq_eq_zero_iff
#print axioms IsSolution.auxiliaryW_zero_forces_auxiliaryDefectTensor_zero
#print axioms IsSolution.auxiliaryW_zero_forces_hessian_identity

end KEBall
