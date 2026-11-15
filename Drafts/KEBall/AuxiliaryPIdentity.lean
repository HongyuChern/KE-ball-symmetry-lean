import Drafts.KEBall.GradientNormDifferential
import Drafts.KEBall.ComplexProductLog
import Drafts.KEBall.HermitianContraction

/-!
# First derivative of the actual P-function and its actual tensor defect

UNCOMPILED_DRAFT. All quantities are concrete derivatives or contractions of
the unchanged potential. No first-derivative formula is assumed at an
IsSolution endpoint. This file does not prove the Laplacian, logarithmic
flux, or final symmetry theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped ContDiff Topology BigOperators

namespace KEBall

/-- The actual tensor S - kappa^{-1} partial u tensor partial u. -/
noncomputable def auxiliaryDefectTensor {n : ℕ} (u : E n → ℝ) (x : E n)
    (i j : Fin n) : ℂ :=
  covariantHessian20 u x i j - (((n + 1 : ℝ)⁻¹ : ℝ) : ℂ) *
    (partialZ i (fun y => (u y : ℂ)) x * partialZ j (fun y => (u y : ℂ)) x)

/-- Exact interface to the pre-existing finite-dimensional defect algebra. -/
theorem auxiliaryDefectTensor_eq_defect {n : ℕ} (u : E n → ℝ) (x : E n) :
    auxiliaryDefectTensor u x =
      AuxiliaryPAlgebra.defect (covariantHessian20 u x)
        (fun i => partialZ i (fun y => (u y : ℂ)) x) (n + 1 : ℝ) := rfl

/-- The first product cancellation uses the actual derivatives of E and q. -/
theorem IsSolution.partialZ_auxiliaryP {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) (j : Fin n) :
    partialZ j (fun y => (auxiliaryP u y : ℂ)) x =
      (expWeight u x / (n + 1 : ℝ) : ℂ) *
        ((∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
          covariantHessian20 u x j i * partialBar l (fun y => (u y : ℂ)) x) -
          (gradientNormSq u x / (n + 1 : ℝ) : ℂ) *
            partialZ j (fun y => (u y : ℂ)) x) := by
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  have hqAt := hu.gradientNormSq_contDiffAt hx
  have hE := (contDiffAt_expWeight huAt).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ
      (fun y => 1 + (n + 1 : ℝ)⁻¹ * gradientNormSq u y) x :=
    (contDiffAt_const.add (contDiffAt_const.mul hqAt)).differentiableAt (by simp)
  have hP : auxiliaryP u =
      fun y => expWeight u y * (1 + (n + 1 : ℝ)⁻¹ * gradientNormSq u y) := by
    funext y
    unfold auxiliaryP
    ring
  rw [hP, partialZ_ofReal_mul hE hH,
    partialZ_expWeight (huAt.differentiableAt (by simp)),
    partialZ_const_add_const_mul (hqAt.differentiableAt (by simp)) 1 (n + 1 : ℝ)⁻¹,
    hu.partialZ_gradientNormSq hx]
  push_cast
  ring

/-- The actual rank-one contraction equals q times the covector. Reality of
the Hermitian self-pairing is proved from the constructed metric frame. -/
theorem IsSolution.auxiliaryDefectTensor_contract {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) (j : Fin n) :
    hermitianTensorContract (inverseCoefficient u x) (auxiliaryDefectTensor u x)
        (fun i => partialZ i (fun y => (u y : ℂ)) x) j =
      (∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
        covariantHessian20 u x j i * partialBar l (fun y => (u y : ℂ)) x) -
      (gradientNormSq u x / (n + 1 : ℝ) : ℂ) *
        partialZ j (fun y => (u y : ℂ)) x := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  have hQ := inverseCoefficient_gradient_pairing_eq huAt
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)) (hg x hxU)
  unfold hermitianTensorContract auxiliaryDefectTensor
  calc
    _ = (∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
          covariantHessian20 u x j i *
          star (partialZ l (fun y => (u y : ℂ)) x)) -
        (((n + 1 : ℝ)⁻¹ : ℝ) : ℂ) * partialZ j (fun y => (u y : ℂ)) x *
          (∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
            partialZ i (fun y => (u y : ℂ)) x *
            star (partialZ l (fun y => (u y : ℂ)) x)) := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [hQ]
      simp only [partialBar_ofReal (huAt.differentiableAt (by simp))]
      push_cast
      ring

/-- The exact frozen tensor formula for the actual first derivative of P. -/
theorem IsSolution.partialZ_auxiliaryP_defect {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) (j : Fin n) :
    partialZ j (fun y => (auxiliaryP u y : ℂ)) x =
      (expWeight u x / (n + 1 : ℝ) : ℂ) *
        hermitianTensorContract (inverseCoefficient u x) (auxiliaryDefectTensor u x)
          (fun i => partialZ i (fun y => (u y : ℂ)) x) j := by
  rw [hu.partialZ_auxiliaryP hx, hu.auxiliaryDefectTensor_contract hx]

end KEBall
