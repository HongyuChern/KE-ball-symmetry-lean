import Drafts.KEBall.AuxiliaryPIdentity
import Drafts.KEBall.AuxiliaryWIdentity
import Drafts.KEBall.ComplexBochner

/-!
# The actual P-Laplacian, Kato inequality and logarithmic subharmonicity

SOURCE_DRAFT_UNCOMPILED. This source integrates the concrete first derivatives,
Bochner identity, product rule and Gram contractions; none of those desired
identities is an extra hypothesis at an IsSolution endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators ComplexOrder

namespace KEBall

/-- Exponential differentiation in the second entry of the real pairing. -/
theorem gradientPairing_expWeight_right {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) :
    gradientPairing u h (expWeight u) x =
      -(expWeight u x / (n + 1 : ℝ)) * gradientPairing u h u x := by
  have hs : (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      partialZ i (fun y => (h y : ℂ)) x *
      partialBar j (fun y => (expWeight u y : ℂ)) x) =
      ((-(expWeight u x / (n + 1 : ℝ)) : ℝ) : ℂ) *
        (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
          partialZ i (fun y => (h y : ℂ)) x *
          partialBar j (fun y => (u y : ℂ)) x) := by
    simp_rw [partialBar_expWeight hu]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  unfold gradientPairing
  rw [hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The cross term in the product formula is obtained from the actual dq. -/
theorem IsSolution.gradientPairing_q_self {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    gradientPairing u (gradientNormSq u) u x = gradientNormSq u x +
      hermitianTensorRankOnePairing (inverseCoefficient u x) (covariantHessian20 u x)
        (fun i => partialZ i (fun y => (u y : ℂ)) x) := by
  have hud := (hu.2.1.contDiffAt
    (Metric.ball_subset_closedBall hx)).differentiableAt (by simp)
  simp only [gradientPairing]
  simp_rw [hu.partialZ_gradientNormSq hx, partialBar_ofReal hud]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Complex.add_re,
    gradientNormSq, hermitianTensorRankOnePairing, hermitianTensorContract,
    partialBar_ofReal hud]

/-- The actual defect norm expansion, after constructing a metric frame. -/
theorem IsSolution.auxiliaryDefectTensor_normSq {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    complexTensorNormSq u x (auxiliaryDefectTensor u x) =
      complexTensorNormSq u x (covariantHessian20 u x) -
        2 * (n + 1 : ℝ)⁻¹ *
          hermitianTensorRankOnePairing (inverseCoefficient u x) (covariantHessian20 u x)
            (fun i => partialZ i (fun y => (u y : ℂ)) x) +
        (n + 1 : ℝ)⁻¹ ^ 2 * gradientNormSq u x ^ 2 := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  have hm := metric_frame_complex_moment huAt
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)) (hg x hxU)
  have he := hermitianTensorDefect_expansion_of_gram (inverseCoefficient u x)
    (fun a => complexCoord (g.orthonormalBasis x a)) (covariantHessian20 u x)
    (fun i => partialZ i (fun y => (u y : ℂ)) x) (n + 1 : ℝ) hm
  simpa only [auxiliaryDefectTensor_eq_defect, complexTensorNormSq,
    hermitianTensorNormSq, hermitianCovectorNormSq, gradientNormSq,
    partialBar_ofReal (huAt.differentiableAt (by simp))] using he

/-- Exact P-Laplacian: the scalar cancellation consumes the proved concrete
product, weight, q-Bochner and q-first-derivative identities. -/
theorem IsSolution.auxiliaryP_laplacian {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    complexLaplacian u (auxiliaryP u) x = expWeight u x / (n + 1 : ℝ) *
      complexTensorNormSq u x (auxiliaryDefectTensor u x) := by
  have hxcl := Metric.ball_subset_closedBall hx
  have huAt := hu.2.1.contDiffAt hxcl
  have hqAt := hu.gradientNormSq_contDiffAt_closedBall hxcl
  have hEAt := contDiffAt_expWeight huAt
  let ψ : E n → ℝ := fun y => 1 + (n + 1 : ℝ)⁻¹ * gradientNormSq u y
  have hψAt : ContDiffAt ℝ ∞ ψ x :=
    contDiffAt_const.add (contDiffAt_const.mul hqAt)
  have hP : auxiliaryP u = fun y => expWeight u y * ψ y := by
    funext y
    dsimp [auxiliaryP, ψ]
    ring
  have hLψ : complexLaplacian u ψ x = (n + 1 : ℝ)⁻¹ *
      ((n : ℝ) + gradientNormSq u x +
        complexTensorNormSq u x (covariantHessian20 u x)) := by
    rw [complexLaplacian_const_add_const_mul u hqAt 1 (n + 1 : ℝ)⁻¹,
      hu.complex_bochner_identity hx]
  have hcross : gradientPairing u ψ (expWeight u) x =
      -expWeight u x / (n + 1 : ℝ) ^ 2 *
        (gradientNormSq u x + hermitianTensorRankOnePairing (inverseCoefficient u x)
          (covariantHessian20 u x) (fun i => partialZ i (fun y => (u y : ℂ)) x)) := by
    rw [gradientPairing_const_add_const_mul_left u (expWeight u)
      (hqAt.differentiableAt (by simp)) 1 (n + 1 : ℝ)⁻¹,
      gradientPairing_expWeight_right (huAt.differentiableAt (by simp)),
      hu.gradientPairing_q_self hx]
    have hk : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hk] <;> ring
  have hsym : gradientPairing u (expWeight u) ψ x =
      gradientPairing u ψ (expWeight u) x :=
    gradientPairing_symm (hu.2.2.1 x hx).isHermitian
      (hEAt.differentiableAt (by simp)) (hψAt.differentiableAt (by simp))
  rw [hu.auxiliaryDefectTensor_normSq hx, hP,
    complexLaplacian_mul u hEAt hψAt, hLψ, hu.complexLaplacian_expWeight hxcl,
    hsym]
  simp only [hcross]
  have hc := AuxiliaryPAlgebra.product_rule_cancellation
    (expWeight u x) (n + 1 : ℝ) (n : ℝ) (gradientNormSq u x)
    (complexTensorNormSq u x (covariantHessian20 u x))
    (hermitianTensorRankOnePairing (inverseCoefficient u x) (covariantHessian20 u x)
      (fun i => partialZ i (fun y => (u y : ℂ)) x)) (by positivity) rfl
  convert hc using 1 <;> dsimp [ψ] <;> ring

/-- Actual test-function norm agrees with the covector contraction. -/
theorem metricGradientNormSq_eq_hermitian {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hh : DifferentiableAt ℝ h x) :
    metricGradientNormSq u h x = hermitianCovectorNormSq (inverseCoefficient u x)
      (fun i => partialZ i (fun y => (h y : ℂ)) x) := by
  simp only [metricGradientNormSq, gradientPairing, hermitianCovectorNormSq,
    partialBar_ofReal hh]

theorem hermitianCovectorNormSq_real_mul {ι : Type*} [Fintype ι]
    (C : ι → ι → ℂ) (p : ι → ℂ) (a : ℝ) :
    hermitianCovectorNormSq C (fun i => (a : ℂ) * p i) =
      a ^ 2 * hermitianCovectorNormSq C p := by
  have hs : (∑ i, ∑ j, C i j * ((a : ℂ) * p i) * star ((a : ℂ) * p j)) =
      ((a ^ 2 : ℝ) : ℂ) * (∑ i, ∑ j, C i j * p i * star (p j)) := by
    simp only [Finset.mul_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  unfold hermitianCovectorNormSq
  rw [hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

set_option backward.isDefEq.respectTransparency true in
/-- The actual differential norm of P, with its complete coefficient. -/
theorem IsSolution.auxiliaryP_gradientNormSq {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    metricGradientNormSq u (auxiliaryP u) x = (expWeight u x / (n + 1 : ℝ)) ^ 2 *
      hermitianCovectorNormSq (inverseCoefficient u x)
        (hermitianTensorContract (inverseCoefficient u x) (auxiliaryDefectTensor u x)
          (fun i => partialZ i (fun y => (u y : ℂ)) x)) := by
  have hPDiff : DifferentiableAt ℝ (auxiliaryP u) x :=
    (hu.auxiliaryP_contDiffAt_closedBall
      (Metric.ball_subset_closedBall hx)).differentiableAt (by simp)
  have hnorm := metricGradientNormSq_eq_hermitian u hPDiff
  rw [hnorm]
  simp_rw [hu.partialZ_auxiliaryP_defect hx]
  simpa only [Complex.ofReal_div] using
    hermitianCovectorNormSq_real_mul (inverseCoefficient u x)
    (hermitianTensorContract (inverseCoefficient u x) (auxiliaryDefectTensor u x)
      (fun i => partialZ i (fun y => (u y : ℂ)) x))
    (expWeight u x / (n + 1 : ℝ))

theorem IsSolution.auxiliaryP_laplacian_nonneg {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    0 ≤ complexLaplacian u (auxiliaryP u) x := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  rw [hu.auxiliaryP_laplacian hx]
  apply mul_nonneg (div_nonneg (Real.exp_pos _).le (by positivity))
  exact complexTensorNormSq_nonneg
    (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)) (hg x hxU) _

/-- Kato for the actual P, not merely for an abstract finite-frame vector. -/
theorem IsSolution.auxiliaryP_kato {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    metricGradientNormSq u (auxiliaryP u) x ≤
      (auxiliaryP u x - expWeight u x) * complexLaplacian u (auxiliaryP u) x := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  have hK := inverseCoefficient_tensor_kato huAt
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)) (hg x hxU)
    (auxiliaryDefectTensor u x) (fun i => partialZ i (fun y => (u y : ℂ)) x)
  have hq : hermitianCovectorNormSq (inverseCoefficient u x)
      (fun i => partialZ i (fun y => (u y : ℂ)) x) = gradientNormSq u x := by
    simp only [hermitianCovectorNormSq, gradientNormSq,
      partialBar_ofReal (huAt.differentiableAt (by simp))]
  rw [hq] at hK
  rw [hu.auxiliaryP_gradientNormSq hx, hu.auxiliaryP_laplacian hx]
  calc
    _ ≤ (expWeight u x / (n + 1 : ℝ)) ^ 2 *
        (complexTensorNormSq u x (auxiliaryDefectTensor u x) * gradientNormSq u x) :=
      mul_le_mul_of_nonneg_left hK (sq_nonneg _)
    _ = _ := AuxiliaryPAlgebra.kato_factorization _ _ _ _

/-- The sharp quantitative lower bound after applying actual Kato. -/
theorem IsSolution.auxiliaryW_laplacian_lower {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    (expWeight u x - 1) / (auxiliaryP u x - 1) ^ 2 *
        complexLaplacian u (auxiliaryP u) x ≤ complexLaplacian u (auxiliaryW u) x := by
  rw [hu.complexLaplacian_auxiliaryW_closedBall hn (Metric.ball_subset_closedBall hx)]
  exact AuxiliaryPAlgebra.logarithmic_lower_bound
    (hu.auxiliaryP_gt_one_closedBall hn (Metric.ball_subset_closedBall hx))
    (hu.auxiliaryP_kato hx)

/-- The second conjunct of LogarithmicFluxStatement on the original solution
class. The integrated flux and global equality conclusion are not claimed. -/
theorem IsSolution.auxiliaryW_laplacian_nonneg {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    0 ≤ complexLaplacian u (auxiliaryW u) x := by
  rw [hu.complexLaplacian_auxiliaryW_closedBall hn (Metric.ball_subset_closedBall hx)]
  exact AuxiliaryPAlgebra.logarithmic_nonneg
    (hu.auxiliaryP_gt_one_closedBall hn (Metric.ball_subset_closedBall hx))
    (hu.expWeight_gt_one_unitBall (by omega) hx).le
    (hu.auxiliaryP_laplacian_nonneg hx) (hu.auxiliaryP_kato hx)

/-- A pointwise zero of the true log-Laplacian forces the actual defect norm
zero. This does not yet assert each tensor entry is zero or use an integral. -/
theorem IsSolution.auxiliaryW_zero_forces_defect_norm_zero {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (hz : complexLaplacian u (auxiliaryW u) x = 0) :
    complexTensorNormSq u x (auxiliaryDefectTensor u x) = 0 := by
  have hLP := AuxiliaryPAlgebra.logarithmic_zero_forces_zero
    (hu.auxiliaryP_gt_one_closedBall hn (Metric.ball_subset_closedBall hx))
    (hu.expWeight_gt_one_unitBall (by omega) hx)
    (hu.auxiliaryP_laplacian_nonneg hx) (hu.auxiliaryP_kato hx)
    ((hu.complexLaplacian_auxiliaryW_closedBall hn
      (Metric.ball_subset_closedBall hx)).symm.trans hz)
  rw [hu.auxiliaryP_laplacian hx] at hLP
  exact (mul_eq_zero.mp hLP).resolve_left
    (ne_of_gt (div_pos (Real.exp_pos _) (by positivity)))

#print axioms IsSolution.auxiliaryP_laplacian
#print axioms IsSolution.auxiliaryP_kato
#print axioms IsSolution.auxiliaryW_laplacian_nonneg

end KEBall
