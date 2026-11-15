import KEBall.DirichletExponentialDifferences
import KEBall.DirichletClosedFlowEnergy
import KEBall.DirichletRemainderTame

/-! The exponential of the actual potential has a lower-order density
source estimate for every fixed rotation-difference order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem exists_integral_exp_difference_sq_le_potential {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {u : E n → ℝ}
    (hu : ContinuousOn u (closedUnitBall n)) (a c : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ (R : E n ≃ₗᵢ[ℝ] E n) (t : ℝ), t ≠ 0 →
      (∫ x in unitBall n,
        (dirichletIteratedOrthogonalDifference R t (fun y => c * Real.exp (a * u y)) k x) ^ 2 ∂volume0 n) ≤
      C * ∫ x in unitBall n, (dirichletIteratedOrthogonalDifference R t u k x) ^ 2 ∂volume0 n := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hu
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let v (x : E n) := B⁻¹ * u x
  have hv : ContinuousOn v (closedUnitBall n) := hu.const_mul _
  have hvBound (x : E n) (hx : x ∈ unitBall n) : |v x| ≤ 1 := by
    have hU : |u x| ≤ B := (hM x (ball_subset_closedBall hx)).trans
      (by change M ≤ |M| + 1; linarith only [le_abs_self M])
    dsimp only [v]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
    exact (mul_le_mul_of_nonneg_left hU (inv_nonneg.mpr hB.le)).trans_eq (inv_mul_cancel₀ hB.ne')
  let K : ℝ := |c| * (Real.exp ((2 : ℝ) ^ k * |a * B|) * (((4 * (k : ℝ)) ^ (k ^ 3)) ^ k)) * B⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K ^ 2, sq_nonneg _, ?_⟩
  intro R t ht
  have h := dirichletLpSize_normalized_exp_difference_le hn hk R ht hv hvBound (a * B)
  have hExp : (fun x => Real.exp ((a * B) * v x)) = (fun x => Real.exp (a * u x)) := by
    funext x
    congr 1
    dsimp [v]
    field_simp [hB.ne']
  have hDiff : dirichletIteratedOrthogonalDifference R t v k =
      (fun x => B⁻¹ * dirichletIteratedOrthogonalDifference R t u k x) := by
    simpa only [dirichletIteratedFieldDifference_real] using
      dirichletIteratedFieldDifference_const_mul R t B⁻¹ u k
  rw [hExp, hDiff, dirichletLpSize_const_mul _ _ (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (inv_pos.mpr hB)] at h
  have hDiffC : dirichletIteratedOrthogonalDifference R t (fun y => c * Real.exp (a * u y)) k =
      (fun x => c * dirichletIteratedOrthogonalDifference R t (fun y => Real.exp (a * u y)) k x) := by
    simpa only [dirichletIteratedFieldDifference_real] using
      dirichletIteratedFieldDifference_const_mul R t c (fun y => Real.exp (a * u y)) k
  have hN : dirichletLpSize (dirichletIteratedOrthogonalDifference R t
      (fun y => c * Real.exp (a * u y)) k) 2 ≤
      K * dirichletLpSize (dirichletIteratedOrthogonalDifference R t u k) 2 := by
    rw [hDiffC, dirichletLpSize_const_mul _ _ (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg c)).trans_eq (by dsimp [K]; ring)
  have hSq := pow_le_pow_left₀ (dirichletLpSize_nonneg _ _) hN 2
  simpa only [mul_pow, dirichletLpSize_two_sq] using hSq

theorem exists_exponential_density_difference_lower_hessian_energy {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (a c : ℝ) (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ B ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t
          (fun y => c * Real.exp (a * u y)) (k + 1) x) ^ 2 ∂volume0 n) ≤
      B * dirichletFlowLowerHessianEnergy u S hS (k + 1) t := by
  obtain ⟨C, hC, hComp⟩ := exists_integral_exp_difference_sq_le_potential hn
    (Nat.zero_lt_succ k) hu.continuousOn a c
  refine ⟨C * (4 * ‖S‖ ^ 2), by positivity, ?_⟩
  intro t ht
  let R := orthogonalFlow S hS t
  let q := dirichletIteratedOrthogonalDifference R t u k
  have hq := contDiffOn_dirichletIteratedOrthogonalDifference R t hu k
  have hqS := contDiffOn_dirichletIteratedOrthogonalDifference_ball R t huS k
  have hq0 := dirichletIteratedOrthogonalDifference_zero_on_sphere R t hu0 k
  have hFlow := integral_orthogonalFlow_difference_sq_le_within_hessian hn hq hqS hq0 S hS ht
  have hLow : dirichletFlowHessianEnergy u S hS k t ≤
      dirichletFlowLowerHessianEnergy u S hS (k + 1) t :=
    Finset.single_le_sum (fun j _ => dirichletFlowHessianEnergy_nonneg u S hS j t)
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  calc
    _ ≤ C * ∫ x in unitBall n, (dirichletIteratedOrthogonalDifference R t u (k + 1) x) ^ 2 ∂volume0 n :=
      hComp R t ht
    _ ≤ C * ((4 * ‖S‖ ^ 2) * dirichletFlowHessianEnergy u S hS k t) :=
      mul_le_mul_of_nonneg_left hFlow hC
    _ ≤ C * ((4 * ‖S‖ ^ 2) * dirichletFlowLowerHessianEnergy u S hS (k + 1) t) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLow (by positivity)) hC
    _ = _ := by ring

end KEBall
