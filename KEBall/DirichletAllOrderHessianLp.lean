import KEBall.DirichletTensorHigherPower
import KEBall.DirichletHessianDifferenceReverse

/-! Uniform finite even powers of the actual iterated potential-difference Hessian. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff
namespace KEBall

theorem exists_dirichlet_all_spatial_hessian_differences_uniform_even_power_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    ∃ δ > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ j ≤ k,
      (∫ x in unitBall n, ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t
        (dirichletWithinRealHessian u) j x‖^(2*r) ∂volume0 n) ≤ C := by
  induction k with
  | zero =>
    refine ⟨1,zero_lt_one,∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖^(2*r) ∂volume0 n,
      integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _),?_⟩
    intro t ht htδ j hj
    have hj0 : j=0 := by omega
    subst j
    exact le_rfl
  | succ k ih =>
    obtain ⟨δ₀,hδ₀,B,hB,hPrev⟩ := ih
    obtain ⟨δ₁,hδ₁,A,hA,hNew⟩ := exists_dirichlet_spatial_hessian_difference_uniform_even_power_bound
      hn hu huS hu0 hPos hf hEq S hS (Nat.succ_pos k) hr
    refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,max B A,hB.trans (le_max_left _ _),?_⟩
    intro t ht htδ j hj
    by_cases hjk : j ≤ k
    · exact (hPrev t ht (htδ.trans_le (min_le_left _ _)) j hjk).trans (le_max_left _ _)
    · have he : j=k+1 := by omega
      subst j
      exact (hNew t ht (htδ.trans_le (min_le_right _ _))).trans (le_max_right _ _)

theorem exists_dirichlet_iterated_difference_uniform_hessian_even_power_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    ∃ δ > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ‖dirichletWithinRealHessian
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x‖^(2*r)
          ∂volume0 n) ≤ C := by
  obtain ⟨δ,hδ,B,hB,hBound⟩ := exists_dirichlet_all_spatial_hessian_differences_uniform_even_power_bound
    hn hu huS hu0 hPos hf hEq S hS k hr
  let A : ℝ := (1+2*‖S‖)^k
  let K : ℝ := A^(2*r)*(k+1:ℝ)^(2*r-1)
  have hK : 0 ≤ K := by dsimp [K,A]; positivity
  refine ⟨δ,hδ,K*((k+1:ℝ)*B),by positivity,?_⟩
  intro t ht htδ
  let R := orthogonalFlow S hS t
  let F (j : ℕ) (x : E n) := ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) j x‖
  have hFC (j : ℕ) : ContinuousOn (F j) (closedUnitBall n) :=
    (continuousOn_dirichletIteratedFieldDifference R t (continuousOn_dirichletWithinRealHessian hu) j).norm
  have hSumC : ContinuousOn (fun x => ∑ j ∈ Finset.range (k+1), (F j x)^(2*r))
      (closedUnitBall n) := continuousOn_finsetSum _ (fun j _ => (hFC j).pow _)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {g : E n → ℝ} (hg : ContinuousOn g (closedUnitBall n)) :
      IntegrableOn g (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hg 1).integrable le_rfl
  have hHC := continuousOn_dirichletWithinRealHessian (contDiffOn_dirichletIteratedOrthogonalDifference R t hu k)
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x‖^(2*r) ≤
        K*∑ j ∈ Finset.range (k+1), (F j x)^(2*r) := by
    have hN := pow_le_pow_left₀ (norm_nonneg _)
      (norm_dirichlet_iterated_difference_hessian_le_tensor_differences hu S hS ht k (ball_subset_closedBall hx)) (2*r)
    rw [mul_pow] at hN
    have hSum := dirichlet_sum_nat_pow_le (Finset.range (k+1)) (fun j => F j x)
      (fun j _ => norm_nonneg _) (by omega : 1 ≤ 2*r)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hSum
    exact hN.trans ((mul_le_mul_of_nonneg_left hSum (by dsimp [A]; positivity : 0 ≤ A^(2*r))).trans_eq
      (by dsimp [K]; ring))
  have hI := setIntegral_mono_on (hInt (hHC.norm.pow (2*r))) (hInt (hSumC.const_mul K)) measurableSet_ball hPoint
  rw [integral_const_mul, integral_finsetSum (Finset.range (k+1))
    (f := fun j x => (F j x)^(2*r)) (fun j _ => hInt ((hFC j).pow (2*r)))] at hI
  refine hI.trans (mul_le_mul_of_nonneg_left ?_ hK)
  calc
    _ ≤ ∑ _j ∈ Finset.range (k+1), B := Finset.sum_le_sum (fun j hj =>
      hBound t ht htδ j (by have := Finset.mem_range.mp hj; omega))
    _ = (k+1:ℝ)*B := by simp

end KEBall
