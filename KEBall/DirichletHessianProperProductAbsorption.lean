import KEBall.DirichletTensorProperProducts
import KEBall.DirichletIteratedHessianRemainder
import KEBall.DirichletDiscreteHessianQuartic

/-!
# Proper-product absorption at a genuine closed-ball C2 potential

The smooth reference is chosen after the small coefficient and before the step.
Its higher derivatives only contribute to the final additive constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem dirichletIteratedFieldDifference_sub {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F G : E n → V) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun x => F x - G x) k =
      fun x => dirichletIteratedFieldDifference R τ F k x -
        dirichletIteratedFieldDifference R τ G k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dirichletIteratedFieldDifference, ih, dirichletFieldDifference_sub]; rfl

theorem exists_integral_dirichlet_hessian_reference_difference_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {V : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hV : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ V x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n,
        ‖dirichletIteratedFieldDifference R t (fun y => dirichletWithinRealHessian u y - V y) k x‖ ^ 2
          ∂volume0 n) ≤
        (2 * (k + 1 : ℝ) * ((1 + 2 * ‖S‖) ^ k) ^ 2) *
          (∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n,
            ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2
              ∂volume0 n) + C := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  obtain ⟨M, hM, hRef⟩ := exists_dirichlet_smooth_field_iterated_difference_bound hV S hS k
  refine ⟨2 * M ^ 2, by positivity, ?_⟩
  intro t ht
  dsimp only
  let R := orthogonalFlow S hS t
  let A : ℝ := (1 + 2 * ‖S‖) ^ k
  let F (j : ℕ) (x : E n) :=
    ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖
  let Z := dirichletIteratedFieldDifference R t (fun y => dirichletWithinRealHessian u y - V y) k
  let K : ℝ := 2 * (k + 1 : ℝ) * A ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hFC (j : ℕ) : ContinuousOn (F j) (closedUnitBall n) :=
    (continuousOn_dirichletWithinRealHessian
      (contDiffOn_dirichletIteratedOrthogonalDifference R t hu j)).norm
  have hZC : ContinuousOn Z (closedUnitBall n) :=
    continuousOn_dirichletIteratedFieldDifference R t
      ((continuousOn_dirichletWithinRealHessian hu).sub
        (fun x hx => (hV x hx).continuousAt.continuousWithinAt)) k
  have hSumC : ContinuousOn (fun x => ∑ j ∈ Finset.range (k + 1), (F j x) ^ 2)
      (closedUnitBall n) := continuousOn_finset_sum _ (fun j _ => (hFC j).pow 2)
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      ‖Z x‖ ^ 2 ≤ K * (∑ j ∈ Finset.range (k + 1), (F j x) ^ 2) + 2 * M ^ 2 := by
    have hNorm : ‖Z x‖ ≤ A * (∑ j ∈ Finset.range (k + 1), F j x) + M := by
      dsimp only [Z]
      rw [dirichletIteratedFieldDifference_sub]
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_dirichletIteratedFieldDifference_withinHessian_le hu S hS ht k
          (ball_subset_closedBall hx)) (hRef t ht x (ball_subset_closedBall hx)))
    have hSq := pow_le_pow_left₀ (norm_nonneg (Z x)) hNorm 2
    have hSum := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1)) (f := fun j => F j x)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hSum
    have hMul := mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ 2 * A ^ 2)
    dsimp only [K]
    nlinarith only [hSq, hMul, sq_nonneg (A * (∑ j ∈ Finset.range (k + 1), F j x) - M)]
  have h := setIntegral_mono_on (hInt (hZC.norm.pow 2))
    (hInt ((hSumC.const_mul K).add continuousOn_const)) measurableSet_ball hPoint
  have hAdd := integral_add ((hInt hSumC).const_mul K) (integrable_const (2 * M ^ 2))
  have hSwap : (∫ x in unitBall n, ∑ j ∈ Finset.range (k + 1), (F j x) ^ 2 ∂volume0 n) =
      ∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n, (F j x) ^ 2 ∂volume0 n := by
    simpa only [Pi.pow_apply] using
      integral_finset_sum (Finset.range (k + 1)) (fun j _ => hInt ((hFC j).pow 2))
  simp only [Pi.add_apply, Pi.pow_apply] at h
  rw [hAdd, integral_const_mul, hSwap,
    integral_const, probReal_univ, one_smul] at h
  exact h

theorem exists_dirichlet_smooth_reference_proper_product_absorption {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ closedUnitBall n, ‖dirichletWithinRealHessian u x - realHessian v x‖ < 1) ∧
      ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n) (a b : ι → Fin (2 * n)),
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∏ i ∈ s,
        (dirichletIteratedFieldDifference R t
          (fun y => dirichletWithinRealHessian u y - realHessian v y)
          (j i) (Q i x) (e[n] (a i)) (e[n] (b i))) ^ 2 ∂volume0 n) ≤
        ε * (∑ m ∈ Finset.range (k + 1), ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u m) x‖ ^ 2
            ∂volume0 n) + C := by
  classical
  let K : ℝ := 2 * (k + 1 : ℝ) * ((1 + 2 * ‖S‖) ^ k) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let ε' := ε / (K + 1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨η, hη, hProd⟩ := integral_dirichlet_tensor_proper_product_sq_le_small hn hk s j hj hjk hSum hε'
  obtain ⟨v, hv, hv0, hApprox, _⟩ :=
    exists_dirichlet_smooth_zeroBoundary_reference_close_hessian hu huS hu0 (lt_min hη zero_lt_one)
  have hV (x : E n) (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ (realHessian v) x :=
    realHessian_contDiffAt (hv.contDiffAt hx)
  obtain ⟨C, hC, hEnergy⟩ := exists_integral_dirichlet_hessian_reference_difference_bound hn hu hV S hS k
  refine ⟨v, hv, hv0, fun x hx => (hApprox x hx).trans_le (min_le_right _ _),
    ε' * C, mul_nonneg hε'.le hC, ?_⟩
  intro t ht Q a b
  dsimp only
  have hZC : ContinuousOn (fun y => dirichletWithinRealHessian u y - realHessian v y)
      (closedUnitBall n) := (continuousOn_dirichletWithinRealHessian hu).sub
    (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
  have hP := hProd (orthogonalFlow S hS t) t ht _ hZC
    (fun x hx => (hApprox x (ball_subset_closedBall hx)).le.trans (min_le_left _ _)) Q a b
  have hE := mul_le_mul_of_nonneg_left (hEnergy t ht) hε'.le
  have hCap : ε' * K ≤ ε := by
    calc
      ε' * K ≤ ε' * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'.le
      _ = ε := by dsimp [ε']; exact div_mul_cancel₀ ε (by positivity : K + 1 ≠ 0)
  have hSum0 : 0 ≤ ∑ m ∈ Finset.range (k + 1), ∫ x in unitBall n,
      ‖dirichletWithinRealHessian
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u m) x‖ ^ 2 ∂volume0 n :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact hP.trans (hE.trans (by
    rw [mul_add, ← mul_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_right hCap hSum0) le_rfl))

end KEBall
