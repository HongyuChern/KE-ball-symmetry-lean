import KEBall.DirichletIteratedTensorDifferences
import KEBall.DirichletFiniteHolder
import KEBall.DirichletTensorQuartic

/-!
# Small proper products of actual tensor differences

Every differentiated factor has order strictly between zero and the total order.
The reference-independent small coefficient comes from the sup norm of the field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem integral_dirichlet_tensor_proper_product_sq_le {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} (s : Finset ι)
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {H : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hH : ContinuousOn H (closedUnitBall n))
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k)
    (Q : ι → E n ≃ₗᵢ[ℝ] E n) (a b : ι → Fin (2 * n))
    {η : ℝ} (hη : 0 ≤ η) (hBound : ∀ x ∈ unitBall n, ‖H x‖ ≤ η) :
    (∫ x in unitBall n, ∏ i ∈ s,
      (dirichletIteratedFieldDifference R τ H (j i) (Q i x) (e[n] (a i)) (e[n] (b i))) ^ 2
        ∂volume0 n) ≤
      (((4 * (k : ℝ)) ^ (k ^ 3)) ^ s.card * η ^ (s.card - 1)) ^ 2 *
        ∫ x in unitBall n, ‖dirichletIteratedFieldDifference R τ H k x‖ ^ 2 ∂volume0 n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  let F (i : ι) (x : E n) := H x (e[n] (a i)) (e[n] (b i))
  let K := dirichletIteratedFieldDifference R τ H k
  let Y := dirichletLpSize (fun x => ‖K x‖) 2
  have hK : ContinuousOn K (closedUnitBall n) :=
    continuousOn_dirichletIteratedFieldDifference R τ hH k
  have hF (i : ι) : ContinuousOn (F i) (closedUnitBall n) :=
    (hH.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hTop (i : ι) : dirichletLpSize (dirichletIteratedOrthogonalDifference R τ (F i) k) 2 ≤ Y := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (dirichletLpSize_nonneg _ _)
    rw [dirichletLpSize_two_sq, dirichletLpSize_two_sq]
    have hEq (x : E n) : dirichletIteratedOrthogonalDifference R τ (F i) k x =
        K x (e[n] (a i)) (e[n] (b i)) :=
      (dirichletIteratedFieldDifference_bilinear_apply R τ H k x _ _).symm
    simp only [hEq]
    exact setIntegral_mono_on
      (hInt (((hK.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2))
      (hInt (hK.norm.pow 2)) measurableSet_ball (fun x _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (abs_dirichlet_bilinear_entry_le_norm (K x) (a i) (b i)) 2)
  have h := integral_dirichlet_discrete_proper_product_sq_le hn hk s R hτ F
    (fun i _ => hF i) j hj hjk hSum Q hη (dirichletLpSize_nonneg _ _)
    (fun i _ x hx => (abs_dirichlet_bilinear_entry_le_norm (H x) (a i) (b i)).trans (hBound x hx))
    (fun i _ => hTop i)
  have hEq (i : ι) (x : E n) : dirichletIteratedOrthogonalDifference R τ (F i) (j i) (Q i x) =
      dirichletIteratedFieldDifference R τ H (j i) (Q i x) (e[n] (a i)) (e[n] (b i)) :=
    (dirichletIteratedFieldDifference_bilinear_apply R τ H (j i) (Q i x) _ _).symm
  simp only [hEq] at h
  exact h.trans_eq (by rw [mul_pow, dirichletLpSize_two_sq])

theorem dirichlet_proper_order_product_card_ge_two {ι : Type*} (s : Finset ι)
    {k : ℕ} (hk : 0 < k) (j : ι → ℕ)
    (hjk : ∀ i ∈ s, j i < k) (hSum : ∑ i ∈ s, j i = k) : 2 ≤ s.card := by
  classical
  by_contra h
  have hc : s.card ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · have he : s = ∅ := Finset.card_eq_zero.mp h0
    subst s
    simp only [Finset.sum_empty] at hSum
    omega
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
    subst s
    have hj := hjk i (Finset.mem_singleton_self i)
    simp only [Finset.sum_singleton] at hSum
    omega

theorem exists_dirichlet_tensor_proper_product_small_scale {k r : ℕ}
    (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), (((4 * (k : ℝ)) ^ (k ^ 3)) ^ r * η ^ (r - 1)) ^ 2 ≤ ε := by
  have hc : ContinuousAt (fun η : ℝ => (((4 * (k : ℝ)) ^ (k ^ 3)) ^ r * η ^ (r - 1)) ^ 2) 0 := by
    fun_prop
  have hr0 : r - 1 ≠ 0 := by omega
  have h0 : (((4 * (k : ℝ)) ^ (k ^ 3)) ^ r * (0 : ℝ) ^ (r - 1)) ^ 2 < ε := by
    simpa only [zero_pow hr0, mul_zero, zero_pow (by decide : 2 ≠ 0)] using hε
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (gt_mem_nhds h0))
  refine ⟨δ / 2, by positivity, (hδb ?_).le⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

theorem integral_dirichlet_tensor_proper_product_sq_le_small {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ), τ ≠ 0 →
      ∀ (H : E n → E n →L[ℝ] E n →L[ℝ] ℝ), ContinuousOn H (closedUnitBall n) →
      (∀ x ∈ unitBall n, ‖H x‖ ≤ η) →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n) (a b : ι → Fin (2 * n)),
      (∫ x in unitBall n, ∏ i ∈ s,
        (dirichletIteratedFieldDifference R τ H (j i) (Q i x) (e[n] (a i)) (e[n] (b i))) ^ 2
          ∂volume0 n) ≤
        ε * ∫ x in unitBall n, ‖dirichletIteratedFieldDifference R τ H k x‖ ^ 2 ∂volume0 n := by
  obtain ⟨η, hη, hSmall⟩ := exists_dirichlet_tensor_proper_product_small_scale (k := k)
    (dirichlet_proper_order_product_card_ge_two s (by omega) j hjk hSum) hε
  refine ⟨η, hη, ?_⟩
  intro R τ hτ H hH hBound Q a b
  exact (integral_dirichlet_tensor_proper_product_sq_le hn hk s R hτ hH j hj hjk hSum Q a b
    hη.le hBound).trans (mul_le_mul_of_nonneg_right hSmall
      (integral_nonneg (fun _ => sq_nonneg _)))

end KEBall
