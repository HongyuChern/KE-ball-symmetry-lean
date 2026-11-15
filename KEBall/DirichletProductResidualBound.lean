import KEBall.DirichletProductDifferenceEquation

/-! An ordered product split that isolates the all-residual term without a reference-dependent coefficient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open MeasureTheory Metric Set
open scoped BigOperators

namespace KEBall

theorem dirichlet_prod_erase_mixed {ι A : Type*} [LinearOrder ι] [CommMonoid A]
    (s : Finset ι) (F G : ι → A) (i : ι) :
    (∏ j ∈ s.erase i, if j < i then F j else G j) =
      (∏ j ∈ s with j < i, F j) * (∏ j ∈ s with i < j, G j) := by
  classical
  rw [Finset.prod_ite]
  congr 1
  · apply Finset.prod_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hj⟩, hji⟩
        exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨⟨hji.ne, hj⟩, hji⟩
    · intro j hj
      rfl
  · apply Finset.prod_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hj⟩, hji⟩
        exact ⟨hj, lt_of_le_of_ne (not_lt.mp hji) hne.symm⟩
      · rintro ⟨hj, hji⟩
        exact ⟨⟨hji.ne', hj⟩, not_lt_of_ge hji.le⟩
    · intro j hj
      rfl

theorem dirichlet_product_add_sq_le {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (A B : ι → ℝ) :
    (∏ i ∈ s, (A i + B i)) ^ 2 ≤ 2 * (∏ i ∈ s, A i) ^ 2 +
      2 * s.card * ∑ i ∈ s, (B i) ^ 2 * ∏ j ∈ s.erase i,
        (if j < i then A j + B j else A j) ^ 2 := by
  classical
  let Q (i : ι) := B i * ∏ j ∈ s.erase i, if j < i then A j + B j else A j
  have hQ (i : ι) : Q i = B i * (∏ j ∈ s with j < i, (A j + B j)) * (∏ j ∈ s with i < j, A j) := by
    dsimp only [Q]
    rw [dirichlet_prod_erase_mixed]
    ring
  have hSplit : (∏ i ∈ s, (A i + B i)) = (∏ i ∈ s, A i) + ∑ i ∈ s, Q i := by
    rw [Finset.prod_add_ordered]
    simp only [hQ]
  rw [hSplit]
  have hTwo : ((∏ i ∈ s, A i) + ∑ i ∈ s, Q i) ^ 2 ≤
      2 * (∏ i ∈ s, A i) ^ 2 + 2 * (∑ i ∈ s, Q i) ^ 2 := by
    nlinarith only [sq_nonneg ((∏ i ∈ s, A i) - ∑ i ∈ s, Q i)]
  have hSum := sq_sum_le_card_mul_sum_sq (s := s) (f := Q)
  have hQs (i : ι) : Q i ^ 2 = B i ^ 2 * ∏ j ∈ s.erase i,
      (if j < i then A j + B j else A j) ^ 2 := by
    dsimp only [Q]
    rw [mul_pow, Finset.prod_pow]
  simp only [hQs] at hSum
  nlinarith only [hTwo, hSum]

theorem integral_dirichlet_product_add_sq_le {n : ℕ} (hn : 0 < n)
    {ι : Type*} [LinearOrder ι] (s : Finset ι) (A B : ι → E n → ℝ)
    (hA : ∀ i ∈ s, ContinuousOn (A i) (closedUnitBall n))
    (hB : ∀ i ∈ s, ContinuousOn (B i) (closedUnitBall n)) :
    (∫ x in unitBall n, ∏ i ∈ s, (A i x + B i x) ^ 2 ∂volume0 n) ≤
      2 * (∫ x in unitBall n, ∏ i ∈ s, (A i x) ^ 2 ∂volume0 n) +
      2 * s.card * ∑ i ∈ s, ∫ x in unitBall n, (B i x) ^ 2 * ∏ j ∈ s.erase i,
        (if j < i then A j x + B j x else A j x) ^ 2 ∂volume0 n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  let T (i : ι) (x : E n) := (B i x) ^ 2 * ∏ j ∈ s.erase i,
    (if j < i then A j x + B j x else A j x) ^ 2
  have hTC (i : ι) (hi : i ∈ s) : ContinuousOn (T i) (closedUnitBall n) := by
    apply (hB i hi).pow 2 |>.mul
    apply continuousOn_finsetProd
    intro j hj
    have hjs := (Finset.mem_erase.mp hj).2
    by_cases hji : j < i
    · simp only [if_pos hji]
      convert! ((hA j hjs).add (hB j hjs)).pow 2 using 1
    · simp only [if_neg hji]
      convert! (hA j hjs).pow 2 using 1
  have hInt {F : E n → ℝ} (hF : ContinuousOn F (closedUnitBall n)) :
      IntegrableOn F (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hF 1).integrable le_rfl
  have hPC := continuousOn_finsetProd s (fun i hi => ((hA i hi).add (hB i hi)).pow 2)
  have hAC := continuousOn_finsetProd s (fun i hi => (hA i hi).pow 2)
  have hSC := continuousOn_finsetSum s (fun i hi => hTC i hi)
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      (∏ i ∈ s, (A i x + B i x) ^ 2) ≤ 2 * (∏ i ∈ s, (A i x) ^ 2) +
        2 * s.card * ∑ i ∈ s, T i x := by
    simpa only [Finset.prod_pow, T] using dirichlet_product_add_sq_le s (fun i => A i x) (fun i => B i x)
  have h := setIntegral_mono_on (hInt hPC)
    (hInt ((hAC.const_mul 2).add (hSC.const_mul (2 * s.card)))) measurableSet_ball hPoint
  have hAdd := integral_add ((hInt hAC).const_mul 2) ((hInt hSC).const_mul (2 * s.card))
  have hSwap := integral_finset_sum s (fun i hi => hInt (hTC i hi))
  simp only [Pi.add_apply, Pi.pow_apply] at h hAdd
  rw [hAdd, integral_const_mul, integral_const_mul, hSwap] at h
  exact h

end KEBall
