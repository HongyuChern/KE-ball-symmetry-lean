import KEBall.DirichletHessianMixedProductBound

/-! Every ordered cross term with one smooth-reference factor has strictly lower total order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem exists_dirichlet_hessian_reference_cross_term_bound {n k : ℕ}
    (hn : 0 < n) {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {V : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hV : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ V x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (i : ι) (hi : i ∈ s) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ), (∀ l ∈ s, ‖L l‖ ≤ Λ) →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n,
        (L i (dirichletIteratedFieldDifference R t V (j i) (Q i x))) ^ 2 *
        ∏ l ∈ s.erase i,
          (if l < i then L l (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (j l) (Q l x))
            else L l (dirichletIteratedFieldDifference R t
              (fun y => dirichletWithinRealHessian u y - V y) (j l) (Q l x))) ^ 2 ∂volume0 n) ≤
        C * (∑ l ∈ Finset.range k, ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u l) x‖ ^ 2 ∂volume0 n) + C := by
  classical
  let m := k - j i
  have hm0 : 0 < m := by have h := hjk i hi; dsimp [m]; omega
  have hm : m < k := by have h := hj i hi; have h' := hjk i hi; dsimp [m]; omega
  have hSumErase : ∑ l ∈ s.erase i, j l = m := by
    have h := Finset.sum_erase_add s j hi
    rw [hSum] at h
    dsimp [m]
    omega
  have hPos (l : ι) (hl : l ∈ s.erase i) : 0 < j l := hj l (Finset.mem_erase.mp hl).2
  have hOrder (l : ι) (hl : l ∈ s.erase i) : j l ≤ m := by
    rw [← hSumErase]
    exact Finset.single_le_sum (fun l _ => Nat.zero_le (j l)) hl
  obtain ⟨D, hD, hLower⟩ := exists_dirichlet_hessian_mixed_product_lower_bound hn hm0 hm
    (s.erase i) j hPos hOrder hSumErase hu hV S hS hΛ
  obtain ⟨M, hM, hRef⟩ := exists_dirichlet_smooth_field_iterated_difference_bound hV S hS (j i)
  refine ⟨(Λ * M) ^ 2 * D, mul_nonneg (sq_nonneg _) hD, ?_⟩
  intro t ht Q L hL
  dsimp only
  let R := orthogonalFlow S hS t
  let H := dirichletWithinRealHessian u
  let Z (y : E n) := H y - V y
  let F (x : E n) := L i (dirichletIteratedFieldDifference R t V (j i) (Q i x))
  let G (l : ι) (x : E n) :=
    if l < i then L l (dirichletIteratedFieldDifference R t H (j l) (Q l x))
    else L l (dirichletIteratedFieldDifference R t Z (j l) (Q l x))
  have hVC : ContinuousOn V (closedUnitBall n) :=
    fun x hx => (hV x hx).continuousAt.continuousWithinAt
  have hHC : ContinuousOn H (closedUnitBall n) := continuousOn_dirichletWithinRealHessian hu
  have hZC : ContinuousOn Z (closedUnitBall n) := hHC.sub hVC
  have hFC : ContinuousOn F (closedUnitBall n) := (L i).continuous.comp_continuousOn
    (continuousOn_dirichlet_orthogonal_comp
      (continuousOn_dirichletIteratedFieldDifference R t hVC (j i)) (Q i))
  have hGC (l : ι) : ContinuousOn (G l) (closedUnitBall n) := by
    dsimp only [G]
    by_cases hli : l < i
    · simp only [if_pos hli]
      exact (L l).continuous.comp_continuousOn (continuousOn_dirichlet_orthogonal_comp
        (continuousOn_dirichletIteratedFieldDifference R t hHC (j l)) (Q l))
    · simp only [if_neg hli]
      exact (L l).continuous.comp_continuousOn (continuousOn_dirichlet_orthogonal_comp
        (continuousOn_dirichletIteratedFieldDifference R t hZC (j l)) (Q l))
  have hPC := continuousOn_finsetProd (s.erase i) (fun l _ => (hGC l).pow 2)
  have hFBound (x : E n) (hx : x ∈ unitBall n) : |F x| ≤ Λ * M := by
    have hxQ : Q i x ∈ closedUnitBall n := by
      simpa only [closedUnitBall, mem_closedBall_zero_iff, (Q i).norm_map] using ball_subset_closedBall hx
    have h := (L i).le_opNorm (dirichletIteratedFieldDifference R t V (j i) (Q i x))
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul (hL i hi) (hRef t ht (Q i x) hxQ) (norm_nonneg _) hΛ)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      F x ^ 2 * (∏ l ∈ s.erase i, G l x ^ 2) ≤ (Λ * M) ^ 2 * (∏ l ∈ s.erase i, G l x ^ 2) :=
    mul_le_mul_of_nonneg_right
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hFBound x hx) 2)
      (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
  have hI := setIntegral_mono_on (hInt ((hFC.pow 2).mul hPC))
    (hInt (hPC.const_mul ((Λ * M) ^ 2))) measurableSet_ball hPoint
  simp only [Pi.mul_apply, Pi.pow_apply] at hI
  rw [integral_const_mul] at hI
  have hLow : (∫ x in unitBall n, ∏ l ∈ s.erase i, G l x ^ 2 ∂volume0 n) ≤
      D * (∑ l ∈ Finset.range k, ∫ x in unitBall n,
        ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u l) x‖ ^ 2 ∂volume0 n) + D := by
    simpa only [decide_eq_true_eq, G, R, H, Z] using hLower t ht Q L
      (fun l hl => hL l (Finset.mem_erase.mp hl).2) (fun l => decide (l < i))
  exact hI.trans ((mul_le_mul_of_nonneg_left hLow (sq_nonneg _)).trans_eq (by ring))

end KEBall
