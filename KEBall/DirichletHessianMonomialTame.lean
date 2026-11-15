import KEBall.DirichletComplexHessianProductTame

/-! Undifferentiated factors are allowed in proper actual-Hessian monomials. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem exists_dirichlet_hessian_monomial_tame_bound {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (j : ι → ℕ) (hjk : ∀ i ∈ s, j i < k) (hSum : ∑ i ∈ s, j i = k)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℂ), (∀ i ∈ s, ‖L i‖ ≤ Λ) →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∏ i ∈ s,
        ‖L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u)
          (j i) (Q i x))‖ ^ 2 ∂volume0 n) ≤
        ε * (∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x‖ ^ 2 ∂volume0 n) +
        C * (∑ m ∈ Finset.range k, ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u m) x‖ ^ 2 ∂volume0 n) + C := by
  classical
  let p := s.filter (fun i => 0 < j i)
  have hps : p ⊆ s := Finset.filter_subset _ _
  have hpj (i : ι) (hi : i ∈ p) : 0 < j i := (Finset.mem_filter.mp hi).2
  have hpSum : ∑ i ∈ p, j i = k := by
    calc
      _ = ∑ i ∈ s, j i := Finset.sum_subset hps (fun i hi hip => by
        have hnot : ¬ 0 < j i := fun h => hip (Finset.mem_filter.mpr ⟨hi, h⟩)
        omega)
      _ = k := hSum
  have hHC := continuousOn_dirichletWithinRealHessian hu
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hHC
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  let K := ((Λ * B) ^ 2) ^ (s.filter (fun i => ¬ 0 < j i)).card
  have hK : 0 ≤ K := pow_nonneg (sq_nonneg _) _
  let ε' := ε / (K + 1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨C, hC, hBound⟩ := exists_dirichlet_complex_hessian_proper_product_tame_bound hn hk p j hpj
    (fun i hi => hjk i (hps hi)) hpSum hu huS hu0 S hS hΛ hε'
  refine ⟨K * C, mul_nonneg hK hC, ?_⟩
  intro t ht Q L hL
  dsimp only
  let R := orthogonalFlow S hS t
  let F (i : ι) (x : E n) := L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (j i) (Q i x))
  have hFC (i : ι) : ContinuousOn (F i) (closedUnitBall n) := (L i).continuous.comp_continuousOn
    (continuousOn_dirichlet_orthogonal_comp
      (continuousOn_dirichletIteratedFieldDifference R t hHC (j i)) (Q i))
  have hZero (i : ι) (hi : i ∈ s) (hj0 : ¬ 0 < j i) (x : E n) (hx : x ∈ unitBall n) :
      ‖F i x‖ ^ 2 ≤ (Λ * B) ^ 2 := by
    have hje : j i = 0 := by omega
    have hxQ : Q i x ∈ closedUnitBall n := by
      simpa only [closedUnitBall, mem_closedBall_zero_iff, (Q i).norm_map] using ball_subset_closedBall hx
    have hHB : ‖dirichletWithinRealHessian u (Q i x)‖ ≤ B := (hB₀ _ hxQ).trans (le_max_left _ _)
    have hNorm := ((L i).le_opNorm (dirichletWithinRealHessian u (Q i x))).trans
      (mul_le_mul (hL i hi) hHB (norm_nonneg _) hΛ)
    simpa only [F, hje, dirichletIteratedFieldDifference] using pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      (∏ i ∈ s, ‖F i x‖ ^ 2) ≤ K * (∏ i ∈ p, ‖F i x‖ ^ 2) := by
    calc
      _ ≤ ∏ i ∈ s, if 0 < j i then ‖F i x‖ ^ 2 else (Λ * B) ^ 2 := by
        apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
        intro i hi
        split_ifs with hji
        · exact le_rfl
        · exact hZero i hi hji x hx
      _ = _ := by rw [Finset.prod_ite, Finset.prod_const]; exact mul_comm _ _
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hPC := continuousOn_finsetProd p (fun i _ => (hFC i).norm.pow 2)
  have hSC := continuousOn_finsetProd s (fun i _ => (hFC i).norm.pow 2)
  have hI := setIntegral_mono_on (hInt hSC) (hInt (hPC.const_mul K)) measurableSet_ball hPoint
  rw [integral_const_mul] at hI
  have hP := hBound t ht Q L (fun i hi => hL i (hps hi))
  dsimp only at hP
  have hCap : K * ε' ≤ ε := by
    calc
      K * ε' ≤ (K + 1) * ε' := mul_le_mul_of_nonneg_right (by linarith) hε'.le
      _ = ε := by dsimp only [ε']; exact mul_div_cancel₀ ε (by positivity : K + 1 ≠ 0)
  refine hI.trans ((mul_le_mul_of_nonneg_left hP hK).trans ?_)
  simp only [mul_add, ← mul_assoc]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCap
    (integral_nonneg (fun _ => sq_nonneg _))) le_rfl) le_rfl

end KEBall
