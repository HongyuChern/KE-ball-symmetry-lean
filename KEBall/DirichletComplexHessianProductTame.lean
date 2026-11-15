import KEBall.DirichletHessianProductTame

/-! Proper products of complex linear forms of the actual real Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

noncomputable def dirichletComplexPartCLM {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℂ) (p : Bool) : V →L[ℝ] ℝ :=
  if p then Complex.reCLM.comp L else Complex.imCLM.comp L

theorem dirichletComplexPartCLM_apply {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℂ) (p : Bool) (v : V) :
    dirichletComplexPartCLM L p v = if p then (L v).re else (L v).im := by
  cases p <;> rfl

theorem norm_dirichletComplexPartCLM_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℂ) (p : Bool) :
    ‖dirichletComplexPartCLM L p‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  rw [dirichletComplexPartCLM_apply]
  cases p with
  | false => exact (Complex.abs_im_le_norm (L v)).trans (L.le_opNorm v)
  | true => exact (Complex.abs_re_le_norm (L v)).trans (L.le_opNorm v)

theorem dirichlet_complex_product_norm_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ) :
    (∏ i ∈ s, ‖F i‖ ^ 2) = ∑ p ∈ s.powerset,
      ∏ i ∈ s, (if i ∈ p then (F i).re else (F i).im) ^ 2 := by
  classical
  simp only [Complex.sq_norm, Complex.normSq_apply, ← sq]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro p hp
  have hps := Finset.mem_powerset.mp hp
  simp only [ite_pow, Finset.prod_ite]
  have hLeft : s.filter (fun i => i ∈ p) = p := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hps h, h⟩⟩
  have hRight : s.filter (fun i => i ∉ p) = s \ p := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]
  rw [hLeft, hRight]

theorem exists_dirichlet_complex_hessian_proper_product_tame_bound {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
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
  let N : ℝ := s.powerset.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Finset.card_pos.mpr ⟨∅, Finset.empty_mem_powerset s⟩
  obtain ⟨C, hC, hTame⟩ := exists_dirichlet_hessian_proper_product_tame_bound hn hk s j hj hjk hSum hu huS hu0
    S hS hΛ (div_pos hε hN)
  refine ⟨N * C, mul_nonneg hN.le hC, ?_⟩
  intro t ht Q L hL
  dsimp only
  let R := orthogonalFlow S hS t
  let F (i : ι) (x : E n) := L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (j i) (Q i x))
  let P (p : Finset ι) (x : E n) := ∏ i ∈ s, (if i ∈ p then (F i x).re else (F i x).im) ^ 2
  let Energy (m : ℕ) := ∫ x in unitBall n,
    ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u m) x‖ ^ 2 ∂volume0 n
  let Low := ∑ m ∈ Finset.range k, Energy m
  have hFC (i : ι) : ContinuousOn (F i) (closedUnitBall n) := (L i).continuous.comp_continuousOn
    (continuousOn_dirichlet_orthogonal_comp
      (continuousOn_dirichletIteratedFieldDifference R t (continuousOn_dirichletWithinRealHessian hu) (j i)) (Q i))
  have hPC (p : Finset ι) : ContinuousOn (P p) (closedUnitBall n) := by
    apply continuousOn_finsetProd
    intro i hi
    by_cases hip : i ∈ p
    · simp only [if_pos hip]
      exact (Complex.continuous_re.comp_continuousOn (hFC i)).pow 2
    · simp only [if_neg hip]
      exact (Complex.continuous_im.comp_continuousOn (hFC i)).pow 2
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hPI (p : Finset ι) : IntegrableOn (P p) (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn (hPC p) 1).integrable le_rfl
  have hBound (p : Finset ι) : (∫ x in unitBall n, P p x ∂volume0 n) ≤
      ε / N * Energy k + C * Low + C := by
    simpa only [dirichletComplexPartCLM_apply, decide_eq_true_eq] using
      hTame t ht Q (fun i => dirichletComplexPartCLM (L i) (decide (i ∈ p)))
        (fun i hi => (norm_dirichletComplexPartCLM_le (L i) _).trans (hL i hi))
  have hEq (x : E n) : (∏ i ∈ s, ‖F i x‖ ^ 2) = ∑ p ∈ s.powerset, P p x :=
    dirichlet_complex_product_norm_sq s (fun i => F i x)
  calc
    _ = ∫ x in unitBall n, ∑ p ∈ s.powerset, P p x ∂volume0 n := integral_congr_ae (Filter.Eventually.of_forall hEq)
    _ = ∑ p ∈ s.powerset, ∫ x in unitBall n, P p x ∂volume0 n := integral_finset_sum _ (fun p _ => hPI p)
    _ ≤ ∑ _ ∈ s.powerset, (ε / N * Energy k + C * Low + C) := Finset.sum_le_sum (fun p _ => hBound p)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change N * (ε / N * Energy k + C * Low + C) = ε * Energy k + N * C * Low + N * C
      field_simp [hN.ne']

end KEBall
