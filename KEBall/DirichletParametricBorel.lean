import KEBall.DirichletTransverseMonomial

/-! Borel interpolation in one variable with a smooth spatial parameter. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Metric
open scoped ContDiff Topology BigOperators

namespace KEBall

private theorem norm_iteratedFDeriv_comp_projection_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (i := j)
    (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

private theorem exists_bound_iteratedFDeriv_compactSupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hC := hf.continuous_iteratedFDeriv
    (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, h⟩ := hC.norm.bddAbove_range_of_hasCompactSupport (hs.iteratedFDeriv j).norm
  exact ⟨C, (norm_nonneg _).trans (h ⟨0, rfl⟩), fun x => h ⟨x, rfl⟩⟩

private theorem exists_lower_bound_parametricMonomial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → ℝ} (hA : ContDiff ℝ ∞ A) (hAS : HasCompactSupport A)
    {k j : ℕ} (hj : j < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Ioc (0 : ℝ) 1, ∀ x : ℝ × E,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × E => transverseMonomial k a p.1 * A p.2) x‖ ≤ C * a := by
  classical
  let P := ContinuousLinearMap.fst ℝ ℝ E
  let Q := ContinuousLinearMap.snd ℝ ℝ E
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ E
  have hQ : ‖Q‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ E
  have hC (i : ℕ) (hi : i < j + 1) := exists_bound_iteratedFDeriv_transverseMonomial k i (by omega)
  choose C hC₀ hC using hC
  choose B hB₀ hB using exists_bound_iteratedFDeriv_compactSupport hA hAS
  let D (i : ℕ) := if hi : i < j + 1 then C i hi else 0
  have hD₀ (i : ℕ) : 0 ≤ D i := by
    dsimp only [D]
    split
    · apply hC₀
    · exact le_rfl
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D i * B (j - i),
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD₀ i)) (hB₀ _)), fun a ha x => ?_⟩
  have hS := contDiff_transverseMonomial k a
  have hM := norm_iteratedFDeriv_mul_le (hS.comp P.contDiff) (hA.comp Q.contDiff) x
    (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  change ‖iteratedFDeriv ℝ j (fun p : ℝ × E => (transverseMonomial k a ∘ P) p *
    (A ∘ Q) p) x‖ ≤ _
  refine hM.trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < j + 1 := Finset.mem_range.mp hi
  have hOne : a ^ (k - i) ≤ a := by
    rcases Nat.exists_eq_succ_of_ne_zero (show k - i ≠ 0 by omega) with ⟨m, hm⟩
    rw [hm, pow_succ]
    exact mul_le_of_le_one_left ha.1.le (pow_le_one₀ ha.1.le ha.2)
  have h₁ : ‖iteratedFDeriv ℝ i (transverseMonomial k a ∘ P) x‖ ≤ D i * a := by
    apply (norm_iteratedFDeriv_comp_projection_le hS P hP i x).trans
    rw [show D i = C i hi' by simp only [D, dif_pos hi']]
    exact (hC i hi' a ha.1 (P x)).trans (mul_le_mul_of_nonneg_left hOne (hC₀ i hi'))
  have h₂ := (norm_iteratedFDeriv_comp_projection_le hA Q hQ (j - i) x).trans (hB _ _)
  calc
    _ ≤ (j.choose i : ℝ) * (D i * a) * B (j - i) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)) h₂
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD₀ i) ha.1.le))
    _ = _ := by ring

private theorem exists_scale_parametricMonomial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → ℝ} (hA : ContDiff ℝ ∞ A) (hAS : HasCompactSupport A)
    (k : ℕ) :
    ∃ a ∈ Ioc (0 : ℝ) 1, ∀ j < k, ∀ x : ℝ × E,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × E => transverseMonomial k a p.1 * A p.2) x‖
        ≤ ((1 : ℝ) / 2) ^ k := by
  classical
  choose C hC₀ hC using fun j hj => exists_lower_bound_parametricMonomial hA hAS (k := k) (j := j) hj
  let D (j : ℕ) : ℝ := if hj : j < k then C j hj else 0
  let M := ∑ j ∈ Finset.range k, D j
  have hD (j : ℕ) : 0 ≤ D j := by
    dsimp only [D]
    split
    · apply hC₀
    · exact le_rfl
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => hD j
  let a := ((1 : ℝ) / 2) ^ k / (M + 1)
  have ha : 0 < a := div_pos (by positivity) (by linarith)
  have ha₁ : a ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < M + 1)).mpr
    simpa only [one_mul] using (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) (n := k)).trans (show 1 ≤ M + 1 by linarith)
  refine ⟨a, ⟨ha, ha₁⟩, fun j hj x => (hC j hj a ⟨ha, ha₁⟩ x).trans ?_⟩
  have hDM : C j hj ≤ M := by
    simpa only [D, dif_pos hj] using
      (Finset.single_le_sum (f := D) (fun j _ => hD j) (Finset.mem_range.mpr hj))
  calc
    C j hj * a ≤ M * a := mul_le_mul_of_nonneg_right hDM ha.le
    _ ≤ (M + 1) * a := mul_le_mul_of_nonneg_right (by linarith) ha.le
    _ = _ := by
      dsimp only [a]
      rw [← mul_div_assoc, mul_comm (M + 1), mul_div_cancel_right₀ _ (by linarith)]

/-- Smooth compactly supported coefficient functions in a parameter
are the transverse derivatives of one jointly smooth function. -/
theorem exists_contDiff_parametricBorel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (A : ℕ → E → ℝ) (hA : ∀ k, ContDiff ℝ ∞ (A k))
    (hAS : ∀ k, HasCompactSupport (A k)) :
    ∃ H : ℝ × E → ℝ, ContDiff ℝ ∞ H ∧
      ∀ k x, iteratedDeriv k (fun t => H (t, x)) 0 = A k x := by
  classical
  choose a ha hSmall using fun k => exists_scale_parametricMonomial (hA k) (hAS k) k
  let U (k : ℕ) (p : ℝ × E) := transverseMonomial k (a k) p.1 * A k p.2
  have hU (k : ℕ) : ContDiff ℝ ∞ (U k) :=
    ((contDiff_transverseMonomial k (a k)).comp contDiff_fst).mul ((hA k).comp contDiff_snd)
  have hSupp (k : ℕ) : HasCompactSupport (U k) := by
    have hs : Function.support (U k) ⊆ closedBall (0 : ℝ) 1 ×ˢ tsupport (A k) := by
      intro p hp
      have hx : A k p.2 ≠ 0 := fun hz => hp (by simp [U, hz])
      refine ⟨?_, subset_tsupport _ hx⟩
      by_contra hn
      have hn' : 1 < |p.1| := by simpa [Real.dist_eq, Real.norm_eq_abs] using hn
      exact hp (by simp only [U, transverseMonomial_eq_zero_of_lt_abs k (ha k) hn', zero_mul])
    exact HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ) 1).prod (hAS k)) hs
  choose B hB₀ hB using fun j k => exists_bound_iteratedFDeriv_compactSupport (hU k) (hSupp k) j
  let v (j k : ℕ) : ℝ := if k ≤ j then B j k else ((1 : ℝ) / 2) ^ k
  have hV (j : ℕ) : Summable (v j) := by
    apply summable_geometric_two.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop j] with k hk
    simp only [v, if_neg hk.not_ge]
  have hNorm (j k : ℕ) (p : ℝ × E) : ‖iteratedFDeriv ℝ j (U k) p‖ ≤ v j k := by
    by_cases hk : k ≤ j
    · simpa only [v, if_pos hk] using hB j k p
    · simpa only [v, if_neg hk] using hSmall k j (by omega) p
  let H (p : ℝ × E) := ∑' k, U k p
  have hH : ContDiff ℝ ∞ H :=
    contDiff_tsum (N := (⊤ : ℕ∞)) hU (fun j _ => hV j) (fun j k p _ => hNorm j k p)
  refine ⟨H, hH, fun k x => ?_⟩
  let u (i : ℕ) (t : ℝ) := U i (t, x)
  have hu (i : ℕ) : ContDiff ℝ ∞ (u i) :=
    (hU i).comp (contDiff_id.prodMk contDiff_const)
  have hJu (j i : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ j (u i) t‖ ≤ v j i := by
    let L : ℝ →L[ℝ] ℝ × E := (ContinuousLinearMap.id ℝ ℝ).prod 0
    have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun t => by
      change ‖(t, (0 : E))‖ ≤ 1 * ‖t‖
      simp)
    let f := U i ∘ (fun p : ℝ × E => p + (0, x))
    have hf : ContDiff ℝ ∞ f := (hU i).comp (contDiff_id.add contDiff_const)
    have he : u i = f ∘ L := by
      funext t
      simp [u, f, L, Function.comp_def]
    rw [he]
    refine (norm_iteratedFDeriv_comp_projection_le hf L hL j t).trans ?_
    change ‖iteratedFDeriv ℝ j (fun p : ℝ × E => U i (p + (0, x))) (L t)‖ ≤ _
    rw [iteratedFDeriv_comp_add_right]
    exact hNorm j i (L t + (0, x))
  change iteratedDeriv k (fun t => ∑' i, u i t) 0 = _
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) hu (fun j _ => hV j)
      (fun j i t _ => hJu j i t) (by exact le_top)]
  let J := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ) ℝ (fun _ => 1)
  change J (∑' i, iteratedFDeriv ℝ k (u i) 0) = A k x
  have hs : Summable (fun i => iteratedFDeriv ℝ k (u i) 0) :=
    (hV k).of_norm_bounded (fun i => hJu k i 0)
  rw [J.map_tsum hs]
  have hEval (i : ℕ) : J (iteratedFDeriv ℝ k (u i) 0) = if i = k then A k x else 0 := by
    change iteratedDeriv k (fun t => transverseMonomial i (a i) t * A i x) 0 = _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_transverseMonomial_zero _ _ (ha i).1]
    by_cases he : i = k
    · simp [he]
    · simp [he, Ne.symm he]
  simp_rw [hEval]
  simp

end KEBall
