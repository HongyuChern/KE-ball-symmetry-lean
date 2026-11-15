import KEBall.DirichletPowerDifferenceExpansion
import KEBall.DirichletFieldProductInterpolation
import KEBall.DirichletScalarL2Triangle

/-! Quantitative product estimates for bounded scalar potentials.
The count of positive-order factors is at most the total difference
order, independently of the number of undifferentiated factors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem integral_dirichlet_normalized_difference_monomial_sq_le {n m k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {u : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n))
    (hBound : ∀ x ∈ unitBall n, |u x| ≤ 1)
    (j : Fin m → ℕ) (hSum : ∑ i, j i = k) (Q : Fin m → E n ≃ₗᵢ[ℝ] E n) :
    (∫ x in unitBall n, ∏ i : Fin m,
      (dirichletIteratedOrthogonalDifference R τ u (j i) (Q i x)) ^ 2 ∂volume0 n) ≤
      ((((4 * (k : ℝ)) ^ (k ^ 3)) ^ k) *
        dirichletLpSize (dirichletIteratedOrthogonalDifference R τ u k) 2) ^ 2 := by
  classical
  let p : Finset (Fin m) := Finset.univ.filter (fun i => 0 < j i)
  have hps : p ⊆ Finset.univ := Finset.filter_subset _ _
  have hpj (i : Fin m) (hi : i ∈ p) : 0 < j i := (Finset.mem_filter.mp hi).2
  have hpSum : ∑ i ∈ p, j i = k := by
    calc
      _ = ∑ i, j i := Finset.sum_subset hps (fun i hi hip => by
        have hnot : ¬ 0 < j i := fun h => hip (Finset.mem_filter.mpr ⟨hi, h⟩)
        omega)
      _ = k := hSum
  have hpCard : p.card ≤ k := by
    calc
      p.card = ∑ _i ∈ p, 1 := by simp
      _ ≤ ∑ i ∈ p, j i := Finset.sum_le_sum (fun i hi => hpj i hi)
      _ = k := hpSum
  have hjk (i : Fin m) (_hi : i ∈ p) : j i ≤ k := by
    rw [← hSum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let A : ℝ := (4 * (k : ℝ)) ^ (k ^ 3)
  let Y : ℝ := dirichletLpSize (dirichletIteratedOrthogonalDifference R τ u k) 2
  have hA : 1 ≤ A := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 4 * k))
  have hY : 0 ≤ Y := dirichletLpSize_nonneg _ _
  let F (i : Fin m) (x : E n) := dirichletIteratedOrthogonalDifference R τ u (j i) (Q i x)
  have hFC (i : Fin m) : ContinuousOn (F i) (closedUnitBall n) :=
    continuousOn_dirichlet_orthogonal_comp
      (continuousOn_dirichletIteratedOrthogonalDifference R τ hu (j i)) (Q i)
  have hZero (i : Fin m) (hj0 : ¬ 0 < j i) (x : E n) (hx : x ∈ unitBall n) :
      (F i x) ^ 2 ≤ 1 := by
    have hje : j i = 0 := by omega
    have hxQ : Q i x ∈ unitBall n := by
      simpa only [unitBall, mem_ball_zero_iff, (Q i).norm_map] using hx
    have h := pow_le_pow_left₀ (abs_nonneg (u (Q i x))) (hBound (Q i x) hxQ) 2
    simpa only [F, hje, dirichletIteratedOrthogonalDifference, sq_abs, one_pow] using h
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      (∏ i : Fin m, (F i x) ^ 2) ≤ ∏ i ∈ p, (F i x) ^ 2 := by
    calc
      _ ≤ ∏ i : Fin m, if 0 < j i then (F i x) ^ 2 else 1 := by
        apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
        intro i _
        split_ifs with hji
        · exact le_rfl
        · exact hZero i hji x hx
      _ = _ := by rw [Finset.prod_ite]; simp only [Finset.prod_const_one, mul_one]; rfl
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hPC := continuousOn_finsetProd p (fun i _ => (hFC i).pow 2)
  have hSC := continuousOn_finsetProd Finset.univ (fun i _ => (hFC i).pow 2)
  have hI := setIntegral_mono_on (hInt hSC) (hInt hPC) measurableSet_ball hPoint
  have hP := integral_dirichlet_discrete_product_sq_le hn hk p R hτ (fun _ : Fin m => u)
    (fun _ _ => hu) j hpj hjk hpSum Q zero_le_one hY
    (fun _ _ => hBound) (fun _ _ => le_rfl)
  simp only [one_pow, mul_one] at hP
  have hPow : A ^ p.card ≤ A ^ k := pow_le_pow_right₀ hA hpCard
  exact hI.trans (hP.trans (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right hPow hY) 2))

private theorem orthogonal_pow_apply {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) (k : ℕ) (x : E n) :
    (R ^ k) x = R^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, LinearIsometryEquiv.coe_mul, Function.comp_apply, ih, Function.iterate_succ_apply]

theorem dirichletLpSize_normalized_power_difference_le {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {u : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n))
    (hBound : ∀ x ∈ unitBall n, |u x| ≤ 1) (m : ℕ) :
    dirichletLpSize (dirichletIteratedOrthogonalDifference R τ (fun x => u x ^ m) k) 2 ≤
      (m : ℝ) ^ k * (((4 * (k : ℝ)) ^ (k ^ 3)) ^ k) *
        dirichletLpSize (dirichletIteratedOrthogonalDifference R τ u k) 2 := by
  classical
  obtain ⟨L, hLen, hProfile, hExpansion⟩ :=
    dirichletIteratedFieldDifference_product_expansion R τ (fun _ : Fin m => u) k
  let F (p : (Fin m → ℕ) × (Fin m → ℕ)) (x : E n) :=
    dirichletDifferenceMonomial R τ Finset.univ (fun _ : Fin m => u) p.1 p.2 x
  have hFE (p : (Fin m → ℕ) × (Fin m → ℕ)) (x : E n) :
      F p x = ∏ i : Fin m, dirichletIteratedOrthogonalDifference R τ u (p.1 i) ((R ^ p.2 i) x) := by
    simp only [F, dirichletDifferenceMonomial, orthogonal_pow_apply,
      dirichletIteratedFieldDifference_real]
  have hFC (p : (Fin m → ℕ) × (Fin m → ℕ)) : ContinuousOn (F p) (closedUnitBall n) := by
    rw [show F p = (fun x => ∏ i : Fin m,
      dirichletIteratedOrthogonalDifference R τ u (p.1 i) ((R ^ p.2 i) x)) from funext (hFE p)]
    apply continuousOn_finsetProd
    intro i _
    exact continuousOn_dirichlet_orthogonal_comp
      (continuousOn_dirichletIteratedOrthogonalDifference R τ hu (p.1 i)) (R ^ p.2 i)
  let C : ℝ := (((4 * (k : ℝ)) ^ (k ^ 3)) ^ k) *
    dirichletLpSize (dirichletIteratedOrthogonalDifference R τ u k) 2
  have hC : 0 ≤ C := mul_nonneg (by positivity) (dirichletLpSize_nonneg _ _)
  have hBoundF (p : (Fin m → ℕ) × (Fin m → ℕ)) (hp : p ∈ L) :
      dirichletLpSize (F p) 2 ≤ C := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hC
    rw [dirichletLpSize_two_sq]
    simp only [hFE, ← Finset.prod_pow]
    exact integral_dirichlet_normalized_difference_monomial_sq_le hn hk R hτ hu hBound
      p.1 (hProfile p hp) (fun i => R ^ p.2 i)
  have hEq : dirichletIteratedOrthogonalDifference R τ (fun x => u x ^ m) k =
      fun x => (L.map (fun p => F p x)).sum := by
    funext x
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      dirichletIteratedFieldDifference_real] using hExpansion x
  rw [hEq]
  have hSum := dirichletLpSize_two_list_sum_le hn L F (fun p _ => hFC p)
  refine hSum.trans ?_
  calc
    _ ≤ (L.map (fun _ => C)).sum := List.sum_le_sum hBoundF
    _ = (L.length : ℝ) * C := by simp
    _ = _ := by rw [hLen, Nat.cast_pow]; dsimp [C]; ring

end KEBall
