import KEBall.DirichletTensorDifferences
import KEBall.DirichletDiscreteQuarticInterpolation

/-! Discrete quartic interpolation for continuous bilinear fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem abs_dirichlet_bilinear_entry_le_norm {n : ℕ}
    (H : E n →L[ℝ] E n →L[ℝ] ℝ) (i j : Fin (2 * n)) :
    |H (e[n] i) (e[n] j)| ≤ ‖H‖ := by
  simpa only [Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one] using
    H.le_opNorm₂ (e[n] i) (e[n] j)

theorem norm_dirichlet_bilinear_pow_four_le_sum_entries {n : ℕ}
    (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖H‖ ^ 4 ≤ (2 * n : ℝ) ^ 6 *
      ∑ i, ∑ j, (H (e[n] i) (e[n] j)) ^ 4 := by
  have hNorm := pow_le_pow_left₀ (sq_nonneg ‖H‖)
    (norm_dirichlet_bilinear_sq_le_sum_entries H) 2
  let f (s : Fin (2 * n) × Fin (2 * n)) := (H (e[n] s.1) (e[n] s.2)) ^ 2
  have hSum := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
  simp only [f, Fintype.sum_prod_type, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, ← pow_mul] at hSum
  norm_num only at hSum
  calc
    ‖H‖ ^ 4 ≤ (2 * n : ℝ) ^ 4 * (∑ i, ∑ j, (H (e[n] i) (e[n] j)) ^ 2) ^ 2 := by
      simpa only [mul_pow, ← pow_mul, show 2 * 2 = 4 by norm_num] using hNorm
    _ ≤ (2 * n : ℝ) ^ 4 * ((2 * n : ℝ) ^ 2 *
        ∑ i, ∑ j, (H (e[n] i) (e[n] j)) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using hSum
    _ = _ := by ring

theorem integral_dirichletFieldDifference_norm_pow_four_le {n : ℕ}
    (hn : 0 < n) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {H : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hH : ContinuousOn H (closedUnitBall n)) {ε : ℝ} (hε : 0 ≤ ε)
    (hBound : ∀ x ∈ unitBall n, ‖H x‖ ≤ ε) :
    (∫ x in unitBall n, ‖dirichletFieldDifference R τ H x‖ ^ 4 ∂volume0 n) ≤
      36 * (2 * n : ℝ) ^ 8 * ε ^ 2 * ∫ x in unitBall n,
        ‖dirichletFieldDifference R τ (dirichletFieldDifference R τ H) x‖ ^ 2 ∂volume0 n := by
  let D := dirichletFieldDifference R τ H
  let Q := dirichletFieldDifference R τ D
  have hD := continuousOn_dirichletFieldDifference R τ hH
  have hQ := continuousOn_dirichletFieldDifference R τ hD
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hEntry (i j : Fin (2 * n)) :
      (∫ x in unitBall n, (D x (e[n] i) (e[n] j)) ^ 4 ∂volume0 n) ≤
        36 * ε ^ 2 * ∫ x in unitBall n, ‖Q x‖ ^ 2 ∂volume0 n := by
    have hC : ContinuousOn (fun x => H x (e[n] i) (e[n] j)) (closedUnitBall n) :=
      (hH.clm_apply continuousOn_const).clm_apply continuousOn_const
    have hCq : ContinuousOn (fun x => Q x (e[n] i) (e[n] j)) (closedUnitBall n) :=
      (hQ.clm_apply continuousOn_const).clm_apply continuousOn_const
    have h := integral_dirichletOrthogonalDifference_pow_four_le hn R hτ hC hε
      (fun x hx => (abs_dirichlet_bilinear_entry_le_norm (H x) i j).trans (hBound x hx))
    have he (x : E n) : D x (e[n] i) (e[n] j) =
        dirichletOrthogonalDifference R τ (fun y => H y (e[n] i) (e[n] j)) x :=
      dirichletFieldDifference_bilinear_apply R τ H x _ _
    have hq (x : E n) : Q x (e[n] i) (e[n] j) =
        dirichletOrthogonalDifference R τ
          (dirichletOrthogonalDifference R τ (fun y => H y (e[n] i) (e[n] j))) x := by
      rw [dirichletFieldDifference_bilinear_apply R τ D]
      simp only [he]
    simp only [← he, ← hq] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (setIntegral_mono_on (hInt (hCq.pow 2)) (hInt (hQ.norm.pow 2)) measurableSet_ball
        (fun x _ => by
          have h := pow_le_pow_left₀ (abs_nonneg (Q x (e[n] i) (e[n] j)))
            (abs_dirichlet_bilinear_entry_le_norm (Q x) i j) 2
          simpa only [sq_abs] using h)) (by positivity))
  have hDc (i j : Fin (2 * n)) :
      ContinuousOn (fun x => (D x (e[n] i) (e[n] j)) ^ 4) (closedUnitBall n) :=
    ((hD.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 4
  have hSumC : ContinuousOn (fun x => ∑ i, ∑ j,
      (D x (e[n] i) (e[n] j)) ^ 4) (closedUnitBall n) :=
    continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => hDc i j))
  have hNorm := setIntegral_mono_on (hInt (hD.norm.pow 4))
    (hInt (hSumC.const_mul ((2 * n : ℝ) ^ 6))) measurableSet_ball
    (fun x _ => norm_dirichlet_bilinear_pow_four_le_sum_entries (D x))
  rw [integral_const_mul] at hNorm
  have hSwap : (∫ x in unitBall n, ∑ i, ∑ j,
      (D x (e[n] i) (e[n] j)) ^ 4 ∂volume0 n) =
      ∑ i, ∑ j, ∫ x in unitBall n, (D x (e[n] i) (e[n] j)) ^ 4 ∂volume0 n := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hInt (hDc i j)))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finset_sum _ (fun j _ => hInt (hDc i j))
  rw [hSwap] at hNorm
  refine hNorm.trans ?_
  calc
    _ ≤ (2 * n : ℝ) ^ 6 * ∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n),
        (36 * ε ^ 2 * ∫ x in unitBall n, ‖Q x‖ ^ 2 ∂volume0 n) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEntry i j))) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring

end KEBall
