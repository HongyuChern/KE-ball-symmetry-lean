import KEBall.DirichletNormalizedPowerDifferences
import KEBall.DirichletFatouEnergy
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! A genuine tame bound for exponential composition and actual
normalized orthogonal differences. The proof uses finite product
expansions, the exponential series and Fatou's lemma. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace KEBall

theorem tendsto_dirichletIteratedFieldDifference_of_pointwise {n : ℕ}
    {F : ℕ → E n → ℝ} {f : E n → ℝ}
    (h : ∀ x, Tendsto (fun N => F N x) atTop (𝓝 (f x)))
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (k : ℕ) (x : E n) :
    Tendsto (fun N => dirichletIteratedFieldDifference R τ (F N) k x) atTop
      (𝓝 (dirichletIteratedFieldDifference R τ f k x)) := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih => exact ((ih (R x)).sub (ih x)).const_smul τ⁻¹

theorem dirichletLpSize_normalized_exp_difference_le {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {u : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n))
    (hBound : ∀ x ∈ unitBall n, |u x| ≤ 1) (a : ℝ) :
    dirichletLpSize (dirichletIteratedOrthogonalDifference R τ (fun x => Real.exp (a * u x)) k) 2 ≤
      (Real.exp ((2 : ℝ) ^ k * |a|) * (((4 * (k : ℝ)) ^ (k ^ 3)) ^ k)) *
        dirichletLpSize (dirichletIteratedOrthogonalDifference R τ u k) 2 := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  let P (N : ℕ) (x : E n) := ∑ m ∈ Finset.range N, (a ^ m / m.factorial) * u x ^ m
  let A : ℝ := ((4 * (k : ℝ)) ^ (k ^ 3)) ^ k
  let Y : ℝ := dirichletLpSize (dirichletIteratedOrthogonalDifference R τ u k) 2
  let c : ℝ := (2 : ℝ) ^ k * |a|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hY : 0 ≤ Y := dirichletLpSize_nonneg _ _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hSeries (z : ℝ) : HasSum (fun m : ℕ => z ^ m / m.factorial) (Real.exp z) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp z
  have hPC (N : ℕ) : ContinuousOn (P N) (closedUnitBall n) :=
    continuousOn_finsetSum _ (fun m _ => (hu.pow m).const_mul _)
  have hPartial (N : ℕ) :
      dirichletLpSize (dirichletIteratedOrthogonalDifference R τ (P N) k) 2 ≤
        (Real.exp c * A) * Y := by
    let F (m : ℕ) (x : E n) := (a ^ m / m.factorial) *
      dirichletIteratedOrthogonalDifference R τ (fun y => u y ^ m) k x
    have hFC (m : ℕ) : ContinuousOn (F m) (closedUnitBall n) :=
      (continuousOn_dirichletIteratedOrthogonalDifference R τ (hu.pow m) k).const_mul _
    have hD : dirichletIteratedOrthogonalDifference R τ (P N) k =
        fun x => ∑ m ∈ Finset.range N, F m x := by
      have h := dirichletIteratedFieldDifference_finsetSum R τ (Finset.range N)
        (fun m x => (a ^ m / m.factorial) * u x ^ m) k
      simpa only [dirichletIteratedFieldDifference_const_mul,
        dirichletIteratedFieldDifference_real] using h
    rw [hD]
    have hTerm (m : ℕ) : dirichletLpSize (F m) 2 ≤ (c ^ m / m.factorial) * (A * Y) := by
      rw [dirichletLpSize_const_mul _ _ (by norm_num : (0 : ℝ) < 2)]
      have hPow := dirichletLpSize_normalized_power_difference_le hn hk R hτ hu hBound m
      have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast (show m < 2 ^ m from Nat.lt_two_pow_self).le
      have hmk : (m : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ m := by
        calc
          _ ≤ ((2 : ℝ) ^ m) ^ k := pow_le_pow_left₀ (by positivity) hm k
          _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have hCoeff : |a ^ m / (m.factorial : ℝ)| * (m : ℝ) ^ k ≤ c ^ m / m.factorial := by
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m.factorial)]
        exact (mul_le_mul_of_nonneg_left hmk (by positivity)).trans_eq (by
          dsimp [c]; rw [mul_pow]; ring)
      calc
        _ ≤ |a ^ m / (m.factorial : ℝ)| * ((m : ℝ) ^ k * A * Y) :=
          mul_le_mul_of_nonneg_left hPow (abs_nonneg _)
        _ = (|a ^ m / (m.factorial : ℝ)| * (m : ℝ) ^ k) * (A * Y) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCoeff (mul_nonneg hA hY)
    have hSum := dirichletLpSize_two_finset_sum_le hn (Finset.range N) F (fun m _ => hFC m)
    have hS : (∑ m ∈ Finset.range N, c ^ m / m.factorial) ≤ Real.exp c := by
      rw [← (hSeries c).tsum_eq]
      exact Summable.sum_le_tsum (Finset.range N) (fun m _ => by positivity) (hSeries c).summable
    calc
      _ ≤ ∑ m ∈ Finset.range N, dirichletLpSize (F m) 2 := hSum
      _ ≤ ∑ m ∈ Finset.range N, (c ^ m / m.factorial) * (A * Y) :=
        Finset.sum_le_sum (fun m _ => hTerm m)
      _ = (∑ m ∈ Finset.range N, c ^ m / m.factorial) * (A * Y) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ Real.exp c * (A * Y) := mul_le_mul_of_nonneg_right hS (mul_nonneg hA hY)
      _ = _ := by ring
  have hPLim (x : E n) : Tendsto (fun N => P N x) atTop (𝓝 (Real.exp (a * u x))) := by
    simpa only [P, mul_pow, div_mul_eq_mul_div] using (hSeries (a * u x)).tendsto_sum_nat
  let D (N : ℕ) := dirichletIteratedOrthogonalDifference R τ (P N) k
  let f := dirichletIteratedOrthogonalDifference R τ (fun x => Real.exp (a * u x)) k
  have hDC (N : ℕ) : ContinuousOn (D N) (closedUnitBall n) :=
    continuousOn_dirichletIteratedOrthogonalDifference R τ (hPC N) k
  have hfC : ContinuousOn f (closedUnitBall n) :=
    continuousOn_dirichletIteratedOrthogonalDifference R τ
      (Real.continuous_exp.comp_continuousOn (hu.const_mul a)) k
  have hLim (x : E n) : Tendsto (fun N => D N x) atTop (𝓝 (f x)) := by
    simpa only [dirichletIteratedFieldDifference_real] using
      tendsto_dirichletIteratedFieldDifference_of_pointwise hPLim R τ k x
  have hInt (N : ℕ) : IntegrableOn (fun x => (D N x) ^ 2) (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn ((hDC N).pow 2) 1).integrable le_rfl
  have hMeas := (dirichlet_memLp_of_continuousOn hn (hfC.pow 2) 1).aestronglyMeasurable
  have hFatou := dirichlet_integrable_and_integral_le_of_ae_tendsto_nonneg
    (sq_nonneg ((Real.exp c * A) * Y)) hInt hMeas
    (fun _ => Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun x => (hLim x).pow 2))
    (Eventually.of_forall (fun N => by
      rw [← dirichletLpSize_two_sq]
      exact pow_le_pow_left₀ (dirichletLpSize_nonneg _ _) (hPartial N) 2))
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
    (mul_nonneg (mul_nonneg (Real.exp_pos c).le hA) hY)
  rw [dirichletLpSize_two_sq]
  exact hFatou.2

end KEBall
