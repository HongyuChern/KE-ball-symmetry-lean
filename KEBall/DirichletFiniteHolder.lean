import KEBall.DirichletDiscreteDifferences
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Finite-product Holder bounds on the actual normalized ball measure. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace KEBall

theorem dirichlet_integral_prod_rpow_le {n : ℕ} (hn : 0 < n) {ι : Type*}
    (s : Finset ι) (g : ι → E n → ℝ)
    (hg : ∀ i ∈ s, ContinuousOn (g i) (closedUnitBall n))
    (hg0 : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (θ : ι → ℝ) (hθ : ∀ i ∈ s, 0 ≤ θ i) (hSum : ∑ i ∈ s, θ i = 1) :
    (∫ x in unitBall n, ∏ i ∈ s, (g i x) ^ θ i ∂volume0 n) ≤
      ∏ i ∈ s, (∫ x in unitBall n, g i x ∂volume0 n) ^ θ i := by
  classical
  let μ := (volume0 n).restrict (unitBall n)
  let : NeZero n := ⟨hn.ne'⟩
  let : IsProbabilityMeasure μ := volume0_restrict_isProbability n
  have hInt (i : ι) (hi : i ∈ s) : Integrable (g i) μ :=
    (dirichlet_memLp_of_continuousOn hn (hg i hi) 1).integrable le_rfl
  have hPC : ContinuousOn (fun x => ∏ i ∈ s, (g i x) ^ θ i) (closedUnitBall n) :=
    continuousOn_finsetProd s (fun i hi => (hg i hi).rpow_const (fun _ _ => Or.inr (hθ i hi)))
  have hPI : Integrable (fun x => ∏ i ∈ s, (g i x) ^ θ i) μ :=
    (dirichlet_memLp_of_continuousOn hn hPC 1).integrable le_rfl
  have hPN (x : E n) : 0 ≤ ∏ i ∈ s, (g i x) ^ θ i :=
    Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hg0 i hi x) _)
  have hOfProd (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
      ENNReal.ofReal (∏ i ∈ s, (z i) ^ θ i) =
        ∏ i ∈ s, (ENNReal.ofReal (z i)) ^ θ i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i hi => Real.rpow_nonneg (hz i hi) _)]
    exact Finset.prod_congr rfl (fun i hi => (ENNReal.ofReal_rpow_of_nonneg (hz i hi) (hθ i hi)).symm)
  have hL : ENNReal.ofReal (∫ x, ∏ i ∈ s, (g i x) ^ θ i ∂μ) =
      ∫⁻ x, ∏ i ∈ s, (ENNReal.ofReal (g i x)) ^ θ i ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hPI (Eventually.of_forall hPN)]
    exact lintegral_congr (fun x => hOfProd (fun i => g i x) (fun i hi => hg0 i hi x))
  have hI0 (i : ι) (hi : i ∈ s) : 0 ≤ ∫ x, g i x ∂μ := integral_nonneg (hg0 i hi)
  have hR : ENNReal.ofReal (∏ i ∈ s, (∫ x, g i x ∂μ) ^ θ i) =
      ∏ i ∈ s, (∫⁻ x, ENNReal.ofReal (g i x) ∂μ) ^ θ i := by
    rw [hOfProd (fun i => ∫ x, g i x ∂μ) hI0]
    apply Finset.prod_congr rfl
    intro i hi
    rw [ofReal_integral_eq_lintegral_ofReal (hInt i hi) (Eventually.of_forall (hg0 i hi))]
  have hMeas (i : ι) (hi : i ∈ s) : AEMeasurable (fun x => ENNReal.ofReal (g i x)) μ :=
    (((hg i hi).mono ball_subset_closedBall).aemeasurable measurableSet_ball).ennreal_ofReal
  have h := ENNReal.lintegral_prod_norm_pow_le s hMeas hSum hθ
  rw [← hL, ← hR] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hI0 i hi) _))).mp h

theorem dirichlet_integral_prod_sq_le_lp_sizes {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {ι : Type*} (s : Finset ι) (F : ι → E n → ℝ)
    (hF : ∀ i ∈ s, ContinuousOn (F i) (closedUnitBall n))
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hSum : ∑ i ∈ s, j i = k) :
    (∫ x in unitBall n, ∏ i ∈ s, (F i x) ^ 2 ∂volume0 n) ≤
      ∏ i ∈ s, (dirichletLpSize (F i) (2 * (k : ℝ) / j i)) ^ 2 := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hjR (i : ι) (hi : i ∈ s) : (0 : ℝ) < j i := by exact_mod_cast hj i hi
  let p (i : ι) : ℝ := 2 * (k : ℝ) / j i
  let θ (i : ι) : ℝ := (j i : ℝ) / k
  have hp (i : ι) (hi : i ∈ s) : 0 < p i := div_pos (by positivity) (hjR i hi)
  have hθ (i : ι) (hi : i ∈ s) : 0 ≤ θ i := div_nonneg (Nat.cast_nonneg _) hkR.le
  have hθSum : ∑ i ∈ s, θ i = 1 := by
    dsimp only [θ]
    rw [← Finset.sum_div, ← Nat.cast_sum, hSum, div_self hkR.ne']
  have h := dirichlet_integral_prod_rpow_le hn s (fun i x => |F i x| ^ p i)
    (fun i hi => (hF i hi).abs.rpow_const (fun _ _ => Or.inr (hp i hi).le))
    (fun i hi x => Real.rpow_nonneg (abs_nonneg _) _) θ hθ hθSum
  have hLeft (x : E n) : (∏ i ∈ s, (|F i x| ^ p i) ^ θ i) = ∏ i ∈ s, (F i x) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_mul (abs_nonneg _)]
    have he : p i * θ i = 2 := by dsimp [p, θ]; field_simp [(hjR i hi).ne', hkR.ne']
    rw [he, Real.rpow_two, sq_abs]
  have hRight (i : ι) (hi : i ∈ s) :
      (∫ x in unitBall n, |F i x| ^ p i ∂volume0 n) ^ θ i =
        (dirichletLpSize (F i) (p i)) ^ 2 := by
    unfold dirichletLpSize
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul
      (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))]
    congr 1
    dsimp [p, θ]
    field_simp
  simp_rw [hLeft] at h
  have he : (∏ i ∈ s, (∫ x in unitBall n, |F i x| ^ p i ∂volume0 n) ^ θ i) =
      ∏ i ∈ s, (dirichletLpSize (F i) (p i)) ^ 2 :=
    Finset.prod_congr rfl hRight
  exact h.trans_eq he

theorem dirichlet_product_power_interpolation {ι : Type*} (s : Finset ι)
    {k : ℕ} (hk : 0 < k) (j : ι → ℕ)
    (hj : ∀ i ∈ s, j i ≤ k) (hSum : ∑ i ∈ s, j i = k)
    (L : ι → ℝ) (hL : ∀ i ∈ s, 0 ≤ L i)
    {A B Y : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hI : ∀ i ∈ s, L i ^ k ≤ A * B ^ (k - j i) * Y ^ j i) :
    (∏ i ∈ s, L i) ≤ A ^ s.card * B ^ (s.card - 1) * Y := by
  classical
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hExpAdd : (∑ i ∈ s, (k - j i)) + k = s.card * k := by
    calc
      _ = (∑ i ∈ s, (k - j i)) + ∑ i ∈ s, j i := by rw [hSum]
      _ = ∑ i ∈ s, (k - j i + j i) := (Finset.sum_add_distrib).symm
      _ = ∑ _i ∈ s, k := Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hj i hi))
      _ = _ := by simp
  have hExp : (∑ i ∈ s, (k - j i)) = (s.card - 1) * k := by
    rw [Nat.sub_mul, one_mul]
    omega
  have hP : (∏ i ∈ s, L i) ^ k ≤ A ^ s.card * B ^ ((s.card - 1) * k) * Y ^ k := by
    calc
      _ = ∏ i ∈ s, L i ^ k := (Finset.prod_pow s k L).symm
      _ ≤ ∏ i ∈ s, (A * B ^ (k - j i) * Y ^ j i) :=
        Finset.prod_le_prod (fun i hi => pow_nonneg (hL i hi) k) hI
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hSum, hExp]
  have hAPow : A ^ s.card ≤ (A ^ s.card) ^ k := le_self_pow₀ (one_le_pow₀ hA) hk.ne'
  have hCap := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAPow (pow_nonneg hB ((s.card - 1) * k))) (pow_nonneg hY k)
  apply le_of_pow_le_pow_left₀ hk.ne' (by positivity)
  exact hP.trans (hCap.trans_eq (by simp only [mul_pow, ← pow_mul]))

theorem integral_dirichlet_discrete_proper_product_sq_le {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} (s : Finset ι)
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    (F : ι → E n → ℝ) (hF : ∀ i ∈ s, ContinuousOn (F i) (closedUnitBall n))
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k)
    (Q : ι → E n ≃ₗᵢ[ℝ] E n)
    {B Y : ℝ} (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hBase : ∀ i ∈ s, ∀ x ∈ unitBall n, |F i x| ≤ B)
    (hTop : ∀ i ∈ s, dirichletLpSize (dirichletIteratedOrthogonalDifference R τ (F i) k) 2 ≤ Y) :
    (∫ x in unitBall n, ∏ i ∈ s,
      (dirichletIteratedOrthogonalDifference R τ (F i) (j i) (Q i x)) ^ 2 ∂volume0 n) ≤
      (((4 * (k : ℝ)) ^ (k ^ 3)) ^ s.card * B ^ (s.card - 1) * Y) ^ 2 := by
  classical
  let A : ℝ := (4 * (k : ℝ)) ^ (k ^ 3)
  let G (i : ι) (x : E n) := dirichletIteratedOrthogonalDifference R τ (F i) (j i) (Q i x)
  let L (i : ι) := dirichletLpSize (G i) (2 * (k : ℝ) / j i)
  have hA : 1 ≤ A := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 4 * k))
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hG (i : ι) (hi : i ∈ s) : ContinuousOn (G i) (closedUnitBall n) :=
    continuousOn_dirichlet_orthogonal_comp
      (continuousOn_dirichletIteratedOrthogonalDifference R τ (hF i hi) (j i)) (Q i)
  have hL (i : ι) (hi : i ∈ s) : 0 ≤ L i := dirichletLpSize_nonneg _ _
  have hI (i : ι) (hi : i ∈ s) : L i ^ k ≤ A * B ^ (k - j i) * Y ^ j i := by
    have hGN := dirichlet_iterated_difference_gagliardo_nirenberg hn hk R hτ
      (hF i hi) hB (hBase i hi) (hj i hi) (hjk i hi)
    have hBound := hGN.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (dirichletLpSize_nonneg _ _) (hTop i hi) (j i))
      (mul_nonneg hA0 (pow_nonneg hB _)))
    simpa only [L, G, dirichletLpSize_orthogonal_comp, A] using hBound
  have hProd := dirichlet_product_power_interpolation s (by omega : 0 < k) j
    (fun i hi => (hjk i hi).le) hSum L hL hA hB hY hI
  have hHolder := dirichlet_integral_prod_sq_le_lp_sizes hn (by omega : 0 < k) s G hG j hj hSum
  have hPow := pow_le_pow_left₀ (Finset.prod_nonneg hL) hProd 2
  calc
    _ ≤ ∏ i ∈ s, L i ^ 2 := hHolder
    _ = (∏ i ∈ s, L i) ^ 2 := Finset.prod_pow s 2 L
    _ ≤ _ := hPow

end KEBall
