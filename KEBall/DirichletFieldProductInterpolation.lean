import KEBall.DirichletFiniteHolder
import KEBall.DirichletIteratedTensorDifferences
import KEBall.DirichletDiscreteQuarticInterpolation
import KEBall.DirichletHessianProperProductAbsorption

/-! Product interpolation including a highest-order factor and arbitrary real linear forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

theorem integral_dirichlet_discrete_product_sq_le {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {ι : Type*} (s : Finset ι)
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    (F : ι → E n → ℝ) (hF : ∀ i ∈ s, ContinuousOn (F i) (closedUnitBall n))
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i ≤ k)
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
    by_cases he : j i = k
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hp : 2 * (k : ℝ) / j i = 2 := by rw [he]; field_simp [hkR.ne']
      have hLi : L i ≤ Y := by
        dsimp only [L, G]
        rw [hp, dirichletLpSize_orthogonal_comp, he]
        exact hTop i hi
      calc
        L i ^ k ≤ Y ^ k := pow_le_pow_left₀ (hL i hi) hLi k
        _ ≤ A * Y ^ k := le_mul_of_one_le_left (pow_nonneg hY k) hA
        _ = A * B ^ (k - j i) * Y ^ j i := by rw [he, Nat.sub_self, pow_zero, mul_one]
    have hiLt : j i < k := lt_of_le_of_ne (hjk i hi) he
    have hk2 : 2 ≤ k := by have hpos := hj i hi; omega
    have hGN := dirichlet_iterated_difference_gagliardo_nirenberg hn hk2 R hτ
      (hF i hi) hB (hBase i hi) (hj i hi) hiLt
    have hBound := hGN.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (dirichletLpSize_nonneg _ _) (hTop i hi) (j i))
      (mul_nonneg hA0 (pow_nonneg hB _)))
    simpa only [L, G, dirichletLpSize_orthogonal_comp, A] using hBound
  have hProd := dirichlet_product_power_interpolation s (by omega : 0 < k) j
    (fun i hi => hjk i hi) hSum L hL hA hB hY hI
  have hHolder := dirichlet_integral_prod_sq_le_lp_sizes hn (by omega : 0 < k) s G hG j hj hSum
  have hPow := pow_le_pow_left₀ (Finset.prod_nonneg hL) hProd 2
  calc
    _ ≤ ∏ i ∈ s, L i ^ 2 := hHolder
    _ = (∏ i ∈ s, L i) ^ 2 := Finset.prod_pow s 2 L
    _ ≤ _ := hPow


theorem integral_dirichlet_linearForm_product_sq_le {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Finset ι)
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {H : E n → V} (hH : ContinuousOn H (closedUnitBall n))
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i ≤ k)
    (hSum : ∑ i ∈ s, j i = k)
    (Q : ι → E n ≃ₗᵢ[ℝ] E n) (L : ι → V →L[ℝ] ℝ)
    {Λ B : ℝ} (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (hL : ∀ i ∈ s, ‖L i‖ ≤ Λ) (hBound : ∀ x ∈ unitBall n, ‖H x‖ ≤ B) :
    (∫ x in unitBall n, ∏ i ∈ s,
      (L i (dirichletIteratedFieldDifference R τ H (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
      (((4 * (k : ℝ)) ^ (k ^ 3)) ^ s.card * (Λ * B) ^ (s.card - 1) * Λ) ^ 2 *
        ∫ x in unitBall n, ‖dirichletIteratedFieldDifference R τ H k x‖ ^ 2 ∂volume0 n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  let F (i : ι) (x : E n) := L i (H x)
  let K := dirichletIteratedFieldDifference R τ H k
  let Y := dirichletLpSize (fun x => ‖K x‖) 2
  have hY : 0 ≤ Y := dirichletLpSize_nonneg _ _
  have hK : ContinuousOn K (closedUnitBall n) := continuousOn_dirichletIteratedFieldDifference R τ hH k
  have hF (i : ι) : ContinuousOn (F i) (closedUnitBall n) := (L i).continuous.comp_continuousOn hH
  have hLin (i : ι) (hi : i ∈ s) (v : V) : |L i v| ≤ Λ * ‖v‖ := by
    have h := (L i).le_opNorm v
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hL i hi) (norm_nonneg _))
  have hEq (i : ι) (l : ℕ) (x : E n) :
      dirichletIteratedOrthogonalDifference R τ (F i) l x =
        L i (dirichletIteratedFieldDifference R τ H l x) := by
    simpa only [dirichletIteratedFieldDifference_real] using congrArg (fun f => f x)
      (dirichletIteratedFieldDifference_clm R τ (L i) H l)
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hTop (i : ι) (hi : i ∈ s) :
      dirichletLpSize (dirichletIteratedOrthogonalDifference R τ (F i) k) 2 ≤ Λ * Y := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (mul_nonneg hΛ hY)
    rw [mul_pow, dirichletLpSize_two_sq, dirichletLpSize_two_sq]
    simp only [hEq]
    rw [← integral_const_mul]
    exact setIntegral_mono_on
      (hInt (((L i).continuous.comp_continuousOn hK).pow 2))
      (hInt ((hK.norm.pow 2).const_mul (Λ ^ 2))) measurableSet_ball (fun x _ => by
        simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hLin i hi (K x)) 2)
  have h := integral_dirichlet_discrete_product_sq_le hn hk s R hτ F
    (fun i _ => hF i) j hj hjk hSum Q (mul_nonneg hΛ hB) (mul_nonneg hΛ hY)
    (fun i hi x hx => (hLin i hi (H x)).trans (mul_le_mul_of_nonneg_left (hBound x hx) hΛ)) hTop
  simp only [hEq] at h
  refine h.trans_eq ?_
  calc
    _ = (((4 * (k : ℝ)) ^ (k ^ 3)) ^ s.card * (Λ * B) ^ (s.card - 1) * Λ) ^ 2 * Y ^ 2 := by ring
    _ = _ := by rw [dirichletLpSize_two_sq]

theorem exists_dirichlet_linearForm_proper_product_small_scale {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ), τ ≠ 0 →
      ∀ (H : E n → V), ContinuousOn H (closedUnitBall n) → (∀ x ∈ unitBall n, ‖H x‖ ≤ η) →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n) (L : ι → V →L[ℝ] ℝ), (∀ i ∈ s, ‖L i‖ ≤ Λ) →
      (∫ x in unitBall n, ∏ i ∈ s,
        (L i (dirichletIteratedFieldDifference R τ H (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
        ε * ∫ x in unitBall n, ‖dirichletIteratedFieldDifference R τ H k x‖ ^ 2 ∂volume0 n := by
  have hr := dirichlet_proper_order_product_card_ge_two s (by omega) j hjk hSum
  have hr0 : s.card - 1 ≠ 0 := by omega
  let P (η : ℝ) := (((4 * (k : ℝ)) ^ (k ^ 3)) ^ s.card * (Λ * η) ^ (s.card - 1) * Λ) ^ 2
  have hPC : ContinuousAt P 0 := by dsimp [P]; fun_prop
  have hP0 : P 0 < ε := by
    simpa only [P, mul_zero, zero_pow hr0, zero_mul, zero_pow (by decide : 2 ≠ 0)] using hε
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp (hPC.eventually (gt_mem_nhds hP0))
  have hη : 0 < δ / 2 := by positivity
  have hSmall : P (δ / 2) ≤ ε := (hδb (by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hη]
    linarith)).le
  refine ⟨δ / 2, hη, ?_⟩
  intro R τ hτ H hH hBound Q L hL
  exact (integral_dirichlet_linearForm_product_sq_le hn (by omega) s R hτ hH j hj
    (fun i hi => (hjk i hi).le) hSum Q L hΛ hη.le hL hBound).trans
      (mul_le_mul_of_nonneg_right hSmall (integral_nonneg (fun _ => sq_nonneg _)))

theorem exists_dirichlet_hessian_linearForm_reference_absorption {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ closedUnitBall n, ‖dirichletWithinRealHessian u x - realHessian v x‖ < 1) ∧
      ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ), (∀ i ∈ s, ‖L i‖ ≤ Λ) →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∏ i ∈ s,
        (L i (dirichletIteratedFieldDifference R t
          (fun y => dirichletWithinRealHessian u y - realHessian v y) (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
        ε * (∑ m ∈ Finset.range (k + 1), ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u m) x‖ ^ 2 ∂volume0 n) + C := by
  classical
  let K : ℝ := 2 * (k + 1 : ℝ) * ((1 + 2 * ‖S‖) ^ k) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let ε' := ε / (K + 1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨η, hη, hProd⟩ := exists_dirichlet_linearForm_proper_product_small_scale
    (V := E n →L[ℝ] E n →L[ℝ] ℝ) hn hk s j hj hjk hSum hΛ hε'
  obtain ⟨v, hv, hv0, hApprox, _⟩ :=
    exists_dirichlet_smooth_zeroBoundary_reference_close_hessian hu huS hu0 (lt_min hη zero_lt_one)
  have hV (x : E n) (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ (realHessian v) x :=
    realHessian_contDiffAt (hv.contDiffAt hx)
  obtain ⟨C, hC, hEnergy⟩ := exists_integral_dirichlet_hessian_reference_difference_bound hn hu hV S hS k
  refine ⟨v, hv, hv0, fun x hx => (hApprox x hx).trans_le (min_le_right _ _),
    ε' * C, mul_nonneg hε'.le hC, ?_⟩
  intro t ht Q L hL
  dsimp only
  have hZC : ContinuousOn (fun y => dirichletWithinRealHessian u y - realHessian v y)
      (closedUnitBall n) := (continuousOn_dirichletWithinRealHessian hu).sub
    (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
  have hP := hProd (orthogonalFlow S hS t) t ht _ hZC
    (fun x hx => (hApprox x (ball_subset_closedBall hx)).le.trans (min_le_left _ _)) Q L hL
  have hE := mul_le_mul_of_nonneg_left (hEnergy t ht) hε'.le
  have hCap : ε' * K ≤ ε := by
    calc
      ε' * K ≤ ε' * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'.le
      _ = ε := by dsimp [ε']; exact div_mul_cancel₀ ε (by positivity : K + 1 ≠ 0)
  have hSum0 : 0 ≤ ∑ m ∈ Finset.range (k + 1), ∫ x in unitBall n,
      ‖dirichletWithinRealHessian
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u m) x‖ ^ 2 ∂volume0 n :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact hP.trans (hE.trans (by
    rw [mul_add, ← mul_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_right hCap hSum0) le_rfl))

end KEBall
