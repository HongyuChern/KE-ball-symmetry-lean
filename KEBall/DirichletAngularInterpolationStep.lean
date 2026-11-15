import KEBall.DirichletAngularPowerIdentity
import KEBall.DirichletHolderThree

/-! Actual angular Lp interpolation steps on the normalized ball measure. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace KEBall

noncomputable def dirichletLpSize {n : ℕ} (f : E n → ℝ) (p : ℝ) : ℝ :=
  (∫ x in unitBall n, |f x| ^ p ∂volume0 n) ^ (1 / p)

theorem dirichletLpSize_nonneg {n : ℕ} (f : E n → ℝ) (p : ℝ) :
    0 ≤ dirichletLpSize f p :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _

private theorem power_cancel {I K p : ℝ} (hI : 0 ≤ I) (hK : 0 ≤ K) (hp : 0 < p)
    (h : I ≤ K * I ^ ((p - 2) / p)) : I ^ (2 / p) ≤ K := by
  rcases eq_or_lt_of_le hI with hZero | hPos
  · rw [← hZero, Real.zero_rpow (ne_of_gt (div_pos (by norm_num) hp))]
    exact hK
  · have he : (2 / p : ℝ) + (p - 2) / p = 1 := by
      field_simp [hp.ne'] <;> ring
    have hSplit : I = I ^ (2 / p) * I ^ ((p - 2) / p) := by
      rw [← Real.rpow_add hPos, he, Real.rpow_one]
    have h' : I ^ (2 / p) * I ^ ((p - 2) / p) ≤ K * I ^ ((p - 2) / p) :=
      hSplit.symm.trans_le h
    exact le_of_mul_le_mul_right h' (Real.rpow_pos_of_pos hPos _)

private theorem lpSize_sq {n : ℕ} (g : E n → ℝ) (p : ℝ) :
    dirichletLpSize g p ^ 2 =
      (∫ x in unitBall n, |g x| ^ p ∂volume0 n) ^ (2 / p) := by
  unfold dirichletLpSize
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)]
  congr 1
  ring

theorem integral_dirichlet_angular_power_le_abs {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f g h : E n → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hh : ContinuousOn h (closedUnitBall n))
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hDf : ∀ x ∈ unitBall n, fderiv ℝ f x (T x) = g x)
    (hDg : ∀ x ∈ unitBall n, fderiv ℝ g x (T x) = h x)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x in unitBall n, |g x| ^ p ∂volume0 n) ≤
      (p - 1) * ∫ x in unitBall n, |f x| * |g x| ^ (p - 2) * |h x| ∂volume0 n := by
  have hId := integral_dirichlet_angular_power_identity hn hU hSub hf hg T hT hDf hDg
    (show 0 ≤ p - 2 by linarith)
  rw [show p - 2 + 2 = p by ring, show p - 2 + 1 = p - 1 by ring] at hId
  have hAbs : |∫ x in unitBall n, f x * |g x| ^ (p - 2) * h x ∂volume0 n| ≤
      ∫ x in unitBall n, |f x| * |g x| ^ (p - 2) * |h x| ∂volume0 n := by
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
      norm_integral_le_integral_norm (fun x => f x * |g x| ^ (p - 2) * h x)
  rw [hId]
  calc
    _ = (p - 1) * (-(∫ x in unitBall n, f x * |g x| ^ (p - 2) * h x ∂volume0 n)) := by ring
    _ ≤ (p - 1) * |∫ x in unitBall n, f x * |g x| ^ (p - 2) * h x ∂volume0 n| :=
      mul_le_mul_of_nonneg_left (neg_le_abs _) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left hAbs (by linarith)

theorem dirichlet_angular_lp_logconvex {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f g h : E n → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hh : ContinuousOn h (closedUnitBall n))
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hDf : ∀ x ∈ unitBall n, fderiv ℝ f x (T x) = g x)
    (hDg : ∀ x ∈ unitBall n, fderiv ℝ g x (T x) = h x)
    {p a c : ℝ} (hp : 2 < p) (ha : 0 < a) (hc : 0 < c)
    (hBalance : a⁻¹ + c⁻¹ = 2 / p) :
    dirichletLpSize g p ^ 2 ≤ (p - 1) * dirichletLpSize f a * dirichletLpSize h c := by
  let μ := (volume0 n).restrict (unitBall n)
  let I : ℝ := ∫ x, |g x| ^ p ∂μ
  let β : ℝ := p / (p - 2)
  have hp0 : 0 < p := by linarith
  have hβ : 0 < β := div_pos hp0 (by linarith)
  have hABC : a⁻¹ + β⁻¹ + c⁻¹ = 1 := by
    rw [show β⁻¹ = (p - 2) / p by dsimp [β]; rw [inv_div]]
    calc
      _ = (a⁻¹ + c⁻¹) + (p - 2) / p := by ring
      _ = 1 := by rw [hBalance]; field_simp [hp0.ne'] <;> ring
  have hHolder := dirichlet_integral_three_holder_nonneg hn
    (fun x => |f x|) (fun x => |g x| ^ (p - 2)) (fun x => |h x|)
    ((hf.continuousOn.mono hSub).abs)
    (((hg.continuousOn.mono hSub).abs).rpow_const (fun _ _ => Or.inr (by linarith)))
    hh.abs (fun _ => abs_nonneg _) (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (fun _ => abs_nonneg _) ha hβ hc hABC
  have hPow : (fun x => (|g x| ^ (p - 2)) ^ β) = fun x => |g x| ^ p := by
    funext x
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    dsimp [β]
    field_simp [(sub_pos.mpr hp).ne']
  have hInv : 1 / β = (p - 2) / p := by dsimp [β]; rw [one_div_div]
  rw [hPow, hInv] at hHolder
  have hIBP := integral_dirichlet_angular_power_le_abs hn hU hSub hf hg hh T hT hDf hDg hp.le
  have hBound : I ≤
      ((p - 1) * dirichletLpSize f a * dirichletLpSize h c) * I ^ ((p - 2) / p) := by
    calc
      I ≤ (p - 1) * ∫ x, |f x| * |g x| ^ (p - 2) * |h x| ∂μ := hIBP
      _ ≤ (p - 1) * ((dirichletLpSize f a) *
        (I ^ ((p - 2) / p) * dirichletLpSize h c)) :=
          mul_le_mul_of_nonneg_left hHolder (by linarith)
      _ = _ := by ring
  rw [lpSize_sq]
  exact power_cancel (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (mul_nonneg (by linarith) (dirichletLpSize_nonneg f a))
      (dirichletLpSize_nonneg h c)) hp0 hBound

theorem dirichlet_angular_lp_logconvex_sup {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f g h : E n → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hh : ContinuousOn h (closedUnitBall n))
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hDf : ∀ x ∈ unitBall n, fderiv ℝ f x (T x) = g x)
    (hDg : ∀ x ∈ unitBall n, fderiv ℝ g x (T x) = h x)
    {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B) (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    dirichletLpSize g p ^ 2 ≤ (p - 1) * B * dirichletLpSize h (p / 2) := by
  let μ := (volume0 n).restrict (unitBall n)
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure μ := volume0_restrict_isProbability n
  let I : ℝ := ∫ x, |g x| ^ p ∂μ
  let β : ℝ := p / (p - 2)
  have hp0 : 0 < p := by linarith
  have hβ : 0 < β := div_pos hp0 (by linarith)
  have hConj : β.HolderConjugate (p / 2) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · dsimp [β]
      rw [lt_div_iff₀ (show 0 < p - 2 by linarith)]
      linarith
    · dsimp [β]
      rw [inv_div, inv_div]
      field_simp [hp0.ne'] <;> ring
  have hgP : ContinuousOn (fun x => |g x| ^ (p - 2)) (closedUnitBall n) :=
    ((hg.continuousOn.mono hSub).abs).rpow_const (fun _ _ => Or.inr (by linarith))
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hConj
    (f := fun x => |g x| ^ (p - 2)) (g := fun x => |h x|)
    (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (Eventually.of_forall fun _ => abs_nonneg _)
    (dirichlet_memLp_of_continuousOn hn hgP _) (dirichlet_memLp_of_continuousOn hn hh.abs _)
  have hPow : (fun x => (|g x| ^ (p - 2)) ^ β) = fun x => |g x| ^ p := by
    funext x
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    dsimp [β]
    field_simp [(sub_pos.mpr hp).ne']
  have hInv : 1 / β = (p - 2) / p := by dsimp [β]; rw [one_div_div]
  rw [hPow, hInv] at hHolder
  have hInt {v : E n → ℝ} (hv : ContinuousOn v (closedUnitBall n)) : Integrable v μ :=
    (dirichlet_memLp_of_continuousOn hn hv 1).integrable le_rfl
  have hBoundF : (∫ x, |f x| * |g x| ^ (p - 2) * |h x| ∂μ) ≤
      B * ∫ x, |g x| ^ (p - 2) * |h x| ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      (hInt (((hf.continuousOn.mono hSub).abs.mul hgP).mul hh.abs))
      (hInt ((hgP.mul hh.abs).const_mul B))
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    change |f x| * |g x| ^ (p - 2) * |h x| ≤ B * (|g x| ^ (p - 2) * |h x|)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hF x hx)
      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _))
  have hIBP := integral_dirichlet_angular_power_le_abs hn hU hSub hf hg hh T hT hDf hDg hp.le
  have hBound : I ≤ ((p - 1) * B * dirichletLpSize h (p / 2)) * I ^ ((p - 2) / p) := by
    calc
      I ≤ (p - 1) * ∫ x, |f x| * |g x| ^ (p - 2) * |h x| ∂μ := hIBP
      _ ≤ (p - 1) * (B * ∫ x, |g x| ^ (p - 2) * |h x| ∂μ) :=
        mul_le_mul_of_nonneg_left hBoundF (by linarith)
      _ ≤ (p - 1) * (B * (I ^ ((p - 2) / p) * dirichletLpSize h (p / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHolder hB) (by linarith)
      _ = _ := by ring
  rw [lpSize_sq]
  exact power_cancel (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (mul_nonneg (by linarith) hB) (dirichletLpSize_nonneg h (p / 2))) hp0 hBound

end KEBall
