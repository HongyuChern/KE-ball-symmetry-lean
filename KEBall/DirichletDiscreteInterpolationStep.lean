import KEBall.DirichletDiscretePowerIdentity
import KEBall.DirichletAngularInterpolationStep

/-!
# Discrete Lp interpolation on the actual closed ball

The hypotheses are continuity on the closed ball and two genuine orthogonal
difference identities. In particular, no angular derivatives or smooth
extension of the fields are assumed. Both shifted terms in discrete
integration by parts are estimated with the same normalized ball measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace KEBall

theorem dirichletLpSize_orthogonal_comp {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (f : E n → ℝ) (p : ℝ) :
    dirichletLpSize (fun x => f (R x)) p = dirichletLpSize f p := by
  unfold dirichletLpSize
  rw [integral_dirichlet_orthogonal_comp R (fun x => |f x| ^ p)]

theorem dirichletLpSize_const_mul {n : ℕ} (s : ℝ) (f : E n → ℝ)
    {p : ℝ} (hp : 0 < p) :
    dirichletLpSize (fun x => s * f x) p = |s| * dirichletLpSize f p := by
  unfold dirichletLpSize
  simp_rw [abs_mul, Real.mul_rpow (abs_nonneg s) (abs_nonneg (f _))]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg s) _)
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg s), mul_one_div_cancel hp.ne', Real.rpow_one]

private theorem discrete_power_cancel {I K p : ℝ} (hI : 0 ≤ I) (hK : 0 ≤ K)
    (hp : 0 < p) (h : I ≤ K * I ^ ((p - 2) / p)) : I ^ (2 / p) ≤ K := by
  rcases eq_or_lt_of_le hI with hZero | hPos
  · rw [← hZero, Real.zero_rpow (ne_of_gt (div_pos (by norm_num) hp))]
    exact hK
  · have he : (2 / p : ℝ) + (p - 2) / p = 1 := by
      field_simp [hp.ne'] <;> ring
    have hSplit : I = I ^ (2 / p) * I ^ ((p - 2) / p) := by
      rw [← Real.rpow_add hPos, he, Real.rpow_one]
    exact le_of_mul_le_mul_right (hSplit.symm.trans_le h)
      (Real.rpow_pos_of_pos hPos _)

private theorem discrete_lpSize_sq {n : ℕ} (g : E n → ℝ) (p : ℝ) :
    dirichletLpSize g p ^ 2 =
      (∫ x in unitBall n, |g x| ^ p ∂volume0 n) ^ (2 / p) := by
  unfold dirichletLpSize
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)]
  congr 1
  ring

private theorem discrete_three_holder {n : ℕ} (hn : 0 < n)
    {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    {p a c : ℝ} (hp : 2 < p) (ha : 0 < a) (hc : 0 < c)
    (hBalance : a⁻¹ + c⁻¹ = 2 / p) :
    (∫ x in unitBall n, |f x| * |g x| ^ (p - 2) * |h x| ∂volume0 n) ≤
      dirichletLpSize f a *
        ((∫ x in unitBall n, |g x| ^ p ∂volume0 n) ^ ((p - 2) / p) *
          dirichletLpSize h c) := by
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
    hf.abs (hg.abs.rpow_const (fun _ _ => Or.inr (by linarith))) hh.abs
    (fun _ => abs_nonneg _) (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (fun _ => abs_nonneg _) ha hβ hc hABC
  have hPow : (fun x => (|g x| ^ (p - 2)) ^ β) = fun x => |g x| ^ p := by
    funext x
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    dsimp [β]
    field_simp [(sub_pos.mpr hp).ne']
  have hInv : 1 / β = (p - 2) / p := by dsimp [β]; rw [one_div_div]
  rw [hPow, hInv] at hHolder
  exact hHolder

private theorem discrete_two_holder_sup {n : ℕ} (hn : 0 < n)
    {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    (∫ x in unitBall n, |f x| * |g x| ^ (p - 2) * |h x| ∂volume0 n) ≤
      B * ((∫ x in unitBall n, |g x| ^ p ∂volume0 n) ^ ((p - 2) / p) *
        dirichletLpSize h (p / 2)) := by
  let μ := (volume0 n).restrict (unitBall n)
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure μ := volume0_restrict_isProbability n
  let β : ℝ := p / (p - 2)
  have hp0 : 0 < p := by linarith
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
    hg.abs.rpow_const (fun _ _ => Or.inr (by linarith))
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
    apply integral_mono_ae (hInt ((hf.abs.mul hgP).mul hh.abs))
      (hInt ((hgP.mul hh.abs).const_mul B))
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    change |f x| * |g x| ^ (p - 2) * |h x| ≤ B * (|g x| ^ (p - 2) * |h x|)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hF x hx)
      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _))
  exact hBoundF.trans (mul_le_mul_of_nonneg_left hHolder hB)

theorem dirichlet_discrete_lp_logconvex {n : ℕ} (hn : 0 < n)
    (R : E n ≃ₗᵢ[ℝ] E n) {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = g x)
    (hDg : ∀ x ∈ unitBall n, g (R x) - g x = h x)
    {p a c : ℝ} (hp : 2 < p) (ha : 0 < a) (hc : 0 < c)
    (hBalance : a⁻¹ + c⁻¹ = 2 / p) :
    dirichletLpSize g p ^ 2 ≤ 2 * (p - 1) * dirichletLpSize f a * dirichletLpSize h c := by
  let I : ℝ := ∫ x in unitBall n, |g x| ^ p ∂volume0 n
  have hG := continuousOn_dirichlet_orthogonal_comp hg R.symm
  have hH := continuousOn_dirichlet_orthogonal_comp hh R.symm
  have h₁ := discrete_three_holder hn hf hG hH hp ha hc hBalance
  have h₂ := discrete_three_holder hn hf hg hH hp ha hc hBalance
  rw [integral_dirichlet_orthogonal_comp R.symm (fun x => |g x| ^ p),
    dirichletLpSize_orthogonal_comp] at h₁
  rw [dirichletLpSize_orthogonal_comp] at h₂
  have hIBP := integral_dirichlet_discrete_power_le_abs R hf hg hh hDf hDg hp.le
  have hBound : I ≤
      (2 * (p - 1) * dirichletLpSize f a * dirichletLpSize h c) * I ^ ((p - 2) / p) := by
    calc
      I ≤ _ := hIBP
      _ ≤ (p - 1) * (dirichletLpSize f a * (I ^ ((p - 2) / p) * dirichletLpSize h c) +
          dirichletLpSize f a * (I ^ ((p - 2) / p) * dirichletLpSize h c)) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by linarith)
      _ = _ := by ring
  rw [discrete_lpSize_sq]
  exact discrete_power_cancel (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (dirichletLpSize_nonneg f a)) (dirichletLpSize_nonneg h c)) (by linarith) hBound

theorem dirichlet_discrete_lp_logconvex_sup {n : ℕ} (hn : 0 < n)
    (R : E n ≃ₗᵢ[ℝ] E n) {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = g x)
    (hDg : ∀ x ∈ unitBall n, g (R x) - g x = h x)
    {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    dirichletLpSize g p ^ 2 ≤ 2 * (p - 1) * B * dirichletLpSize h (p / 2) := by
  let I : ℝ := ∫ x in unitBall n, |g x| ^ p ∂volume0 n
  have hG := continuousOn_dirichlet_orthogonal_comp hg R.symm
  have hH := continuousOn_dirichlet_orthogonal_comp hh R.symm
  have h₁ := discrete_two_holder_sup hn hf hG hH hp hB hF
  have h₂ := discrete_two_holder_sup hn hf hg hH hp hB hF
  rw [integral_dirichlet_orthogonal_comp R.symm (fun x => |g x| ^ p),
    dirichletLpSize_orthogonal_comp] at h₁
  rw [dirichletLpSize_orthogonal_comp] at h₂
  have hIBP := integral_dirichlet_discrete_power_le_abs R hf hg hh hDf hDg hp.le
  have hBound : I ≤
      (2 * (p - 1) * B * dirichletLpSize h (p / 2)) * I ^ ((p - 2) / p) := by
    calc
      I ≤ _ := hIBP
      _ ≤ (p - 1) * (B * (I ^ ((p - 2) / p) * dirichletLpSize h (p / 2)) +
          B * (I ^ ((p - 2) / p) * dirichletLpSize h (p / 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by linarith)
      _ = _ := by ring
  rw [discrete_lpSize_sq]
  exact discrete_power_cancel (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hB)
      (dirichletLpSize_nonneg h (p / 2))) (by linarith) hBound

end KEBall
