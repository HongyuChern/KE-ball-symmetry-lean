import KEBall.MoserTrudingerGibbsDensityLimit

/-!
# Equality of Gibbs densities at vanishing entropy gap
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped Topology ContDiff ComplexOrder

namespace KEBall.MoserTrudinger

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

/-- The Jensen defect between two Gibbs weights. -/
noncomputable def gibbsEntropyGap (γ : ℝ) (u v : E n → ℝ) : ℝ :=
  Real.log (normalizingIntegral γ v) - Real.log (normalizingIntegral γ u) -
    ∫ x, gibbsDensity γ u x * (-γ * v x + γ * u x) ∂ν[n]

/-- The defect is bounded by the increase in the smooth functional. -/
theorem gibbsEntropyGap_le_functional_increase (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    {γ : ℝ} (hγ : 0 < γ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x) :
    0 ≤ gibbsEntropyGap γ u v ∧
      gibbsEntropyGap γ u v ≤ γ * (smoothFunctional γ v - smoothFunctional γ u) := by
  have hJ := integral_gibbs_log_ratio_le hn (hu.continuousOn.mono hsub)
    (hv.continuousOn.mono hsub) γ γ
  refine ⟨sub_nonneg.mpr hJ, ?_⟩
  have hT := signedSmoothEnergy_tangent_upper hn hU hsub hv hu hv0 hu0 hvP huP
  have hE : (∫ x, gibbsDensity γ u x * (-γ * v x + γ * u x) ∂ν[n]) =
      γ * ∫ x in unitBall n, (u x - v x) * (complexHessian v x).det.re ∂volume0 n := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
    intro x hx
    dsimp only
    rw [hEq x hx]
    ring
  have h := mul_le_mul_of_nonneg_left hT hγ.le
  unfold gibbsEntropyGap smoothFunctional
  rw [hE, mul_sub, mul_add, mul_add,
    show γ * (Real.log (normalizingIntegral γ v) / γ) = Real.log (normalizingIntegral γ v) from
      mul_div_cancel₀ _ hγ.ne',
    show γ * (Real.log (normalizingIntegral γ u) / γ) = Real.log (normalizingIntegral γ u) from
      mul_div_cancel₀ _ hγ.ne']
  linarith only [h, mul_sub γ (signedSmoothEnergy u) (signedSmoothEnergy v)]

/-- The defect is continuous along bounded, almost-everywhere convergent
sequences of both potentials. -/
theorem tendsto_gibbsEntropyGap_of_ae_of_bounded (hn : 0 < n) {γ B : ℝ} (hγ : 0 ≤ γ)
    {u v : ℕ → E n → ℝ} {w r : E n → ℝ}
    (hu : ∀ j, AEMeasurable (u j) ν[n]) (hv : ∀ j, AEMeasurable (v j) ν[n])
    (hw : AEMeasurable w ν[n]) (hr : AEMeasurable r ν[n])
    (huB : ∀ j, ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0)
    (hvB : ∀ j, ∀ᵐ x ∂ν[n], v j x ∈ Icc (-B) 0)
    (huL : ∀ᵐ x ∂ν[n], Tendsto (fun j => u j x) atTop (𝓝 (w x)))
    (hvL : ∀ᵐ x ∂ν[n], Tendsto (fun j => v j x) atTop (𝓝 (r x))) :
    Tendsto (fun j => gibbsEntropyGap γ (u j) (v j)) atTop (𝓝 (gibbsEntropyGap γ w r)) := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨hzU, hZU, hDB, hDL⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hγ hu hw huB huL
  obtain ⟨hzV, hZV, _, _⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hγ hv hr hvB hvL
  have hLogU := (Real.continuousAt_log (zero_lt_one.trans_le hzU).ne').tendsto.comp hZU
  have hLogV := (Real.continuousAt_log (zero_lt_one.trans_le hzV).ne').tendsto.comp hZV
  have hInt : Tendsto (fun j => ∫ x, gibbsDensity γ (u j) x * (-γ * v j x + γ * u j x) ∂ν[n])
      atTop (𝓝 (∫ x, gibbsDensity γ w x * (-γ * r x + γ * w x) ∂ν[n])) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (γ * B) * (γ * B))
    · intro j
      exact ((gibbsDensity_aemeasurable (hu j)).mul
        ((aemeasurable_const.mul (hv j)).add (aemeasurable_const.mul (hu j)))).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      filter_upwards [huB j, hvB j, hDB j] with x hx hy hd
      rw [norm_mul, Real.norm_eq_abs (gibbsDensity γ (u j) x), abs_of_nonneg hd.1, Real.norm_eq_abs]
      apply mul_le_mul hd.2 _ (abs_nonneg _) (Real.exp_pos _).le
      apply abs_le.mpr
      constructor
      · nlinarith only [mul_le_mul_of_nonneg_left hx.1 hγ, mul_nonpos_of_nonneg_of_nonpos hγ hy.2]
      · nlinarith only [mul_le_mul_of_nonneg_left hy.1 hγ, mul_nonpos_of_nonneg_of_nonpos hγ hx.2]
    · filter_upwards [huL, hvL, hDL] with x hx hy hd
      exact hd.mul ((hy.const_mul (-γ)).add (hx.const_mul γ))
  exact (hLogV.sub hLogU).sub hInt

/-- Vanishing defect identifies the Gibbs densities of bounded measurable
potentials almost everywhere. -/
theorem gibbsDensity_ae_eq_of_entropyGap_eq_zero (hn : 0 < n) {γ B : ℝ} (hγ : 0 ≤ γ)
    {u v : E n → ℝ} (hu : AEMeasurable u ν[n]) (hv : AEMeasurable v ν[n])
    (huB : ∀ᵐ x ∂ν[n], u x ∈ Icc (-B) 0) (hvB : ∀ᵐ x ∂ν[n], v x ∈ Icc (-B) 0)
    (hZu : 1 ≤ normalizingIntegral γ u) (hZv : 1 ≤ normalizingIntegral γ v)
    (hGap : gibbsEntropyGap γ u v = 0) :
    gibbsDensity γ u =ᵐ[ν[n]] gibbsDensity γ v := by
  let : NeZero n := ⟨hn.ne'⟩
  let D := Real.exp (γ * B)
  let p := gibbsDensity γ u
  let Zu := normalizingIntegral γ u
  let Zv := normalizingIntegral γ v
  let m := Real.log Zv - Real.log Zu
  let L (x : E n) := -γ * v x + γ * u x
  have hZu₀ : 0 < Zu := zero_lt_one.trans_le hZu
  have hZv₀ : 0 < Zv := zero_lt_one.trans_le hZv
  have hpPos (x : E n) : 0 < p x := div_pos (Real.exp_pos _) hZu₀
  have hpMeas : AEMeasurable p ν[n] := gibbsDensity_aemeasurable hu
  have hLimB : ∀ᵐ x ∂ν[n], ‖p x‖ ≤ D := by
    filter_upwards [huB] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hpPos x).le]
    exact (div_le_self (Real.exp_pos _).le hZu).trans
      (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hx.1 hγ]))
  have hpI : Integrable p ν[n] := (integrable_const D).mono' hpMeas.aestronglyMeasurable hLimB
  have hMass : (∫ x, p x ∂ν[n]) = 1 := by
    change (∫ x, Real.exp (-γ * u x) / Zu ∂ν[n]) = 1
    rw [integral_div, ← normalizingIntegral, div_self hZu₀.ne']
  have hLBound : ∀ᵐ x ∂ν[n], ‖L x‖ ≤ γ * B := by
    filter_upwards [huB, hvB] with x hx hy
    rw [Real.norm_eq_abs, abs_le]
    dsimp [L]
    exact ⟨by nlinarith only [mul_le_mul_of_nonneg_left hx.1 hγ, mul_nonpos_of_nonneg_of_nonpos hγ hy.2],
      by nlinarith only [mul_le_mul_of_nonneg_left hy.1 hγ, mul_nonpos_of_nonneg_of_nonpos hγ hx.2]⟩
  have hLI : Integrable (fun x => p x * L x) ν[n] := by
    apply (integrable_const (D * (γ * B))).mono'
      (hpMeas.mul ((aemeasurable_const.mul hv).add (aemeasurable_const.mul hu))).aestronglyMeasurable
    filter_upwards [hLimB, hLBound] with x hx hy
    change ‖p x * L x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) (Real.exp_pos _).le
  have hExpM : Real.exp m = Zv / Zu := by
    dsimp [m]
    rw [Real.exp_sub, Real.exp_log hZv₀, Real.exp_log hZu₀]
  let A (x : E n) := p x * Real.exp (L x - m)
  have hA (x : E n) : A x = Real.exp (-γ * v x) / Zv := by
    dsimp only [A, p, gibbsDensity, L]
    have h : Real.exp (-γ * u x) * Real.exp (-γ * v x + γ * u x) = Real.exp (-γ * v x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.exp_sub, hExpM]
    change Real.exp (-γ * u x) / Zu * (Real.exp (-γ * v x + γ * u x) / (Zv / Zu)) = _
    calc
      _ = (Real.exp (-γ * u x) * Real.exp (-γ * v x + γ * u x)) / Zv := by
        field_simp [hZu₀.ne', hZv₀.ne']
      _ = _ := by rw [h]
  have hAI : Integrable A ν[n] := by
    rw [show A = _ from funext hA]
    apply Integrable.div_const
    apply (integrable_const D).mono'
      (Real.continuous_exp.measurable.comp_aemeasurable (aemeasurable_const.mul hv)).aestronglyMeasurable
    filter_upwards [hvB] with x hx
    change ‖Real.exp (-γ * v x)‖ ≤ D
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hx.1 hγ])
  have hAOne : (∫ x, A x ∂ν[n]) = 1 := by
    simp_rw [hA]
    rw [integral_div, ← normalizingIntegral, div_self hZv₀.ne']
  let T (x : E n) := p x * (L x - m + 1)
  have hT (x : E n) : T x = p x * L x + (1 - m) * p x := by
    dsimp only [T]
    ring
  have hTI : Integrable T ν[n] := by
    rw [show T = _ from funext hT]
    exact hLI.add (hpI.const_mul _)
  have hMean : (∫ x, p x * L x ∂ν[n]) = m := by
    change m - (∫ x, p x * L x ∂ν[n]) = 0 at hGap
    exact (sub_eq_zero.mp hGap).symm
  have hTOne : (∫ x, T x ∂ν[n]) = 1 := by
    simp_rw [hT]
    rw [integral_add hLI (hpI.const_mul _), integral_const_mul, hMass, hMean]
    ring
  have hZero : (∫ x, A x - T x ∂ν[n]) = 0 := by rw [integral_sub hAI hTI, hAOne, hTOne, sub_self]
  have hNonneg (x : E n) : 0 ≤ A x - T x := by
    apply sub_nonneg.mpr
    exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hpPos x).le
  have hAE := (integral_eq_zero_iff_of_nonneg hNonneg (hAI.sub hTI)).mp hZero
  filter_upwards [hAE] with x hx
  have hm : L x = m := by
    by_contra hne
    have hlt : T x < A x := mul_lt_mul_of_pos_left (Real.add_one_lt_exp (sub_ne_zero.mpr hne)) (hpPos x)
    exact (sub_pos.mpr hlt).ne' hx
  have hExp : Real.exp (-γ * v x) = Real.exp (-γ * u x) * (Zv / Zu) := by
    rw [← hExpM, ← Real.exp_add]
    congr 1
    dsimp [L] at hm
    linarith only [hm]
  change Real.exp (-γ * u x) / Zu = Real.exp (-γ * v x) / Zv
  rw [hExp]
  field_simp [hZu₀.ne', hZv₀.ne']

end KEBall.MoserTrudinger
