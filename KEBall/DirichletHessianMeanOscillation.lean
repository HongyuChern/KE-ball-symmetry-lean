import KEBall.DirichletHessianBallBounds
import Mathlib.MeasureTheory.Integral.Average

/-! Mean oscillation is bounded by essential oscillation, with exact ball averaging. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped NNReal

noncomputable section

namespace KEBall

theorem integral_abs_sub_mean_le_essential_oscillation
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (q : X → ℝ) (hq : Integrable q μ)
    (hLo : IsBoundedUnder (· ≥ ·) (ae μ) q)
    (hHi : IsBoundedUnder (· ≤ ·) (ae μ) q) :
    (∫ x, |q x - ∫ y, q y ∂μ| ∂μ) ≤ essSup q μ - essInf q μ := by
  let a := essInf q μ
  let b := essSup q μ
  let m := ∫ y, q y ∂μ
  have hLow : a ≤ m := by
    simpa only [integral_const, probReal_univ, one_smul] using
      (integral_mono_ae (integrable_const a) hq (ae_essInf_le hLo))
  have hHigh : m ≤ b := by
    simpa only [integral_const, probReal_univ, one_smul] using
      (integral_mono_ae hq (integrable_const b) (ae_le_essSup hHi))
  have hAbs : ∀ᵐ x ∂μ, |q x - m| ≤ b - a := by
    filter_upwards [ae_essInf_le hLo, ae_le_essSup hHi] with x hxLo hxHi
    apply abs_le.mpr
    change a ≤ q x at hxLo
    change q x ≤ b at hxHi
    constructor <;> linarith
  have h := integral_mono_ae ((hq.sub (integrable_const m)).abs) (integrable_const (b - a)) hAbs
  simpa only [Pi.sub_apply, m, a, b, integral_const, probReal_univ, one_smul] using h

theorem dirichlet_hessian_mean_oscillation_le {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : E n)
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n) :
    (⨍ x in ball x₀ r,
      |fderiv ℝ G x v v - ⨍ y in ball x₀ r, fderiv ℝ G y v v|) ≤
      essSup (fun x => fderiv ℝ G x v v) (volume.restrict (ball x₀ r)) -
        essInf (fun x => fderiv ℝ G x v v) (volume.restrict (ball x₀ r)) := by
  let μ := dirichletBallProbability x₀ r
  let q : E n → ℝ := fun x => fderiv ℝ G x v v
  let K : ℝ := (L : ℝ) * ‖v‖ * ‖v‖
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_dirichletBallProbability x₀ hr
  have hBounds : ∀ᵐ x ∂μ, -K ≤ q x ∧ q x ≤ K := by
    apply ae_dirichletBallProbability_iff.mpr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
    exact abs_le.mp (norm_dirichlet_hessianEntry_le hG (hBall hx) v v)
  have hLo : IsBoundedUnder (· ≥ ·) (ae μ) q := ⟨-K, hBounds.mono fun _ h => h.1⟩
  have hHi : IsBoundedUnder (· ≤ ·) (ae μ) q := ⟨K, hBounds.mono fun _ h => h.2⟩
  have hInt : Integrable q μ := (integrable_dirichletBallProbability_iff hr).mpr
    (integrableOn_dirichlet_hessianEntry_ball hG v hBall)
  have h := integral_abs_sub_mean_le_essential_oscillation q hInt hLo hHi
  simp only [μ, essSup_dirichletBallProbability, essInf_dirichletBallProbability] at h
  simpa only [q, setAverage_eq', dirichletBallProbability] using h

end KEBall
