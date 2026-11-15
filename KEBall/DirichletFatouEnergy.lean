import KEBall.DirichletTensorQuartic

/-! A nonnegative energy limit is integrable, not merely assigned a Bochner integral. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory
open scoped Topology ENNReal

namespace KEBall

theorem dirichlet_integrable_and_integral_le_of_ae_tendsto_nonneg
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {G : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ k, Integrable (F k) μ) (hG : AEStronglyMeasurable G μ)
    (hF₀ : ∀ k, 0 ≤ᵐ[μ] F k) (hG₀ : 0 ≤ᵐ[μ] G)
    (hLim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (G x)))
    (hBound : ∀ᶠ k in atTop, (∫ x, F k x ∂μ) ≤ C) :
    Integrable G μ ∧ (∫ x, G x ∂μ) ≤ C := by
  have h := lintegral_liminf_le' (u := atTop) (fun k => (hF k).aemeasurable.ennreal_ofReal)
  have he : (∫⁻ x, liminf (fun k => ENNReal.ofReal (F k x)) atTop ∂μ) =
      ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hLim] with x hx
    exact ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx) :
      Tendsto (fun k => ENNReal.ofReal (F k x)) atTop (𝓝 (ENNReal.ofReal (G x)))).liminf_eq
  have hL : ∀ᶠ k in atTop, (∫⁻ x, ENNReal.ofReal (F k x) ∂μ) ≤ ENNReal.ofReal C := by
    filter_upwards [hBound] with k hk
    rw [← ofReal_integral_eq_lintegral_ofReal (hF k) (hF₀ k)]
    exact ENNReal.ofReal_le_ofReal hk
  have hL' : liminf (fun k => ∫⁻ x, ENNReal.ofReal (F k x) ∂μ) atTop ≤ ENNReal.ofReal C := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hL
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    exact iSup_le fun k => iInf_le_of_le (max k N)
      (iInf_le_of_le (le_max_left _ _) (hN _ (le_max_right _ _)))
  rw [he] at h
  have hBoundG := h.trans hL'
  have hIntegrable : Integrable G μ :=
    (lintegral_ofReal_ne_top_iff_integrable hG hG₀).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBoundG)
  refine ⟨hIntegrable, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hG₀] at hBoundG
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hBoundG

end KEBall
