import KEBall.DirichletWeakHarnack

/-! Essential-extremum and source-correction steps for Hessian defects. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set

noncomputable section

namespace KEBall

/-- A bounded nonnegative correction costs only its uniform upper bound
when the essential infimum of an upper defect is estimated. -/
theorem dirichlet_essInf_corrected_defect_le {n : ℕ} {μ : Measure (E n)}
    (hμ : μ ≠ 0) {q s : E n → ℝ} {l u M ε K : ℝ}
    (hq : ∀ᵐ x ∂μ, l ≤ q x ∧ q x ≤ u)
    (hs : ∀ᵐ x ∂μ, 0 ≤ s x ∧ s x ≤ K) :
    essInf (fun x => M + ε - q x + s x) μ ≤ M + ε - essSup q μ + K := by
  letI : NeZero μ := ⟨hμ⟩
  have hLo : IsBoundedUnder (· ≥ ·) (ae μ) q := ⟨l, hq.mono fun _ h => h.1⟩
  have hHi : IsBoundedUnder (· ≤ ·) (ae μ) q := ⟨u, hq.mono fun _ h => h.2⟩
  have hnLo : IsBoundedUnder (· ≥ ·) (ae μ) (fun x => -q x) :=
    ⟨-u, hq.mono fun _ h => neg_le_neg h.2⟩
  have hnHi : IsBoundedUnder (· ≤ ·) (ae μ) (fun x => -q x) :=
    ⟨-l, hq.mono fun _ h => neg_le_neg h.1⟩
  have hfLo : IsBoundedUnder (· ≥ ·) (ae μ) (fun x => M + ε - q x + s x) := by
    refine ⟨M + ε - u, ?_⟩
    change ∀ᵐ x ∂μ, M + ε - u ≤ M + ε - q x + s x
    filter_upwards [hq, hs] with x hx hxs
    linarith [hx.2, hxs.1]
  have hgHi : IsBoundedUnder (· ≤ ·) (ae μ) (fun x => -q x + (M + ε + K)) := by
    refine ⟨-l + (M + ε + K), ?_⟩
    change ∀ᵐ x ∂μ, -q x + (M + ε + K) ≤ -l + (M + ε + K)
    filter_upwards [hq] with x hx
    linarith [hx.1]
  have hle : (fun x => M + ε - q x + s x) ≤ᵐ[μ]
      (fun x => -q x + (M + ε + K)) := by
    filter_upwards [hs] with x hx
    linarith [hx.2]
  calc
    _ ≤ essInf (fun x => -q x + (M + ε + K)) μ :=
      essInf_mono_ae hle hfLo hgHi.isCoboundedUnder_ge
    _ = -essSup q μ + (M + ε + K) := by
      rw [DeGiorgi.essInf_add_const_of_bdd hμ _ hnLo hnHi,
        DeGiorgi.essInf_neg_of_bdd hμ hLo hHi hnLo hnHi]
    _ = _ := by ring

/-- The strict positivity parameter can be removed after Harnack has been
applied; no positive pointwise representative of the original defect is
assumed. -/
theorem dirichlet_defect_bound_of_corrected_harnack {n : ℕ} {μ : Measure (E n)}
    (hμ : μ ≠ 0) {q s : E n → ℝ} {l u M K C J : ℝ}
    (hC : 0 ≤ C)
    (hq : ∀ᵐ x ∂μ, l ≤ q x ∧ q x ≤ u)
    (hs : ∀ᵐ x ∂μ, 0 ≤ s x ∧ s x ≤ K)
    (hH : ∀ ε : ℝ, 0 < ε → J ≤ C * essInf (fun x => M + ε - q x + s x) μ) :
    J ≤ C * (M - essSup q μ + K) := by
  by_cases hC0 : C = 0
  · simpa only [hC0, zero_mul] using hH 1 zero_lt_one
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  by_contra h
  have hgap : 0 < J - C * (M - essSup q μ + K) := sub_pos.mpr (lt_of_not_ge h)
  let ε := (J - C * (M - essSup q μ + K)) / (2 * C)
  have hε : 0 < ε := div_pos hgap (mul_pos (by norm_num) hCp)
  have h₁ := hH ε hε
  have h₂ := mul_le_mul_of_nonneg_left
    (dirichlet_essInf_corrected_defect_le hμ (M := M) (ε := ε) hq hs) hC
  have hεeq : ε * (2 * C) = J - C * (M - essSup q μ + K) :=
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hC0)
  nlinarith only [h₁, h₂, hεeq, hgap]

end KEBall
