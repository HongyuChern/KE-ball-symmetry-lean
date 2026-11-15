import KEBall.DirichletOscillationIntegral

/-!
# Essential-oscillation contraction from Harnack and two-point comparison

The assumptions are estimates on the same integrable directional family
and the same inner probability measure.  This is the averaging step of the
Evans--Krylov argument; an application must still supply these estimates
for its actual Hessian.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace KEBall

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
variable {μ : Measure X} [IsProbabilityMeasure μ]

theorem dirichlet_total_oscillation_le_defect_mean
    (q : ι → X → ℝ) (m M : ι → ℝ) (hInt : ∀ i, Integrable (q i) μ)
    (hBounds : ∀ i, ∀ᵐ x ∂μ, m i ≤ q i x ∧ q i x ≤ M i)
    {l U E : ℝ} (hl : 0 < l)
    (hCompare : ∀ j, ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
      l * (q j x - q j y) ≤ U * (∑ i : ι, (M i - q i x)) + E) :
    l * (∑ i : ι, (essSup (q i) μ - essInf (q i) μ)) ≤
      (l + (Fintype.card ι : ℝ) * U) * (∑ i : ι, ∫ x, M i - q i x ∂μ) +
        (Fintype.card ι : ℝ) * E := by
  have hUpper (i : ι) : ∀ᵐ x ∂μ, q i x ≤ M i := (hBounds i).mono fun _ h => h.2
  have hSup (i : ι) : essSup (q i) μ ≤ M i := by
    have hLo : IsBoundedUnder (· ≥ ·) (ae μ) (q i) :=
      ⟨m i, (hBounds i).mono fun _ h => h.1⟩
    exact essSup_le_of_ae_le _ (hUpper i) hLo.isCoboundedUnder_le
  have hEach (j : ι) : l * (essSup (q j) μ - essInf (q j) μ) ≤
      l * (∫ x, M j - q j x ∂μ) +
        U * (∑ i : ι, ∫ x, M i - q i x ∂μ) + E :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right (hSup j) _) hl.le).trans
      (dirichlet_mean_defect_lower_control q M hInt hUpper hl hCompare j)
  calc
    _ = ∑ j : ι, l * (essSup (q j) μ - essInf (q j) μ) := Finset.mul_sum _ _ _
    _ ≤ ∑ j : ι, (l * (∫ x, M j - q j x ∂μ) +
        U * (∑ i : ι, ∫ x, M i - q i x ∂μ) + E) :=
      Finset.sum_le_sum fun j _ => hEach j
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

/-- Quantitative contraction of the sum of essential directional
oscillations.  `H` is the Harnack constant, `F` its additive error, and `E`
the error in the two-point comparison. -/
theorem dirichlet_essential_oscillation_contraction
    (q : ι → X → ℝ) (m M : ι → ℝ) (hInt : ∀ i, Integrable (q i) μ)
    (hBounds : ∀ i, ∀ᵐ x ∂μ, m i ≤ q i x ∧ q i x ≤ M i)
    {l U E H F : ℝ} (hl : 0 < l) (hU : 0 ≤ U) (hH : 0 ≤ H)
    (hCompare : ∀ j, ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
      l * (q j x - q j y) ≤ U * (∑ i : ι, (M i - q i x)) + E)
    (hHarnack : ∀ i, (∫ x, M i - q i x ∂μ) ≤ H * (M i - essSup (q i) μ) + F) :
    let N : ℝ := Fintype.card ι
    let a : ℝ := (l + N * U) / l
    let K : ℝ := a * H
    let err : ℝ := a * (N * F) + (N / l) * E
    (∑ i : ι, (essSup (q i) μ - essInf (q i) μ)) ≤
      K / (1 + K) * (∑ i : ι, (M i - m i)) + err / (1 + K) := by
  let N : ℝ := Fintype.card ι
  let a : ℝ := (l + N * U) / l
  let K : ℝ := a * H
  let err : ℝ := a * (N * F) + (N / l) * E
  let O : ℝ := ∑ i : ι, (M i - m i)
  let o : ℝ := ∑ i : ι, (essSup (q i) μ - essInf (q i) μ)
  let drop : ℝ := ∑ i : ι, (M i - essSup (q i) μ)
  let J : ℝ := ∑ i : ι, ∫ x, M i - q i x ∂μ
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have ha : 0 ≤ a := div_nonneg (add_nonneg hl.le (mul_nonneg hN hU)) hl.le
  have hK : 0 ≤ K := mul_nonneg ha hH
  have hMean : J ≤ H * drop + N * F := by
    calc
      _ ≤ ∑ i : ι, (H * (M i - essSup (q i) μ) + F) :=
        Finset.sum_le_sum fun i _ => hHarnack i
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, drop, N]
  have hTotal : l * o ≤ (l + N * U) * J + N * E :=
    dirichlet_total_oscillation_le_defect_mean q m M hInt hBounds hl hCompare
  have hSmall : o ≤ a * J + (N / l) * E := by
    have h : o ≤ ((l + N * U) * J + N * E) / l :=
      (le_div_iff₀ hl).mpr (by simpa only [mul_comm o l] using hTotal)
    calc
      o ≤ ((l + N * U) * J + N * E) / l := h
      _ = _ := by dsimp only [a]; ring
  have hEstimate : o ≤ K * drop + err := by
    calc
      o ≤ a * J + (N / l) * E := hSmall
      _ ≤ a * (H * drop + N * F) + (N / l) * E :=
        add_le_add (mul_le_mul_of_nonneg_left hMean ha) le_rfl
      _ = _ := by dsimp only [K, err]; ring
  have hInf (i : ι) : m i ≤ essInf (q i) μ := by
    have hHi : IsBoundedUnder (· ≤ ·) (ae μ) (q i) :=
      ⟨M i, (hBounds i).mono fun _ h => h.2⟩
    exact le_essInf_of_ae_le _ ((hBounds i).mono fun _ h => h.1) hHi.isCoboundedUnder_ge
  have hDrop : drop ≤ O - o := by
    calc
      drop ≤ ∑ i : ι, ((M i - m i) - (essSup (q i) μ - essInf (q i) μ)) := by
        apply Finset.sum_le_sum
        intro i _
        linarith only [hInf i]
      _ = O - o := by rw [Finset.sum_sub_distrib]
  exact dirichlet_oscillation_absorb hK hDrop hEstimate

end KEBall
