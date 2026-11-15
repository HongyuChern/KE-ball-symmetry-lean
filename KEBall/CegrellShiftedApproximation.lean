import KEBall.CegrellOrder

/-!
# Global energy convergence under a common boundary barrier
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {b u v : ComplexModel n → ℝ}

private theorem dist_integral_cutoff_le (hn : 0 < n) (hu : IsE0 (complexUnitBall n) u)
    {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(complexUnitBall n, ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hsmall : ∀ x ∈ complexUnitBall n, χ x ≠ 1 → -u x ≤ ε) :
    dist (∫ x, u x ∂topMeasure hu.locallyBoundedPsh)
      (∫ x, χ x * u x ∂topMeasure hu.locallyBoundedPsh) ≤
      ε * (topMeasure hu.locallyBoundedPsh univ).toReal := by
  let μ := topMeasure hu.locallyBoundedPsh
  let : IsFiniteMeasure μ := ⟨hu.finiteMass⟩
  have hdom : ∀ᵐ x ∂μ, x ∈ complexUnitBall n := by
    rw [ae_iff]
    exact topMeasure_compl hu.locallyBoundedPsh
  rw [Real.dist_eq, ← integral_sub (hu.integrable_against_topMeasure hu)
    (integrable_test_mul_topMeasure hu.locallyBoundedPsh hu.locallyBoundedPsh χ), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_const ε) ?_).trans_eq ?_
  · filter_upwards [hdom] with x hx
    change ‖u x - χ x * u x‖ ≤ ε
    by_cases h : χ x = 1
    · rw [h, one_mul, sub_self, norm_zero]
      exact hε.le
    · rw [← one_sub_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr (hχ x).2), abs_of_nonpos (hu.nonpositive_unitBall hn x hx)]
      exact (mul_le_of_le_one_left (neg_nonneg.mpr (hu.nonpositive_unitBall hn x hx))
        (sub_le_self _ (hχ x).1)).trans (hsmall x hx h)
  · rw [integral_const, smul_eq_mul, measureReal_def, mul_comm]

/-- On the ball, compactly supported weighted convergence extends to
global energy convergence for zero-boundary potentials with a common
lower barrier and uniformly bounded total mass. Additive corrections
tending to zero are allowed in the decreasing approximants. -/
theorem tendsto_boundedEnergy_of_shifted_decreasing (hn : 0 < n)
    (hb : IsE0 (complexUnitBall n) b) (hv : IsE0 (complexUnitBall n) v)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsE0 (complexUnitBall n) (p j))
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hAnti : ∀ x ∈ complexUnitBall n, Antitone (fun j => p j x + c j))
    (hLim : ∀ x ∈ complexUnitBall n, Tendsto (fun j => p j x + c j) atTop (𝓝 (v x)))
    (hbv : ∀ x ∈ complexUnitBall n, b x ≤ v x)
    (hbp : ∀ j x, x ∈ complexUnitBall n → b x ≤ p j x)
    {M : ℝ≥0∞} (hM : M < ⊤)
    (hMlimit : topMeasure hv.locallyBoundedPsh univ ≤ M)
    (hMass : ∀ j, topMeasure (hp j).locallyBoundedPsh univ ≤ M) :
    Tendsto (fun j => boundedEnergy (hp j)) atTop (𝓝 (boundedEnergy hv)) := by
  let B := complexUnitBall n
  let μ (j : ℕ) := topMeasure (hp j).locallyBoundedPsh
  let ν := topMeasure hv.locallyBoundedPsh
  let P (j : ℕ) := locallyBoundedPsh_add_const (hp j).locallyBoundedPsh (c j)
  have hEq (j : ℕ) : topMeasure (P j) = μ j := topMeasure_add_const (hp j).locallyBoundedPsh (c j)
  have hTest (χ : 𝓓(B, ℝ)) : Tendsto (fun j => ∫ x, χ x * p j x ∂μ j) atTop
      (𝓝 (∫ x, χ x * v x ∂ν)) := by
    have hW := tendsto_weightedTopMeasure_of_decreasing hv.locallyBoundedPsh hv.locallyBoundedPsh
      P P hAnti hAnti hLim hLim χ
    have hU := tendsto_topMeasure_of_decreasing hv.locallyBoundedPsh P hAnti hLim
      χ χ.continuous χ.hasCompactSupport χ.tsupport_subset
    simp_rw [hEq] at hW hU
    have hProd := hc.mul hU
    rw [zero_mul] at hProd
    have h := hW.sub hProd
    rw [sub_zero] at h
    apply h.congr
    intro j
    have hi : Integrable (fun x => χ x) (μ j) := by
      simpa only [mul_one] using integrable_test_mul_topMeasure
        (locallyBoundedPsh_const 1) (hp j).locallyBoundedPsh χ
    change (∫ x, χ x * (p j x + c j) ∂μ j) - c j * (∫ x, χ x ∂μ j) = _
    simp_rw [mul_add, mul_comm (χ _) (c j)]
    rw [integral_add (integrable_test_mul_topMeasure (hp j).locallyBoundedPsh (hp j).locallyBoundedPsh χ)
      (hi.const_mul (c j)), integral_const_mul, add_sub_cancel_right]
  have hInt : Tendsto (fun j => ∫ x, p j x ∂μ j) atTop (𝓝 (∫ x, v x ∂ν)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    let ε := δ / (3 * (M.toReal + 1))
    have hε : 0 < ε := div_pos hδ (by positivity)
    have hεM : ε * M.toReal < δ / 3 := by
      have he : ε * (M.toReal + 1) = δ / 3 := by dsimp [ε]; field_simp
      linarith
    let K := closure {x ∈ B | b x ≤ -ε}
    have hKB : K ⊆ B := sublevel_closure_subset hb (neg_lt_zero.mpr hε)
    have hK : IsCompact K := (isCompact_closure_complexUnitBall n).of_isClosed_subset
      isClosed_closure (closure_mono fun _ hx => hx.1)
    obtain ⟨χ, hχ, hχK⟩ := exists_testFunction_one_on hK hKB
    have hSmall (x : ComplexModel n) (hx : x ∈ B) (hc : χ x ≠ 1) : -b x ≤ ε := by
      have hb : -ε < b x := lt_of_not_ge fun h => hc (hχK (subset_closure ⟨hx, h⟩))
      linarith
    have hTailP (j : ℕ) : dist (∫ x, p j x ∂μ j) (∫ x, χ x * p j x ∂μ j) < δ / 3 :=
      (dist_integral_cutoff_le hn (hp j) hε χ hχ (fun x hx hc =>
        (neg_le_neg (hbp j x hx)).trans (hSmall x hx hc))).trans_lt
        ((mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hM.ne (hMass j)) hε.le).trans_lt hεM)
    have hTailV : dist (∫ x, v x ∂ν) (∫ x, χ x * v x ∂ν) < δ / 3 :=
      (dist_integral_cutoff_le hn hv hε χ hχ (fun x hx hc =>
        (neg_le_neg (hbv x hx)).trans (hSmall x hx hc))).trans_lt
        ((mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hM.ne hMlimit) hε.le).trans_lt hεM)
    filter_upwards [Metric.tendsto_nhds.mp (hTest χ) (δ / 3) (by positivity)] with j hj
    exact (dist_triangle4 (∫ x, p j x ∂μ j) (∫ x, χ x * p j x ∂μ j)
      (∫ x, χ x * v x ∂ν) (∫ x, v x ∂ν)).trans_lt (by
        rw [dist_comm (∫ x, χ x * v x ∂ν)]
        linarith [hTailP j, hTailV])
  have hE (j : ℕ) : boundedEnergy (hp j) = ENNReal.ofReal (-(∫ x, p j x ∂μ j)) :=
    crossEnergy_eq_ofReal (hp j) (hp j) ((hp j).nonpositive_unitBall hn)
  have hvE : boundedEnergy hv = ENNReal.ofReal (-(∫ x, v x ∂ν)) :=
    crossEnergy_eq_ofReal hv hv (hv.nonpositive_unitBall hn)
  simp_rw [hE, hvE]
  exact ENNReal.tendsto_ofReal hInt.neg

/-- Replacing an upper potential by a small negative shift makes its
maximum with a fixed lower barrier agree with the barrier in a collar. -/
theorem tendsto_energy_max_sub_const (hn : 0 < n)
    (hb : IsE0 (complexUnitBall n) b) (hu : IsE0 (complexUnitBall n) u)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) (hc₀ : ∀ j, 0 < c j) (hcAnti : Antitone c)
    (hv : IsE0 (complexUnitBall n) (fun x => max (b x) (u x)))
    (hp : ∀ j, IsE0 (complexUnitBall n) (fun x => max (b x) (u x + -c j))) :
    Tendsto (fun j => boundedEnergy (hp j)) atTop (𝓝 (boundedEnergy hv)) := by
  let B := complexUnitBall n
  let p (j : ℕ) (x : ComplexModel n) := max (b x) (u x + -c j)
  have he (j : ℕ) (x : ComplexModel n) : p j x + c j = max (b x + c j) (u x) := by
    dsimp [p]
    rw [← max_add_add_right, neg_add_cancel_right]
  have hAnti (x : ComplexModel n) (_ : x ∈ B) : Antitone (fun j => p j x + c j) := by
    intro i j hij
    change p j x + c j ≤ p i x + c i
    rw [he, he]
    exact max_le_max_right _ (add_le_add le_rfl (hcAnti hij))
  have hLim (x : ComplexModel n) (_ : x ∈ B) :
      Tendsto (fun j => p j x + c j) atTop (𝓝 (max (b x) (u x))) := by
    simp_rw [he]
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := b x)).add hc).max (tendsto_const_nhds (x := u x))
  have hMass (j : ℕ) : topMeasure (hp j).locallyBoundedPsh univ =
      topMeasure hb.locallyBoundedPsh univ := by
    obtain ⟨_, K, hK, hKB, hKp⟩ := hb.max_shift (isCompact_closure_complexUnitBall n)
      hu.locallyBoundedPsh (hb.nonpositive_unitBall hn) (hu.nonpositive_unitBall hn) (hc₀ j)
    exact (topMeasure_total_eq_of_eq_off_compact hb.locallyBoundedPsh (hp j).locallyBoundedPsh
      hK hKB hKp).symm
  exact tendsto_boundedEnergy_of_shifted_decreasing hn hb hv hp hc hAnti hLim
    (fun _ _ => le_max_left _ _) (fun _ _ _ => le_max_left _ _)
    (ENNReal.add_lt_top.mpr ⟨hv.finiteMass, hb.finiteMass⟩)
    (le_self_add) (fun j => (hMass j).le.trans le_add_self)

end KEBall.Cegrell
