import KEBall.ScalarBranches

/-!
Stage08 SOURCE_DRAFT_UNCOMPILED.
Scalar comparison used after the genuine lower boundary slope theorem.
No global upper bound on the actual slope is assumed.
-/
set_option autoImplicit false
open Set

namespace KEBall

/-- Between the two positive roots the boundary polynomial lies above its
level. This uses the increasing and decreasing pieces separately. -/
theorem boundaryPolynomial_ge_between_roots {n : ℕ} (hn : 1 ≤ n)
    {μ a c s : ℝ} (ha : 0 < a) (han : a < (n : ℝ))
    (hnc : (n : ℝ) < c) (hck : c < (n + 1 : ℝ))
    (hFa : boundaryPolynomial n a = μ) (hFc : boundaryPolynomial n c = μ)
    (has : a ≤ s) (hsc : s ≤ c) : μ ≤ boundaryPolynomial n s := by
  by_cases hsn : s ≤ (n : ℝ)
  · rw [← hFa]
    exact (boundaryPolynomial_strictMonoOn hn).monotoneOn
      ⟨ha.le, han.le⟩ ⟨ha.le.trans has, hsn⟩ has
  · rw [← hFc]
    exact (boundaryPolynomial_strictAntiOn hn).antitoneOn
      ⟨le_of_not_ge hsn, hsc.trans hck.le⟩ ⟨hnc.le, hck.le⟩ hsc

/-- Above the upper root the polynomial is below its level, including
s ≥ n+1, where the polynomial is nonpositive. -/
theorem boundaryPolynomial_le_above_upper_root {n : ℕ} (hn : 1 ≤ n)
    {μ c s : ℝ} (hμ : 0 < μ) (hnc : (n : ℝ) < c)
    (hck : c < (n + 1 : ℝ)) (hFc : boundaryPolynomial n c = μ)
    (hcs : c ≤ s) : boundaryPolynomial n s ≤ μ := by
  by_cases hsk : s ≤ (n + 1 : ℝ)
  · rw [← hFc]
    exact (boundaryPolynomial_strictAntiOn hn).antitoneOn
      ⟨hnc.le, hck.le⟩ ⟨hnc.le.trans hcs, hsk⟩ hcs
  · have hs : 0 ≤ s := le_trans (by positivity : (0 : ℝ) ≤ n) (hnc.le.trans hcs)
    have hk : 0 < (n + 1 : ℝ) := by positivity
    have hfac : 1 - s / (n + 1 : ℝ) ≤ 0 := by
      have hd := (one_le_div hk).mpr (le_of_not_ge hsk)
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs n) hfac).trans hμ.le

/-- The reciprocal sign change matches the upper root sign change. -/
theorem boundary_weighted_defect_nonneg {n : ℕ} (hn : 1 ≤ n)
    {μ a c s : ℝ} (hμ : 0 < μ) (ha : 0 < a) (han : a < (n : ℝ))
    (hnc : (n : ℝ) < c) (hck : c < (n + 1 : ℝ))
    (hFa : boundaryPolynomial n a = μ) (hFc : boundaryPolynomial n c = μ)
    (has : a ≤ s) :
    0 ≤ (boundaryPolynomial n s - μ) * (1 / s - 1 / c) := by
  have hs : 0 < s := ha.trans_le has
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := hnR.trans hnc
  have hd : 1 / s - 1 / c = (c - s) / (s * c) := by
    field_simp [ne_of_gt hs, ne_of_gt hc]
    <;> ring
  rw [hd]
  by_cases hsc : s ≤ c
  · exact mul_nonneg
      (sub_nonneg.mpr (boundaryPolynomial_ge_between_roots hn ha han hnc hck hFa hFc has hsc))
      (div_nonneg (sub_nonneg.mpr hsc) (mul_pos hs hc).le)
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (boundaryPolynomial_le_above_upper_root hn hμ hnc hck hFc
        (le_of_not_ge hsc)))
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hsc))
        (mul_pos hs hc).le)

/-- Vanishing of the reciprocal defect forces the polynomial to have its
root value; the reciprocal factor cannot introduce an unrelated zero. -/
theorem boundaryPolynomial_eq_of_weighted_defect_zero {n : ℕ}
    {μ c s : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hFc : boundaryPolynomial n c = μ)
    (hz : (boundaryPolynomial n s - μ) * (1 / s - 1 / c) = 0) :
    boundaryPolynomial n s = μ := by
  rcases mul_eq_zero.mp hz with hF | hrec
  · exact sub_eq_zero.mp hF
  · have hsc : s = c := by
      field_simp [ne_of_gt hs, ne_of_gt hc] at hrec
      linarith
    simpa only [hsc] using hFc

end KEBall
