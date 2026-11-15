import KEBall.BedfordTaylorCompactDifference
import KEBall.BedfordTaylorNonsmoothWeights
import KEBall.BedfordTaylorScaling
import KEBall.BedfordTaylorTruncationLocality

/-!
# Weighted convergence with an affine collar
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- A common exterior model permits passing from compactly supported weighted
convergence to convergence of the entire Bedford–Taylor energy pairing. -/
theorem tendsto_integral_topMeasure_of_decreasing_of_affine_collar {n : ℕ}
    {Ω : Opens (ComplexModel n)} {u b : ComplexModel n → ℝ} {q : ℕ → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hb : IsLocallyBoundedPshOn Ω b)
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (huEq : EqOn u b ((Ω : Set (ComplexModel n)) \ K))
    {a d : ℕ → ℝ} (ha : ∀ j, 0 < a j) (haLim : Tendsto a atTop (𝓝 1))
    (hdLim : Tendsto d atTop (𝓝 0))
    (hqEq : ∀ j, EqOn (q j) (fun x => a j * b x + d j) ((Ω : Set (ComplexModel n)) \ K))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (hbFinite : IsFiniteMeasure (topMeasure hb))
    (hbInt : Integrable b (topMeasure hb))
    (huInt : Integrable u (topMeasure hu))
    (hqInt : ∀ j, Integrable (q j) (topMeasure (hq j))) :
    Tendsto (fun j => ∫ x, q j x ∂topMeasure (hq j)) atTop
      (𝓝 (∫ x, u x ∂topMeasure hu)) := by
  obtain ⟨χ, hχRange, hχ⟩ := exists_testFunction_one_on hK hKΩ
  let ψ (x : ComplexModel n) := 1 - χ x
  let μ := (topMeasure hb).restrict Kᶜ
  let B := ∫ x, ψ x * b x ∂μ
  let C := ∫ x, ψ x ∂μ
  have hχM (x : ComplexModel n) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hχRange x).1]
    exact (hχRange x).2
  have hψM (x : ComplexModel n) : ‖ψ x‖ ≤ 1 := by
    change ‖1 - χ x‖ ≤ 1
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (hχRange x).2)]
    linarith only [(hχRange x).1]
  have hψCont : Continuous ψ := continuous_const.sub χ.continuous
  have hSplit {f : ComplexModel n → ℝ} {ν : Measure (ComplexModel n)}
      (hf : Integrable f ν) :
      (∫ x, f x ∂ν) = (∫ x, χ x * f x ∂ν) + ∫ x, ψ x * f x ∂ν := by
    rw [← integral_add (hf.bdd_mul χ.continuous.aestronglyMeasurable
      (Eventually.of_forall hχM)) (hf.bdd_mul
        hψCont.aestronglyMeasurable (Eventually.of_forall hψM))]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [ψ]
    ring
  have hRestrict (f : ComplexModel n → ℝ) (ν : Measure (ComplexModel n)) :
      (∫ x, ψ x * f x ∂ν) = ∫ x, ψ x * f x ∂ν.restrict Kᶜ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxK : x ∈ K := by simpa only [mem_compl_iff, not_not] using hx
    simp only [ψ, hχ hxK, Pi.one_apply, sub_self, zero_mul]
  have hbInt' : Integrable (fun x => ψ x * b x) μ :=
    hbInt.restrict.bdd_mul hψCont.aestronglyMeasurable
      (Eventually.of_forall hψM)
  have hψInt : Integrable ψ μ := by
    let : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
    exact (integrable_const (1 : ℝ)).sub (integrable_test_topMeasure hb χ).restrict
  have hΩ : ∀ᵐ x ∂μ, x ∈ Ω := by
    have h : ∀ᵐ x ∂topMeasure hb, x ∈ Ω := by
      rw [ae_iff]
      exact topMeasure_compl hb
    exact ae_mono Measure.restrict_le_self h
  have huTail : (∫ x, ψ x * u x ∂topMeasure hu) = B := by
    rw [hRestrict, topMeasure_restrict_compl_eq_of_eq_off_compact hu hb hK huEq]
    apply integral_congr_ae
    filter_upwards [hΩ, ae_restrict_mem hK.measurableSet.compl] with x hx hKx
    rw [huEq ⟨hx, hKx⟩]
  have hqTail (j : ℕ) :
      (∫ x, ψ x * q j x ∂topMeasure (hq j)) = a j ^ n * (a j * B + d j * C) := by
    let f (x : ComplexModel n) := a j * b x + d j
    have hf : IsLocallyBoundedPshOn Ω f :=
      locallyBoundedPsh_add_const (locallyBoundedPsh_const_mul hb (ha j)) (d j)
    have hM : topMeasure hf = ENNReal.ofReal (a j ^ n) • topMeasure hb := by
      rw [topMeasure_add_const (locallyBoundedPsh_const_mul hb (ha j)),
        topMeasure_const_mul hb (ha j)]
    rw [hRestrict, topMeasure_restrict_compl_eq_of_eq_off_compact (hq j) hf hK (hqEq j),
      hM, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (pow_nonneg (ha j).le _), smul_eq_mul]
    congr 1
    have heq : (∫ x, ψ x * q j x ∂μ) = ∫ x, a j * (ψ x * b x) + d j * ψ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hΩ, ae_restrict_mem hK.measurableSet.compl] with x hx hKx
      rw [hqEq j ⟨hx, hKx⟩]
      ring
    rw [heq, integral_add (hbInt'.const_mul _) (hψInt.const_mul _),
      integral_const_mul, integral_const_mul]
  have htail : Tendsto (fun j => a j ^ n * (a j * B + d j * C)) atTop (𝓝 B) := by
    simpa only [one_pow, one_mul, zero_mul, add_zero] using
      (haLim.pow n).mul ((haLim.mul_const B).add (hdLim.mul_const C))
  simp_rw [hSplit (hqInt _), hqTail, hSplit huInt, huTail]
  exact (tendsto_weightedTopMeasure_of_decreasing hu hu hq hq hanti hanti hlim hlim χ).add htail

end KEBall.BedfordTaylor
