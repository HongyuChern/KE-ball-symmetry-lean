import KEBall.BedfordTaylorLocallyBoundedMonotone
import KEBall.BedfordTaylorTruncationLocality
import PshLines.PlurisubharmonicLimits

/-!
# Uniform convergence of locally bounded Bedford–Taylor potentials
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
  {q : ℕ → ComplexModel n → ℝ}

private theorem exists_shifted_decreasing_subseq
    (hU : TendstoUniformlyOn q u atTop Ω) :
    ∃ φ : ℕ → ℕ, ∃ c : ℕ → ℝ,
      (∀ x ∈ Ω, Antitone (fun j => q (φ j) x + c j)) ∧
      (∀ x ∈ Ω, Tendsto (fun j => q (φ j) x + c j) atTop (𝓝 (u x))) ∧
      (∀ x ∈ Ω, |q (φ 0) x - u x| ≤ 1) := by
  let ε (j : ℕ) := (1 / 2 : ℝ) ^ j
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεLim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨φ, hφ, hdist⟩ := extraction_forall_of_eventually
    (fun j => Metric.tendstoUniformlyOn_iff.mp hU (ε j) (hε j))
  let c (j : ℕ) := 3 * ε j
  have hc : Tendsto c atTop (𝓝 0) := by simpa only [mul_zero] using hεLim.const_mul 3
  refine ⟨φ, c, ?_, ?_, ?_⟩
  · intro x hx
    apply antitone_nat_of_succ_le
    intro j
    have hj := abs_lt.mp (show |q (φ j) x - u x| < ε j by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist j x hx)
    have hj' := abs_lt.mp (show |q (φ (j + 1)) x - u x| < ε (j + 1) by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist (j + 1) x hx)
    have he : ε (j + 1) = ε j / 2 := by dsimp [ε]; rw [pow_succ]; ring
    dsimp [c]
    linarith only [hj.1, hj'.2, he]
  · intro x hx
    have h := ((hU.tendsto_at hx).comp hφ.tendsto_atTop).add hc
    simpa only [Function.comp_apply, add_zero] using h
  · intro x hx
    simpa only [ε, pow_zero, Real.dist_eq, abs_sub_comm] using (hdist 0 x hx).le

/-- A uniform limit of locally bounded plurisubharmonic potentials remains in
the same class. -/
theorem isLocallyBoundedPshOn_of_tendstoUniformlyOn
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j)) (hU : TendstoUniformlyOn q u atTop Ω) :
    IsLocallyBoundedPshOn Ω u := by
  obtain ⟨φ, c, hanti, hlim, hclose⟩ := exists_shifted_decreasing_subseq hU
  let p (j : ℕ) (x : ComplexModel n) := q (φ j) x + c j
  let hp (j : ℕ) : IsLocallyBoundedPshOn Ω (p j) := locallyBoundedPsh_add_const (hq (φ j)) _
  have hAnti (x : ComplexModel n) (hx : x ∈ Ω) : Antitone (fun j => (p j x : EReal)) :=
    fun _ _ hij => EReal.coe_le_coe_iff.mpr (hanti x hx hij)
  have hPsh := DiscPshOn.plurisubharmonicOn_iInf_of_antitone Ω.isOpen
    (fun j => (hp j).1.discPshOn) hAnti
  refine ⟨fun x hx => (hPsh x hx).congr ?_, ?_⟩
  · filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact iInf_eq_of_tendsto (hAnti y hy) (EReal.tendsto_coe.mpr (hlim y hy))
  · intro x hx
    obtain ⟨W, hxW, hW, C, hC⟩ := (hq (φ 0)).2 x hx
    refine ⟨W, hxW, hW, C + 1, fun y hy => ?_⟩
    have hD : |u y - q (φ 0) y| ≤ 1 := by rw [abs_sub_comm]; exact hclose y (hW hy)
    have h := abs_add_le (q (φ 0) y) (u y - q (φ 0) y)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add (hC y hy) hD)

/-- Uniform convergence of locally bounded PSH potentials gives weak
convergence of their Bedford–Taylor measures against compact tests. -/
theorem tendsto_topMeasure_of_tendstoUniformlyOn
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j)) (hU : TendstoUniformlyOn q u atTop Ω)
    (f : ComplexModel n → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfΩ : tsupport f ⊆ Ω) :
    Tendsto (fun j => ∫ x, f x ∂topMeasure (hq j)) atTop
      (𝓝 (∫ x, f x ∂topMeasure (isLocallyBoundedPshOn_of_tendstoUniformlyOn hq hU))) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hU' : TendstoUniformlyOn (fun j => q (ns j)) u atTop Ω := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact hns.eventually (Metric.tendstoUniformlyOn_iff.mp hU ε hε)
  obtain ⟨φ, c, hanti, hlim, _⟩ := exists_shifted_decreasing_subseq hU'
  refine ⟨φ, ?_⟩
  let p (j : ℕ) (x : ComplexModel n) := q (ns (φ j)) x + c j
  let hp (j : ℕ) : IsLocallyBoundedPshOn Ω (p j) := locallyBoundedPsh_add_const (hq (ns (φ j))) _
  have h := tendsto_topMeasure_of_decreasing (isLocallyBoundedPshOn_of_tendstoUniformlyOn hq hU)
    hp hanti hlim f hf hfc hfΩ
  exact h.congr (fun j =>
    congrArg (fun μ : Measure (ComplexModel n) => ∫ x, f x ∂μ)
      (topMeasure_add_const (hq (ns (φ j))) (c j)))

end KEBall.BedfordTaylor
