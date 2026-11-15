import KEBall.BedfordTaylorComparison
import KEBall.BedfordTaylorQuadraticPerturbation
import PshLines.PlurisubharmonicAE

/-!
# Domination for locally bounded potentials of finite mass
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

/-- Measure domination and the comparison boundary condition imply pointwise
ordering on a bounded domain. -/
theorem le_of_topMeasure_le (hn : 0 < n)
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hfin : topMeasure hu univ < ⊤) (hμ : topMeasure hu ≤ topMeasure hv)
    (hΩ : ∃ C : ℝ, ∀ x ∈ Ω, ‖x‖ ^ 2 ≤ C)
    (hboundary : ∀ ε : ℝ, 0 < ε → ∃ K : Set (ComplexModel n),
      IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ (Ω : Set (ComplexModel n)) \ K, v x - ε ≤ u x) :
    ∀ x ∈ Ω, v x ≤ u x := by
  obtain ⟨C, hC⟩ := hΩ
  have hpert (δ : ℝ) (hδ : 0 < δ) :
      ∀ x ∈ Ω, v x + δ * ‖x‖ ^ 2 + -(δ * C) ≤ u x := by
    let w : ComplexModel n → ℝ := fun x => v x + δ * ‖x‖ ^ 2 + -(δ * C)
    let hvq := locallyBoundedPsh_add_quadratic hv hδ
    have hw : IsLocallyBoundedPshOn Ω w := locallyBoundedPsh_add_const hvq _
    have hwu (x : ComplexModel n) (hx : x ∈ Ω) : w x ≤ v x := by
      dsimp [w]
      linarith [mul_le_mul_of_nonneg_left (hC x hx) hδ.le]
    let A : Set (ComplexModel n) := {x ∈ Ω | u x < w x}
    have hcomp : topMeasure hw A ≤ topMeasure hu A := by
      apply topMeasure_comparison hu hw hfin
      intro ε hε
      obtain ⟨K, hK, hKΩ, hKord⟩ := hboundary ε hε
      exact ⟨K, hK, hKΩ, fun x hx => (sub_le_sub_right (hwu x hx.1) ε).trans (hKord x hx)⟩
    let density := ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * δ ^ n)
    have hdensity : 0 < density := ENNReal.ofReal_pos.mpr (by positivity)
    have hmass : topMeasure hu A + density * volume.restrict (Ω : Set (ComplexModel n)) A ≤
        topMeasure hu A := by
      have hq := topMeasure_add_quadratic_ge hn hv hδ A
      rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at hq
      rw [show topMeasure hw = topMeasure hvq from topMeasure_add_const hvq _] at hcomp
      exact (add_le_add (hμ A) le_rfl).trans (hq.trans hcomp)
    have hzero : volume.restrict (Ω : Set (ComplexModel n)) A = 0 := by
      have hAfinite : topMeasure hu A ≠ ⊤ :=
        ((measure_mono (subset_univ A)).trans_lt hfin).ne
      have hprod := ENNReal.le_of_add_le_add_left hAfinite (hmass.trans (le_of_eq (add_zero _).symm))
      exact (mul_eq_zero.mp (nonpos_iff_eq_zero.mp hprod)).resolve_left hdensity.ne'
    have ha : ∀ᵐ x ∂volume.restrict (Ω : Set (ComplexModel n)), (w x : EReal) ≤ (u x : EReal) := by
      have hmem : ∀ᵐ x ∂volume.restrict (Ω : Set (ComplexModel n)), x ∈ Aᶜ := by
        rw [ae_iff]
        change volume.restrict (Ω : Set (ComplexModel n)) (Aᶜ)ᶜ = 0
        rwa [compl_compl]
      filter_upwards [hmem, ae_restrict_mem Ω.isOpen.measurableSet] with x hxA hxΩ
      exact EReal.coe_le_coe_iff.mpr (le_of_not_gt fun h => hxA ⟨hxΩ, h⟩)
    intro x hx
    exact EReal.coe_le_coe_iff.mp
      (hw.1.le_of_ae_le Ω.isOpen hu.1.upperSemicontinuousOn volume ha x hx)
  intro x hx
  by_contra! hxlt
  let d := C - ‖x‖ ^ 2 + 1
  have hd : 0 < d := by dsimp [d]; linarith [hC x hx]
  obtain ⟨δ, hδ, hδsmall⟩ := exists_between (div_pos (sub_pos.mpr hxlt) hd)
  have hh := hpert δ hδ x hx
  have hsmall := (lt_div_iff₀ hd).mp hδsmall
  dsimp [d] at hsmall
  nlinarith only [hh, hsmall, hδ]

/-- A zero top measure implies maximality for locally bounded PSH
competitors that lie below the potential off a compact set. -/
theorem le_of_topMeasure_eq_zero (hn : 0 < n)
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hzero : topMeasure hu = 0) (hΩ : ∃ C : ℝ, ∀ x ∈ Ω, ‖x‖ ^ 2 ≤ C)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (horder : ∀ x ∈ (Ω : Set (ComplexModel n)) \ K, v x ≤ u x) :
    ∀ x ∈ Ω, v x ≤ u x := by
  have hfin : topMeasure hu univ < ⊤ := by simp [hzero]
  have hμ : topMeasure hu ≤ topMeasure hv := by rw [hzero]; exact Measure.zero_le _
  exact le_of_topMeasure_le hn hu hv hfin hμ hΩ
    (fun ε hε => ⟨K, hK, hKΩ, fun x hx => (sub_le_self _ hε.le).trans (horder x hx)⟩)

end KEBall.BedfordTaylor
