import KEBall.BedfordTaylorLocallyBoundedMonotone

/-!
# Cegrell's bounded and finite-energy classes

The bounded class uses the actual Bedford–Taylor measure. The
finite-energy class allows extended-real potentials and uses bounded
approximants with a uniform energy bound.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

private theorem locallyBoundedPsh_of_bounded {u : ComplexModel n → ℝ}
    (hp : PlurisubharmonicOn (fun x => (u x : EReal)) Ω)
    (hb : ∃ C : ℝ, ∀ x ∈ Ω, |u x| ≤ C) :
    IsLocallyBoundedPshOn Ω u := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨hp, fun x hx => ⟨Ω, hx, le_rfl, C, hC⟩⟩

/-- Bounded PSH potentials with zero boundary values and finite
Bedford–Taylor mass. -/
structure IsE0 (Ω : Opens (ComplexModel n)) (u : ComplexModel n → ℝ) : Prop where
  psh : PlurisubharmonicOn (fun x => (u x : EReal)) Ω
  bounded : ∃ C : ℝ, ∀ x ∈ Ω, |u x| ≤ C
  boundary : ∀ z ∈ frontier (Ω : Set (ComplexModel n)), Tendsto u (𝓝[Ω] z) (𝓝 0)
  finiteMass : topMeasure (locallyBoundedPsh_of_bounded psh bounded) univ < ⊤

theorem IsE0.locallyBoundedPsh {u : ComplexModel n → ℝ} (hu : IsE0 Ω u) :
    IsLocallyBoundedPshOn Ω u :=
  locallyBoundedPsh_of_bounded hu.psh hu.bounded

/-- The nonnegative energy integral on the bounded class. -/
noncomputable def boundedEnergy {u : ComplexModel n → ℝ} (hu : IsE0 Ω u) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-u x) ∂topMeasure hu.locallyBoundedPsh

theorem boundedEnergy_lt_top {u : ComplexModel n → ℝ} (hu : IsE0 Ω u) :
    boundedEnergy hu < ⊤ := by
  obtain ⟨C, hC⟩ := hu.bounded
  let μ := topMeasure hu.locallyBoundedPsh
  have hAE : ∀ᵐ x ∂μ, x ∈ Ω := by
    rw [ae_iff]
    exact topMeasure_compl hu.locallyBoundedPsh
  calc
    boundedEnergy hu ≤ ∫⁻ _ : ComplexModel n, ENNReal.ofReal C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hAE] with x hx
      exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hC x hx))
    _ < ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.finiteMass

/-- A defining sequence for the finite-energy class. -/
structure E1Approximation (Ω : Opens (ComplexModel n)) (u : ComplexModel n → EReal) where
  term : ℕ → ComplexModel n → ℝ
  term_mem : ∀ j, IsE0 Ω (term j)
  antitone : ∀ x ∈ Ω, Antitone (fun j => term j x)
  pointwise : ∀ x ∈ Ω, Tendsto (fun j => (term j x : EReal)) atTop (𝓝 (u x))
  energyBound : (⨆ j, boundedEnergy (term_mem j)) < ⊤

/-- The finite-energy class defined by decreasing bounded approximants. -/
def IsE1 (Ω : Opens (ComplexModel n)) (u : ComplexModel n → EReal) : Prop :=
  PlurisubharmonicOn u Ω ∧ Nonempty (E1Approximation Ω u)

theorem IsE0.isE1 {u : ComplexModel n → ℝ} (hu : IsE0 Ω u) :
    IsE1 Ω (fun x => (u x : EReal)) := by
  refine ⟨hu.psh, ⟨⟨fun _ => u, fun _ => hu, fun _ _ _ _ _ => le_rfl,
    fun _ _ => tendsto_const_nhds, ?_⟩⟩⟩
  simpa only [ciSup_const] using boundedEnergy_lt_top hu

/-- Smoothness on a neighborhood of the compact closure, PSH in the
domain, and zero boundary values imply membership in the bounded class. -/
theorem isE0_of_smoothOn_closure {u : ComplexModel n → ℝ} {W : Opens (ComplexModel n)}
    (hcompact : IsCompact (closure (Ω : Set (ComplexModel n))))
    (hW : closure (Ω : Set (ComplexModel n)) ⊆ W)
    (hu : IsSmoothPshOn Ω u) (hs : ContDiffOn ℝ ∞ u W)
    (hzero : EqOn u 0 (frontier (Ω : Set (ComplexModel n)))) :
    IsE0 Ω u := by
  have hbound : ∃ C : ℝ, ∀ x ∈ Ω, |u x| ≤ C := by
    obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn (hs.continuousOn.mono hW).abs).bddAbove
    exact ⟨C, fun x hx => hC ⟨x, subset_closure hx, rfl⟩⟩
  refine ⟨hu.2.1, hbound, ?_, ?_⟩
  · intro z hz
    have hzW := hW (frontier_subset_closure hz)
    have h : ContinuousWithinAt u (Ω : Set (ComplexModel n)) z :=
      (hs.continuousOn.continuousAt (W.isOpen.mem_nhds hzW)).continuousWithinAt
    simpa only [ContinuousWithinAt, hzero hz, Pi.zero_apply] using h
  · rw [show topMeasure (locallyBoundedPsh_of_bounded hu.2.1 hbound) = smoothMeasure Ω u hu from
      topMeasure_eq_smoothMeasure hu, smoothMeasure, withDensity_apply _ MeasurableSet.univ]
    obtain ⟨C, hC⟩ :=
      (hcompact.image_of_continuousOn ((continuousOn_smoothDensity hs).mono hW)).bddAbove
    calc
      _ ≤ ∫⁻ _ : ComplexModel n, ENNReal.ofReal C ∂volume.restrict Ω := by
        rw [Measure.restrict_univ]
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
        exact ENNReal.ofReal_le_ofReal (hC ⟨x, subset_closure hx, rfl⟩)
      _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((measure_mono (subset_closure (s := (Ω : Set (ComplexModel n))))).trans_lt
            hcompact.measure_lt_top)

end KEBall.Cegrell
