import KEBall.CegrellClass
import KEBall.BedfordTaylorComparison

/-!
# Energy bounds for Cegrell truncations
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

theorem sublevel_closure_subset (hu : IsE0 Ω u) {c : ℝ} (hc : c < 0) :
    closure {x ∈ Ω | u x ≤ c} ⊆ Ω := by
  let F := {x ∈ Ω | u x ≤ c}
  have hF : F ⊆ Ω := fun _ hx => hx.1
  intro x hx
  by_contra hxΩ
  have hxFront : x ∈ frontier (Ω : Set (ComplexModel n)) := by
    rw [frontier, Ω.isOpen.interior_eq]
    exact ⟨closure_mono hF hx, hxΩ⟩
  let : NeBot (𝓝[F] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hlim : Tendsto u (𝓝[F] x) (𝓝 0) := (hu.boundary x hxFront).mono_left (nhdsWithin_mono x hF)
  have hmem : ∀ᶠ y in 𝓝[F] x, y ∈ F := self_mem_nhdsWithin
  obtain ⟨y, hyF, hygt⟩ := (hmem.and (hlim.eventually_const_lt hc)).exists
  exact (not_lt_of_ge hyF.2) hygt

/-- Comparison with a nonpositive locally bounded PSH potential. The
first potential has zero boundary trace and finite total mass. -/
theorem IsE0.compare (hΩ : IsCompact (closure (Ω : Set (ComplexModel n))))
    (hu : IsE0 Ω u) {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) (hneg : ∀ x ∈ Ω, v x ≤ 0) :
    topMeasure hv {x ∈ Ω | u x < v x} ≤
      topMeasure hu.locallyBoundedPsh {x ∈ Ω | u x < v x} := by
  apply topMeasure_comparison hu.locallyBoundedPsh hv hu.finiteMass
  intro ε hε
  let K := closure {x ∈ Ω | u x ≤ -ε}
  have hKΩ : K ⊆ Ω := sublevel_closure_subset hu (neg_lt_zero.mpr hε)
  have hK : IsCompact K :=
    hΩ.of_isClosed_subset isClosed_closure (closure_mono fun _ hx => hx.1)
  refine ⟨K, hK, hKΩ, fun x hx => ?_⟩
  have hlt : -ε < u x := lt_of_not_ge fun h => hx.2 (subset_closure ⟨hx.1, h⟩)
  exact (sub_le_sub_right (hneg x hx.1) ε).trans (by simpa only [zero_sub] using hlt.le)

theorem truncation_totalMass (hΩ : IsCompact (closure (Ω : Set (ComplexModel n))))
    (hu : IsE0 Ω u) {c : ℝ} (hc : c < 0) :
    topMeasure (locallyBoundedPsh_max_const hu.locallyBoundedPsh c) univ =
      topMeasure hu.locallyBoundedPsh univ := by
  let K := closure {x ∈ Ω | u x ≤ c}
  have hKΩ : K ⊆ Ω := sublevel_closure_subset hu hc
  have hK : IsCompact K :=
    hΩ.of_isClosed_subset isClosed_closure (closure_mono fun _ hx => hx.1)
  apply (topMeasure_total_eq_of_eq_off_compact hu.locallyBoundedPsh
    (locallyBoundedPsh_max_const hu.locallyBoundedPsh c) hK hKΩ ?_).symm
  intro x hx
  have hcx : c < u x := lt_of_not_ge fun h => hx.2 (subset_closure ⟨hx.1, h⟩)
  exact (max_eq_left hcx.le).symm

theorem IsE0.truncate (hu : IsE0 Ω u) (hΩ : IsCompact (closure (Ω : Set (ComplexModel n))))
    {c : ℝ} (hc : c < 0) : IsE0 Ω (fun x => max (u x) c) := by
  have hq := locallyBoundedPsh_max_const hu.locallyBoundedPsh c
  obtain ⟨C, hC⟩ := hu.bounded
  refine ⟨hq.1, ⟨max C |c|, fun x hx => ?_⟩, ?_, ?_⟩
  · exact abs_le.mpr ⟨
      (neg_le_neg (le_max_left C |c|)).trans ((abs_le.mp (hC x hx)).1.trans (le_max_left _ _)),
      max_le (((abs_le.mp (hC x hx)).2).trans (le_max_left _ _))
        ((le_abs_self c).trans (le_max_right _ _))⟩
  · intro z hz
    simpa only [max_eq_left hc.le] using (hu.boundary z hz).max
      (tendsto_const_nhds (x := c) (f := 𝓝[Ω] z))
  · exact (truncation_totalMass hΩ hu hc).trans_lt hu.finiteMass

/-- The energy of a bounded potential does not increase under a
constant truncation below zero. -/
theorem boundedEnergy_truncate_le (hΩ : IsCompact (closure (Ω : Set (ComplexModel n))))
    (hu : IsE0 Ω u) {c : ℝ} (hc : c < 0) :
    boundedEnergy (hu.truncate hΩ hc) ≤ boundedEnergy hu := by
  let q := fun x => max (u x) c
  let μ := topMeasure hu.locallyBoundedPsh
  let ν := topMeasure (hu.truncate hΩ hc).locallyBoundedPsh
  let G := {x ∈ Ω | c < u x}
  have hG : MeasurableSet G := measurableSet_gt_on_domain hu.locallyBoundedPsh c
  have hRes : μ.restrict G = ν.restrict G := topMeasure_restrict_gt_truncation hu.locallyBoundedPsh c
  have hResMass := congrArg (fun ρ : Measure (ComplexModel n) => ρ univ) hRes
  simp only [Measure.restrict_apply_univ] at hResMass
  have hGFin : μ G ≠ ⊤ := (measure_mono (subset_univ G)).trans_lt hu.finiteMass |>.ne
  have hTotal : ν univ = μ univ := truncation_totalMass hΩ hu hc
  have hTail : ν Gᶜ = μ Gᶜ := by
    apply (ENNReal.add_right_inj hGFin).mp
    rw [hResMass, measure_add_measure_compl hG, ← hResMass, measure_add_measure_compl hG, hTotal]
  have hEq : (∫⁻ x in G, ENNReal.ofReal (-q x) ∂ν) =
      ∫⁻ x in G, ENNReal.ofReal (-u x) ∂μ := by
    rw [← hRes]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hG] with x hx
    change ENNReal.ofReal (-max (u x) c) = _
    rw [max_eq_left hx.2.le]
  have hDom {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Ω w) :
      ∀ᵐ x ∂topMeasure hw, x ∈ Ω := by
    rw [ae_iff]
    exact topMeasure_compl hw
  have hRight : (∫⁻ x in Gᶜ, ENNReal.ofReal (-q x) ∂ν) ≤
      ∫⁻ x in Gᶜ, ENNReal.ofReal (-u x) ∂μ := calc
    _ = ∫⁻ _ in Gᶜ, ENNReal.ofReal (-c) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hG.compl, ae_mono Measure.restrict_le_self
        (hDom (hu.truncate hΩ hc).locallyBoundedPsh)] with x hx hxΩ
      have hxc : u x ≤ c := le_of_not_gt fun h => hx ⟨hxΩ, h⟩
      simp only [q, max_eq_right hxc]
    _ = ∫⁻ _ in Gᶜ, ENNReal.ofReal (-c) ∂μ := by
      rw [lintegral_const, lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply_univ, hTail]
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hG.compl, ae_mono Measure.restrict_le_self
        (hDom hu.locallyBoundedPsh)] with x hx hxΩ
      exact ENNReal.ofReal_le_ofReal (neg_le_neg (le_of_not_gt fun h => hx ⟨hxΩ, h⟩))
  change (∫⁻ x, ENNReal.ofReal (-q x) ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (-u x) ∂μ
  rw [← lintegral_add_compl (μ := ν) (fun x => ENNReal.ofReal (-q x)) hG,
    ← lintegral_add_compl (μ := μ) (fun x => ENNReal.ofReal (-u x)) hG, hEq]
  exact add_le_add_right hRight _

end KEBall.Cegrell
