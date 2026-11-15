import KEBall.BedfordTaylorDomination
import KEBall.CegrellClass

/-!
# Comparing a larger-domain potential with the zero-boundary potential
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω V : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

/-- Negative sublevel sets of an E₀ potential stay away from the boundary. -/
theorem IsE0.exists_compact_sublevel (hu : IsE0 Ω u)
    (hΩ : IsCompact (closure (Ω : Set (ComplexModel n)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ Ω ∧
      ∀ x ∈ (Ω : Set (ComplexModel n)) \ K, -ε ≤ u x := by
  let A : Set (ComplexModel n) := {x ∈ Ω | u x < -ε}
  have hAΩ : A ⊆ Ω := fun _ hx => hx.1
  refine ⟨closure A, hΩ.of_isClosed_subset isClosed_closure (closure_mono hAΩ), ?_, ?_⟩
  · intro x hx
    by_contra hxΩ
    have hxFront : x ∈ frontier (Ω : Set (ComplexModel n)) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨closure_mono hAΩ hx, hxΩ⟩
    let : NeBot (𝓝[A] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    have hlim : Tendsto u (𝓝[A] x) (𝓝 0) :=
      (hu.boundary x hxFront).mono_left (nhdsWithin_mono x hAΩ)
    have hmem : ∀ᶠ y in 𝓝[A] x, y ∈ A := self_mem_nhdsWithin
    obtain ⟨y, hyA, hyu⟩ := (hmem.and (hlim.eventually_const_lt (neg_lt_zero.mpr hε))).exists
    exact (not_lt_of_ge hyu.le) hyA.2
  · intro x hx
    exact le_of_not_gt fun h => hx.2 (subset_closure (show x ∈ A from ⟨hx.1, h⟩))

/-- A nonpositive larger-domain potential whose Monge–Ampère measure dominates
the original measure is a subextension of the original E₀ potential. -/
theorem IsE0.subextension_le (hn : 0 < n) (hu : IsE0 Ω u)
    (hΩ : IsCompact (closure (Ω : Set (ComplexModel n)))) (hΩV : Ω ≤ V)
    (hv : IsLocallyBoundedPshOn V v) (hv₀ : ∀ x ∈ Ω, v x ≤ 0)
    (hμ : topMeasure hu.locallyBoundedPsh ≤ topMeasure hv) :
    ∀ x ∈ Ω, v x ≤ u x := by
  have hμ' : topMeasure hu.locallyBoundedPsh ≤ topMeasure (IsLocallyBoundedPshOn.mono hv hΩV) := by
    rw [← topMeasure_restrict hv hΩV]
    have hself : (topMeasure hu.locallyBoundedPsh).restrict (Ω : Set (ComplexModel n)) =
        topMeasure hu.locallyBoundedPsh := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact topMeasure_compl hu.locallyBoundedPsh
    rw [← hself]
    exact Measure.restrict_mono Subset.rfl hμ
  apply le_of_topMeasure_le hn hu.locallyBoundedPsh (IsLocallyBoundedPshOn.mono hv hΩV) hu.finiteMass hμ'
  · obtain ⟨C, hC⟩ := (hΩ.image (continuous_norm.pow 2)).bddAbove
    exact ⟨C, fun x hx => hC ⟨x, subset_closure hx, rfl⟩⟩
  · intro ε hε
    obtain ⟨K, hK, hKΩ, hKord⟩ := hu.exists_compact_sublevel hΩ hε
    exact ⟨K, hK, hKΩ, fun x hx => by linarith [hv₀ x hx.1, hKord x hx]⟩

end KEBall.Cegrell
