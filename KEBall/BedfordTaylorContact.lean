import KEBall.BedfordTaylorComparison

/-!
# Domination of the Monge–Ampère measure on a contact set
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

/-- For two ordered bounded PSH potentials, the lower potential's
Monge–Ampère measure is dominated by the upper one's on the contact set. -/
theorem topMeasure_restrict_contact_le (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (hle : ∀ x ∈ Ω, u x ≤ v x) :
    let G : Set (ComplexModel n) := {x ∈ Ω | u x = v x}
    (topMeasure hu).restrict G ≤ (topMeasure hv).restrict G := by
  let G : Set (ComplexModel n) := {x ∈ Ω | u x = v x}
  have hG : MeasurableSet G := by
    have he : G = (Ω : Set (ComplexModel n)) \ {x ∈ Ω | u x < v x} := by
      ext x
      exact ⟨fun hx => ⟨hx.1, fun h => h.2.ne hx.2⟩,
        fun hx => ⟨hx.1, (hle x hx.1).antisymm (le_of_not_gt fun h => hx.2 ⟨hx.1, h⟩)⟩⟩
    rw [he]
    exact Ω.isOpen.measurableSet.diff (measurableSet_lt_of_locallyBoundedPsh hu hv)
  have hμ : (topMeasure hu).restrict G ≤ topMeasure hv := by
    apply ambientMeasure_le_of_smooth_test
      (by exact le_antisymm ((Measure.restrict_le_self _).trans_eq (topMeasure_compl hu)) bot_le)
      (topMeasure_compl hv)
      (fun _ hK hKΩ => (Measure.restrict_le_self _).trans_lt (topMeasure_finite_on_compact hu hK hKΩ))
      (fun _ hK hKΩ => topMeasure_finite_on_compact hv hK hKΩ)
    intro χ hχ
    let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
    have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
    have hεAnti : Antitone ε := fun i j hij => one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
    have hεLim : Tendsto ε atTop (𝓝 0) :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
    let w (j : ℕ) (x : ComplexModel n) := max (u x + ε j) (v x)
    let hU (j : ℕ) := locallyBoundedPsh_add_const hu (ε j)
    let hW (j : ℕ) := locallyBoundedPsh_max (hU j) hv
    have hAnti (x : ComplexModel n) (_ : x ∈ Ω) : Antitone (fun j => w j x) :=
      fun i j hij => max_le_max_right _ (add_le_add le_rfl (hεAnti hij))
    have hLim (x : ComplexModel n) (hx : x ∈ Ω) :
        Tendsto (fun j => w j x) atTop (𝓝 (v x)) := by
      simpa only [w, add_zero, max_eq_right (hle x hx)] using
        ((tendsto_const_nhds (x := u x)).add hεLim).max (tendsto_const_nhds (x := v x))
    have h := tendsto_topMeasure_of_decreasing hv hW hAnti hLim χ χ.continuous
      χ.hasCompactSupport χ.tsupport_subset
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds h
    intro j
    let A : Set (ComplexModel n) := {x ∈ Ω | v x < u x + ε j}
    have hGA : G ⊆ A := fun x hx => ⟨hx.1, hx.2 ▸ lt_add_of_pos_right _ (hε j)⟩
    have hLocal : (topMeasure hu).restrict A = (topMeasure (hW j)).restrict A := by
      have he := topMeasure_restrict_gt_max (hU j) hv
      rw [topMeasure_add_const hu (ε j)] at he
      exact he
    have hOrder : (topMeasure hu).restrict G ≤ topMeasure (hW j) := calc
      _ ≤ (topMeasure hu).restrict A := Measure.restrict_mono_set _ hGA
      _ = _ := hLocal
      _ ≤ _ := Measure.restrict_le_self
    exact integral_mono_measure hOrder (Eventually.of_forall hχ) (integrable_test_topMeasure (hW j) χ)
  have hres := Measure.restrict_mono (s := G) le_rfl hμ
  rwa [Measure.restrict_restrict hG, inter_self] at hres

end KEBall.BedfordTaylor
