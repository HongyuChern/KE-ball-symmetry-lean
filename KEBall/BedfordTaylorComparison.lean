import KEBall.BedfordTaylorTruncationLocality
import KEBall.BedfordTaylorCompactDifference

/-!
# Comparison of bounded Monge–Ampère measures
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

/-- Comparison when the maximum differs from the first potential only on a
compact subset of the domain. -/
theorem topMeasure_comparison_of_eq_off_compact (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (hfin : topMeasure hu univ < ⊤)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (he : ∀ x ∈ (Ω : Set (ComplexModel n)) \ K, v x ≤ u x) :
    topMeasure hv {x ∈ Ω | u x < v x} ≤ topMeasure hu {x ∈ Ω | u x ≤ v x} := by
  let A : Set (ComplexModel n) := {x ∈ Ω | u x < v x}
  let B : Set (ComplexModel n) := {x ∈ Ω | v x < u x}
  let hq := locallyBoundedPsh_max hu hv
  let ρ := topMeasure hq
  have hmax : EqOn u (fun x => max (u x) (v x)) (Ω \ K) :=
    fun x hx => (max_eq_left (he x hx)).symm
  have htotal : ρ univ = topMeasure hu univ :=
    (topMeasure_total_eq_of_eq_off_compact hu hq hK hKΩ hmax).symm
  have hA : (topMeasure hv).restrict A = ρ.restrict A := by
    have h := topMeasure_restrict_gt_max hv hu
    have heq : EqOn (fun x => max (v x) (u x)) (fun x => max (u x) (v x)) Ω :=
      fun x _ => max_comm _ _
    rw [topMeasure_congr _ hq heq] at h
    exact h
  have hB : (topMeasure hu).restrict B = ρ.restrict B := topMeasure_restrict_gt_max hu hv
  have hmassA : topMeasure hv A = ρ A := by
    simpa only [Measure.restrict_apply_univ] using
      congrArg (fun μ : Measure (ComplexModel n) => μ univ) hA
  have hmassB : topMeasure hu B = ρ B := by
    simpa only [Measure.restrict_apply_univ] using
      congrArg (fun μ : Measure (ComplexModel n) => μ univ) hB
  have hBmeas := measurableSet_lt_of_locallyBoundedPsh hv hu
  have hBfin : topMeasure hu B ≠ ⊤ := ((measure_mono (subset_univ B)).trans_lt hfin).ne
  have hcompl : ρ Bᶜ = topMeasure hu Bᶜ := by
    apply (ENNReal.add_right_inj hBfin).mp
    rw [hmassB, measure_add_measure_compl hBmeas, ← hmassB,
      measure_add_measure_compl hBmeas, htotal]
  have hsubset : A ⊆ Bᶜ := fun _ hx hxB => (not_lt_of_ge hx.2.le) hxB.2
  calc
    topMeasure hv A = ρ A := hmassA
    _ ≤ ρ Bᶜ := measure_mono hsubset
    _ = topMeasure hu Bᶜ := hcompl
    _ ≤ topMeasure hu {x ∈ Ω | u x ≤ v x} := by
      apply measure_mono_ae
      have hae : ∀ᵐ x ∂topMeasure hu, x ∈ Ω := by
        rw [ae_iff]
        exact topMeasure_compl hu
      filter_upwards [hae] with x hx hxB
      exact ⟨hx, le_of_not_gt fun h => hxB ⟨hx, h⟩⟩

/-- The comparison principle under the boundary condition that every strict
negative shift of the second potential lies below the first off a compact set. -/
theorem topMeasure_comparison (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (hfin : topMeasure hu univ < ⊤)
    (hboundary : ∀ ε : ℝ, 0 < ε → ∃ K : Set (ComplexModel n),
      IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ (Ω : Set (ComplexModel n)) \ K, v x - ε ≤ u x) :
    topMeasure hv {x ∈ Ω | u x < v x} ≤ topMeasure hu {x ∈ Ω | u x < v x} := by
  let ε (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  let A (j : ℕ) : Set (ComplexModel n) := {x ∈ Ω | u x < v x + -ε j}
  have hmono : Monotone A := by
    intro i j hij x hx
    have he : ε j ≤ ε i := one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hij)
    exact ⟨hx.1, hx.2.trans_le (add_le_add le_rfl (neg_le_neg he))⟩
  have hUnion : (⋃ j, A j) = {x ∈ Ω | u x < v x} := by
    ext x
    rw [mem_iUnion]
    constructor
    · rintro ⟨j, hx⟩
      exact ⟨hx.1, hx.2.trans (by linarith [hε j])⟩
    · intro hx
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hx.2)
      exact ⟨j, hx.1, by
        change u x < v x + -ε j
        change ε j < v x - u x at hj
        linarith⟩
  rw [← hUnion, hmono.measure_iUnion]
  apply iSup_le
  intro j
  obtain ⟨K, hK, hKΩ, hKorder⟩ := hboundary (ε j) (hε j)
  let hv' := locallyBoundedPsh_add_const hv (-ε j)
  have h := topMeasure_comparison_of_eq_off_compact hu hv' hfin hK hKΩ
    (fun x hx => by simpa only [← sub_eq_add_neg] using hKorder x hx)
  rw [topMeasure_add_const hv (-ε j)] at h
  exact h.trans (measure_mono fun x hx => by
    have hx' : u x ≤ v x + -ε j := hx.2
    rw [hUnion]
    exact ⟨hx.1, hx'.trans_lt (by linarith [hε j])⟩)

end KEBall.BedfordTaylor
