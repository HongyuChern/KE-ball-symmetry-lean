import KEBall.BedfordTaylorContact
import KEBall.BedfordTaylorSmoothCriterion

/-!
# Mass control from contact with a zero-extended obstacle
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

variable {n : ℕ} {Ω V : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

theorem topMeasure_const (hn : 0 < n) (c : ℝ) :
    topMeasure (locallyBoundedPsh_const (Ω := Ω) c) = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    have hs : IsSmoothPshOn Ω (fun _ => c) :=
      isSmoothPshOn_of_coordinateHessian contDiffOn_const (by
        intro x _
        rw [PshLines.FirstPass.MongeAmpere.complexHessian_const]
        exact Matrix.PosSemidef.zero)
    rw [show topMeasure (locallyBoundedPsh_const (Ω := Ω) c) = smoothMeasure Ω _ hs
      from topMeasure_eq_smoothMeasure hs]
    simp only [smoothMeasure, smoothDensity_const, ENNReal.ofReal_zero]
    exact withDensity_zero

/-- A nonpositive minorant whose Monge–Ampère measure is carried by the
contact set of a zero-extended obstacle has measure dominated by that of
the original obstacle. -/
theorem topMeasure_le_of_zeroExtendedObstacle_contact (hn : 0 < n)
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn V v) (hΩV : Ω ≤ V)
    (hvu : ∀ x ∈ Ω, v x ≤ u x) (hv₀ : ∀ x ∈ V, v x ≤ 0)
    (hsupport : topMeasure hv {x ∈ V | v x < (Ω : Set (ComplexModel n)).indicator u x} = 0) :
    topMeasure hv ≤ topMeasure hu := by
  let μ := topMeasure hv
  let A : Set (ComplexModel n) := {x ∈ Ω | v x = u x}
  let B : Set (ComplexModel n) := {x ∈ V | v x = 0}
  have hB : μ B = 0 := by
    have h := topMeasure_restrict_contact_le hv (locallyBoundedPsh_const 0) hv₀
    change μ.restrict B ≤ (topMeasure (locallyBoundedPsh_const 0)).restrict B at h
    rw [topMeasure_const hn, Measure.restrict_zero] at h
    have h' := (h univ).trans_eq (show (0 : Measure (ComplexModel n)) univ = 0 by simp)
    exact le_antisymm (by simpa only [Measure.restrict_apply_univ] using h') bot_le
  have hAEV : ∀ᵐ x ∂μ, x ∈ V := by
    rw [ae_iff]
    exact topMeasure_compl hv
  have hAEB : ∀ᵐ x ∂μ, x ∉ B := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hB
  have hAEgap : ∀ᵐ x ∂μ, ¬ (x ∈ V ∧ v x < (Ω : Set (ComplexModel n)).indicator u x) := by
    rw [ae_iff]
    simpa only [not_not] using hsupport
  have hAEA : ∀ᵐ x ∂μ, x ∈ A := by
    filter_upwards [hAEV, hAEB, hAEgap] with x hxV hxB hxgap
    have hle := le_of_not_gt fun h => hxgap ⟨hxV, h⟩
    by_cases hxΩ : x ∈ Ω
    · rw [indicator_of_mem hxΩ] at hle
      exact ⟨hxΩ, (hvu x hxΩ).antisymm hle⟩
    · rw [indicator_of_notMem hxΩ] at hle
      exact (hxB ⟨hxV, (hv₀ x hxV).antisymm hle⟩).elim
  have hc := topMeasure_restrict_contact_le (IsLocallyBoundedPshOn.mono hv hΩV) hu hvu
  change (topMeasure (IsLocallyBoundedPshOn.mono hv hΩV)).restrict A ≤ (topMeasure hu).restrict A at hc
  rw [← topMeasure_restrict hv hΩV, Measure.restrict_restrict_of_subset (fun _ hx => hx.1),
    Measure.restrict_eq_self_of_ae_mem hAEA] at hc
  exact hc.trans Measure.restrict_le_self

end KEBall.BedfordTaylor
