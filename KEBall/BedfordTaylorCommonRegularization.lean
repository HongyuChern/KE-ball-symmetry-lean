import KEBall.BedfordTaylorNonsmoothWeights
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Synchronized regularization of potentials with a compact difference
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ} {Ω A : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

theorem decreasing_explicitRegularization
    (hu : IsLocallyBoundedPshOn Ω u) {R : ℝ} (hR : 0 < R)
    {N K : Set (ComplexModel n)} (hN : IsOpen N) (hAN : (A : Set _) ⊆ N)
    (hNΩ : N ⊆ Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hball : ∀ x ∈ N, closedBall x R ⊆ K) :
    IsDecreasingApproximation A u
      (fun j => translationPairing volume (K.indicator u) (explicitRadialKernel R hR j)) := by
  let huL := locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have huLevi := hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1
  obtain ⟨S, hSkernel⟩ := exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
    hu hR hN hNΩ hK hKΩ hball
  let f (j : ℕ) := translationPairing volume (K.indicator u) (S.kernel j)
  have hEq (j : ℕ) : S.kernel j = explicitRadialKernel R hR j := funext (hSkernel j)
  have hf (j : ℕ) : IsSmoothPshOn A (f j) := by
    have hd := discPshOn_translationPairing_indicator huL huLevi
      (S.kernel_hasCompactSupport j) (S.kernel_contDiff j) (S.kernel_nonneg j)
      hK hKΩ (S.translated_tsupport j)
    have hI := (integrable_indicator_of_locallyIntegrableOn_isCompact huL hK hKΩ).locallyIntegrable
    exact isSmoothPshOn_of_psh
      (contDiff_translationPairing hI (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)).contDiffOn
      ((hd.plurisubharmonicOn hN).mono hAN)
  have hanti (x : ComplexModel n) (hx : x ∈ A) : Antitone (fun j => f j x) :=
    S.antitone_pairing x (hAN hx)
  have hae := ae_mono (Measure.restrict_mono hAN le_rfl) S.ae_tendsto_pairing
  have hpoint := tendsto_everywhere_of_ae_of_antitone_psh (hu.1.mono (hAN.trans hNΩ))
    (fun j => (hf j).2.1) hanti hae
  simpa only [f, hEq] using (show IsDecreasingApproximation A u f from ⟨hf, hanti, hpoint⟩)

/-- Use the same radial convolution for both potentials. The approximants
agree outside any prescribed compact neighborhood of the original difference. -/
theorem exists_common_decreasingRegularization
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hA : RelativelyCompactIn A Ω)
    {L L' : Set (ComplexModel n)} (hL : IsCompact L) (hLL' : L ⊆ interior L')
    (he : EqOn u v ((Ω : Set (ComplexModel n)) \ L)) :
    ∃ p q : ℕ → ComplexModel n → ℝ, IsDecreasingApproximation A u p ∧
      IsDecreasingApproximation A v q ∧ ∀ j, EqOn (p j) (q j) ((A : Set _) \ L') := by
  let : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR, N, K, hN, hclAN, hNK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 Ω.isOpen hA.2
  obtain ⟨r, hr, hthick⟩ := hL.exists_cthickening_subset_open isOpen_interior hLL'
  let ρ := min R r
  have hρ : 0 < ρ := lt_min hR hr
  have hρball (x : ComplexModel n) (hx : x ∈ N) : closedBall x ρ ⊆ K :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans (hball x hx)
  have hAN := subset_closure.trans hclAN
  let p (j : ℕ) := translationPairing volume (K.indicator u) (explicitRadialKernel ρ hρ j)
  let q (j : ℕ) := translationPairing volume (K.indicator v) (explicitRadialKernel ρ hρ j)
  refine ⟨p, q, decreasing_explicitRegularization hu hρ hN hAN (hNK.trans hKΩ) hK hKΩ hρball,
    decreasing_explicitRegularization hv hρ hN hAN (hNK.trans hKΩ) hK hKΩ hρball, ?_⟩
  intro j z hz
  change translationPairing volume (K.indicator u) _ z =
    translationPairing volume (K.indicator v) _ z
  unfold translationPairing
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxs : x ∈ tsupport (fun x => explicitRadialKernel ρ hρ j (x - z))
  · have hxball : x ∈ closedBall z ρ := closedBall_subset_closedBall
      (shrinkingBump_rOut_le ρ hρ j) (tsupport_explicitRadialKernel_translate_subset ρ hρ j z hxs)
    have hxK := hρball z (hAN hz.1) hxball
    have hxL : x ∉ L := by
      intro h
      have hdist : dist z x ≤ r := by
        rw [dist_comm]
        exact (mem_closedBall.mp hxball).trans (min_le_right _ _)
      exact hz.2 (interior_subset (hthick (mem_cthickening_of_dist_le z x r L h hdist)))
    rw [indicator_of_mem hxK, indicator_of_mem hxK, he ⟨hKΩ hxK, hxL⟩]
  · have hzK : explicitRadialKernel ρ hρ j (x - z) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => explicitRadialKernel ρ hρ j (y - z)) hxs
    rw [hzK, mul_zero, mul_zero]

end KEBall.BedfordTaylor
