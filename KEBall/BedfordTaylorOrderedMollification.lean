import KEBall.BedfordTaylorMixedApproximation

/-!
# Order-preserving local smooth regularization
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ} {Ω A : Opens (ComplexModel n)}

/-- A bound on the centered differences at the points sampled by a
nonnegative normalized kernel is preserved by convolution. -/
theorem centered_difference_translationPairing_le
    {p k : ComplexModel n → ℝ} (hp : LocallyIntegrable p volume)
    (hk : HasCompactSupport k) (hkC : Continuous k) (hk₀ : ∀ x, 0 ≤ k x)
    (hk₁ : (∫ t, k t) = 1) {x h : ComplexModel n} {C : ℝ}
    (hbound : ∀ t, k t ≠ 0 → p (x + h + t) + p (x - h + t) - 2 * p (x + t) ≤ C) :
    translationPairing volume p k (x + h) + translationPairing volume p k (x - h) -
      2 * translationPairing volume p k x ≤ C := by
  have hshift (a : ComplexModel n) : translationPairing volume p k a = ∫ t, p (a + t) * k t := by
    let w (y : ComplexModel n) := p y * k (y - a)
    have ht : (∫ t, w (t + a)) = ∫ t, w t := integral_add_right_eq_self w a
    simp only [w, add_sub_cancel_right] at ht
    simpa only [translationPairing, add_comm] using ht.symm
  have hInt (a : ComplexModel n) : Integrable (fun t => p (a + t) * k t) volume := by
    let w (y : ComplexModel n) := p y * k (y - a)
    have hw : Integrable w volume := integrable_translationPairing hp hk hkC a
    have h := hw.comp_add_right a
    simp only [w, add_sub_cancel_right] at h
    simpa only [add_comm] using h
  have hPoint (t : ComplexModel n) :
      p (x + h + t) * k t + p (x - h + t) * k t - 2 * (p (x + t) * k t) ≤ C * k t := by
    by_cases ht : k t = 0
    · simp only [ht, mul_zero, add_zero, sub_zero, le_refl]
    calc
      _ = (p (x + h + t) + p (x - h + t) - 2 * p (x + t)) * k t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ht) (hk₀ t)
  have hplus : Integrable (fun t => p (x + h + t) * k t + p (x - h + t) * k t) volume :=
    (hInt (x + h)).add (hInt (x - h))
  rw [hshift (x + h), hshift (x - h), hshift x, ← integral_add (hInt (x + h)) (hInt (x - h)),
    ← integral_const_mul, ← integral_sub hplus ((hInt x).const_mul 2)]
  calc
    _ ≤ ∫ t, C * k t :=
      integral_mono (hplus.sub ((hInt x).const_mul 2))
        ((hkC.integrable_of_hasCompactSupport hk).const_mul _) hPoint
    _ = _ := by rw [integral_const_mul, hk₁, mul_one]

set_option maxHeartbeats 500000 in
/-- Fix a common kernel sequence and cutoff region for all potentials.
On the inner domain, this regularization preserves pointwise order. -/
theorem exists_order_preserving_smoothApproximation_centered (hA : RelativelyCompactIn A Ω) :
    ∃ f : (ComplexModel n → ℝ) → ℕ → ComplexModel n → ℝ,
      (∀ p, IsLocallyBoundedPshOn Ω p → IsDecreasingApproximation A p (f p)) ∧
      (∀ p q, IsLocallyBoundedPshOn Ω p → IsLocallyBoundedPshOn Ω q →
        (∀ x ∈ Ω, p x ≤ q x) → ∀ j x, x ∈ A → f p j x ≤ f q j x) ∧
      (∀ p, IsLocallyBoundedPshOn Ω p → ∀ C δ : ℝ,
        (∀ x ∈ Ω, ∀ h : ComplexModel n, ‖h‖ ≤ δ →
          p (x + h) + p (x - h) - 2 * p x ≤ C * ‖h‖ ^ 2) →
        ∀ j x, x ∈ A → ∀ h : ComplexModel n, ‖h‖ ≤ δ → x + h ∈ A → x - h ∈ A →
          f p j (x + h) + f p j (x - h) - 2 * f p j x ≤ C * ‖h‖ ^ 2) ∧
      ∃ (R : ℝ) (hR : 0 < R) (K : Set (ComplexModel n)),
        IsCompact K ∧ K ⊆ Ω ∧ (A : Set (ComplexModel n)) ⊆ interior K ∧
        (∀ p j, f p j = translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)) ∧
        ∀ x ∈ A, closedBall x R ⊆ K := by
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR, N, K, hN, hclAN, hNK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 Ω.isOpen hA.2
  have hAN : (A : Set (ComplexModel n)) ⊆ N := subset_closure.trans hclAN
  have hAΩ : (A : Set (ComplexModel n)) ⊆ Ω := hAN.trans (hNK.trans hKΩ)
  let f : (ComplexModel n → ℝ) → ℕ → ComplexModel n → ℝ := fun p j =>
    translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)
  have hL (p : ComplexModel n → ℝ) (hp : IsLocallyBoundedPshOn Ω p) :
      LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact
      (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1) hK hKΩ).locallyIntegrable
  refine ⟨f, ?_, ?_, ?_, R, hR, K, hK, hKΩ, hAN.trans ?_, (fun _ _ => rfl), fun x hx => hball x (hAN hx)⟩
  · intro p hp
    let hpL := locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
    have hpLevi := hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hp.1
    obtain ⟨S, hS⟩ := exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
      hp hR hN (hNK.trans hKΩ) hK hKΩ hball
    have hEq (j : ℕ) : S.kernel j = explicitRadialKernel R hR j := funext (hS j)
    have hPsh (j : ℕ) : PlurisubharmonicOn (fun x => (f p j x : EReal)) A := by
      have hdisc := discPshOn_translationPairing_indicator hpL hpLevi
        (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
        (S.kernel_nonneg j) hK hKΩ (S.translated_tsupport j)
      rw [hEq j] at hdisc
      exact ((hdisc.plurisubharmonicOn hN).mono hAN)
    have hSmooth (j : ℕ) : IsSmoothPshOn A (f p j) :=
      isSmoothPshOn_of_psh (contDiff_translationPairing (hL p hp)
        (explicitRadialKernel_hasCompactSupport R hR j) (explicitRadialKernel_contDiff R hR j)).contDiffOn (hPsh j)
    have hanti : ∀ x ∈ A, Antitone (fun j => f p j x) := by
      intro x hx
      simpa only [hEq, f] using S.antitone_pairing x (hAN hx)
    have hae : ∀ᵐ x ∂volume.restrict (A : Set (ComplexModel n)),
        Tendsto (fun j => f p j x) atTop (𝓝 (p x)) := by
      apply ae_mono (Measure.restrict_mono hAN le_rfl)
      have haeN := S.ae_tendsto_pairing
      change ∀ᵐ x ∂volume.restrict N,
        Tendsto (fun j => translationPairing volume (K.indicator p) (S.kernel j) x) atTop (𝓝 (p x)) at haeN
      simp only [hEq] at haeN
      exact haeN
    exact ⟨hSmooth, hanti, tendsto_everywhere_of_ae_of_antitone_psh (hp.1.mono hAΩ) hPsh hanti hae⟩
  · intro p q hp hq hpq j x hx
    apply integral_mono
    · exact integrable_translationPairing (hL p hp) (explicitRadialKernel_hasCompactSupport R hR j)
        (explicitRadialKernel_contDiff R hR j).continuous x
    · exact integrable_translationPairing (hL q hq) (explicitRadialKernel_hasCompactSupport R hR j)
        (explicitRadialKernel_contDiff R hR j).continuous x
    · intro y
      apply mul_le_mul_of_nonneg_right _ (explicitRadialKernel_nonneg R hR j (y - x))
      by_cases hy : y ∈ K
      · simpa only [indicator_of_mem hy] using hpq y (hKΩ hy)
      · simp only [indicator_of_notMem hy, le_refl]
  · intro p hp C δ hbound j x hx h hh hxplus hxminus
    rw [show f p j = translationPairing volume (K.indicator p) (explicitRadialKernel R hR j) by rfl]
    apply centered_difference_translationPairing_le (hL p hp)
      (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff R hR j).continuous
      (explicitRadialKernel_nonneg R hR j) (explicitRadialKernel_integral_one R hR j)
    intro t ht
    have htS := subset_tsupport (explicitRadialKernel R hR j) ht
    have htR : ‖t‖ ≤ R := by
      rw [explicitRadialKernel_tsupport, mem_closedBall, dist_zero_right] at htS
      exact htS.trans (div_le_self hR.le (le_add_of_nonneg_left (Nat.cast_nonneg j)))
    have htK (a : ComplexModel n) (ha : a ∈ A) : a + t ∈ K := by
      apply hball a (hAN ha)
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using htR
    have he₁ : x + h + t = x + t + h := by abel
    have he₂ : x - h + t = x + t - h := by abel
    rw [indicator_of_mem (htK (x + h) hxplus), indicator_of_mem (htK (x - h) hxminus),
      indicator_of_mem (htK x hx), he₁, he₂]
    exact hbound (x + t) (hKΩ (htK x hx)) h hh
  · exact interior_maximal hNK hN

theorem exists_order_preserving_smoothApproximation (hA : RelativelyCompactIn A Ω) :
    ∃ f : (ComplexModel n → ℝ) → ℕ → ComplexModel n → ℝ,
      (∀ p, IsLocallyBoundedPshOn Ω p → IsDecreasingApproximation A p (f p)) ∧
      ∀ p q, IsLocallyBoundedPshOn Ω p → IsLocallyBoundedPshOn Ω q →
        (∀ x ∈ Ω, p x ≤ q x) → ∀ j x, x ∈ A → f p j x ≤ f q j x := by
  obtain ⟨f, hf, hmono, _, _⟩ := exists_order_preserving_smoothApproximation_centered hA
  exact ⟨f, hf, hmono⟩

end KEBall.BedfordTaylor
