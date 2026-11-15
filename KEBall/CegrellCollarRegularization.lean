import KEBall.CegrellQuadraticMollifier
import KEBall.BedfordTaylorScaling

/-!
# Regularization with a quadratic boundary collar
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere hiding complexHessian
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ}

private theorem locallyBoundedPsh_quadratic_global (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IsLocallyBoundedPshOn (⊤ : Opens (ComplexModel n)) (fun x => c * ballQuadratic n x) := by
  have hN : IsSmoothPshOn (⊤ : Opens (ComplexModel n)) (fun x : ComplexModel n => ‖x‖ ^ 2) := by
    apply isSmoothPshOn_of_coordinateHessian (contDiff_norm_sq ℝ).contDiffOn
    intro x _
    rw [complexHessian_norm_sq]
    exact Matrix.PosSemidef.one
  have h := locallyBoundedPsh_add_const
    (locallyBoundedPsh_const_mul (isLocallyBoundedPshOn_of_isSmoothPshOn hN) hc) (-c)
  have he : (fun x : ComplexModel n => c * ‖x‖ ^ 2 + -c) =
      (fun x => c * ballQuadratic n x) := by
    funext x
    simp only [ballQuadratic]
    ring
  exact he ▸ h

/-- A potential agreeing with the quadratic barrier off an interior compact
set has a smooth decreasing regularization. Outside a slightly larger compact
set the regularizations agree exactly with the averaged barrier. -/
theorem exists_decreasingRegularization_quadratic_collar
    {u : ComplexModel n → ℝ} (hu : IsE0 (complexUnitBall n) u)
    {c : ℝ} (hc : 0 < c)
    {K₀ : Set (ComplexModel n)} (hK₀ : IsCompact K₀) (hK₀B : K₀ ⊆ complexUnitBall n)
    (he : EqOn u (fun x => c * ballQuadratic n x) ((complexUnitBall n : Set (ComplexModel n)) \ K₀))
    (hle : ∀ x ∈ complexUnitBall n, c * ballQuadratic n x ≤ u x) :
    ∃ (R : ℝ) (hR : 0 < R) (p : ℕ → ComplexModel n → ℝ) (K' : Set (ComplexModel n)),
      IsCompact K' ∧ K' ⊆ complexUnitBall n ∧
      (∀ j, ContDiff ℝ ∞ (p j)) ∧ IsDecreasingApproximation (complexUnitBall n) u p ∧
      (∀ j x, x ∈ closure (complexUnitBall n : Set (ComplexModel n)) → x ∉ K' →
        p j x = c * (ballQuadratic n x + radialKernelSecondMoment n R hR j)) ∧
      ∀ j x, x ∈ complexUnitBall n →
        c * (ballQuadratic n x + radialKernelSecondMoment n R hR j) ≤ p j x := by
  classical
  let B := complexUnitBall n
  let b (x : ComplexModel n) := c * ballQuadratic n x
  let Ω : Opens (ComplexModel n) := ⊤
  let w := (B : Set (ComplexModel n)).piecewise u b
  have hb : IsLocallyBoundedPshOn Ω b := locallyBoundedPsh_quadratic_global n hc
  have hwEq (x : ComplexModel n) (hx : x ∉ K₀) : w x = b x := by
    by_cases hxB : x ∈ (B : Set (ComplexModel n))
    · rw [show w x = u x from piecewise_eq_of_mem _ _ _ hxB]
      exact he ⟨hxB, hx⟩
    · exact piecewise_eq_of_notMem _ _ _ hxB
  have hwGe (x : ComplexModel n) : b x ≤ w x := by
    by_cases hx : x ∈ (B : Set (ComplexModel n))
    · rw [show w x = u x from piecewise_eq_of_mem _ _ _ hx]
      exact hle x hx
    · exact (piecewise_eq_of_notMem _ _ _ hx).ge
  have hwPsh : PlurisubharmonicOn (fun x => (w x : EReal)) Ω := by
    intro x hx
    by_cases hxB : x ∈ (B : Set (ComplexModel n))
    · apply (hu.psh x hxB).congr
      filter_upwards [B.isOpen.mem_nhds hxB] with y hy
      exact congrArg (fun t : ℝ => (t : EReal)) (piecewise_eq_of_mem _ u b hy).symm
    · have hxK : x ∉ K₀ := fun h => hxB (hK₀B h)
      apply (hb.1 x hx).congr
      filter_upwards [hK₀.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact congrArg (fun t : ℝ => (t : EReal)) (hwEq y hy).symm
  have hw : IsLocallyBoundedPshOn Ω w := by
    refine ⟨hwPsh, ?_⟩
    intro x hx
    obtain ⟨W, hxW, hW, D, hD⟩ := hb.2 x hx
    obtain ⟨C, hC⟩ := hu.bounded
    refine ⟨W, hxW, hW, max C D, fun y hy => ?_⟩
    by_cases h : y ∈ (B : Set (ComplexModel n))
    · exact ((piecewise_eq_of_mem _ u b h).symm ▸ hC y h).trans (le_max_left _ _)
    · exact ((piecewise_eq_of_notMem _ u b h).symm ▸ hD y hy).trans (le_max_right _ _)
  let : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨V, hV, hK₀V, hVB, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK₀ B.isOpen hK₀B
  obtain ⟨s, hs, hsV⟩ := hK₀.exists_cthickening_subset_open hV hK₀V
  obtain ⟨r, hr, N, K, hN, hclBN, hNK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood (isCompact_closure_complexUnitBall n)
      Ω.isOpen (subset_univ _)
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  have hRball (x : ComplexModel n) (hx : x ∈ N) : closedBall x R ⊆ K :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans (hball x hx)
  have hBN : (B : Set (ComplexModel n)) ⊆ N := subset_closure.trans hclBN
  let k (j : ℕ) := explicitRadialKernel (n := n) R hR j
  let p (j : ℕ) := translationPairing volume (K.indicator w) (k j)
  have hI : Integrable (K.indicator w) volume :=
    integrable_indicator_of_locallyIntegrableOn_isCompact
      (locallyIntegrableOn_of_plurisubharmonicOn_real hw.1) hK hKΩ
  have hSmooth (j : ℕ) : ContDiff ℝ ∞ (p j) :=
    contDiff_translationPairing hI.locallyIntegrable (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff R hR j)
  have hDec := decreasing_explicitRegularization hw hR hN hBN (hNK.trans hKΩ) hK hKΩ hRball
  have hlim (x : ComplexModel n) (hx : x ∈ B) : Tendsto (fun j => p j x) atTop (𝓝 (u x)) := by
    have h := hDec.2.2 x hx
    rw [show w x = u x from piecewise_eq_of_mem _ u b hx] at h
    exact h
  have hSupp (j : ℕ) (x : ComplexModel n) (hx : x ∈ N) :
      tsupport (fun y => k j (y - x)) ⊆ K :=
    (tsupport_explicitRadialKernel_translate_subset R hR j x).trans
      ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j)).trans (hRball x hx))
  refine ⟨R, hR, p, closure V, hVc, hVB, hSmooth, ⟨hDec.1, hDec.2.1, hlim⟩, ?_, ?_⟩
  · intro j x hx hxV
    have hxN := hclBN hx
    rw [show p j x = translationPairing volume (K.indicator w) (k j) x from rfl,
      ← translationPairing_ballQuadratic c hR j x,
      ← translationPairing_indicator_eq b (k j) x (hSupp j x hxN)]
    unfold translationPairing
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ tsupport (fun y => k j (y - x))
    · have hyBall : y ∈ closedBall x R := closedBall_subset_closedBall
        (shrinkingBump_rOut_le R hR j) (tsupport_explicitRadialKernel_translate_subset R hR j x hy)
      have hy₀ : y ∉ K₀ := by
        intro h
        have hd : dist x y ≤ s := by
          rw [dist_comm]
          exact (mem_closedBall.mp hyBall).trans (min_le_right _ _)
        exact hxV (subset_closure (hsV (mem_cthickening_of_dist_le x y s K₀ h hd)))
      have hyK := hSupp j x hxN hy
      rw [indicator_of_mem hyK, indicator_of_mem hyK, hwEq y hy₀]
    · rw [image_eq_zero_of_notMem_tsupport (f := fun y => k j (y - x)) hy, mul_zero, mul_zero]
  · intro j x hx
    rw [← translationPairing_ballQuadratic c hR j x,
      ← translationPairing_indicator_eq b (k j) x (hSupp j x (hBN hx))]
    have hbI : Integrable (K.indicator b) volume :=
      integrable_indicator_of_locallyIntegrableOn_isCompact
        (locallyIntegrableOn_of_plurisubharmonicOn_real hb.1) hK hKΩ
    have hkC := (explicitRadialKernel_contDiff (n := n) R hR j).continuous
    have hkS := explicitRadialKernel_hasCompactSupport (n := n) R hR j
    exact integral_mono (integrable_translationPairing hbI.locallyIntegrable hkS hkC x)
      (integrable_translationPairing hI.locallyIntegrable hkS hkC x)
      (fun y => mul_le_mul_of_nonneg_right (indicator_le_indicator (hwGe y))
        (explicitRadialKernel_nonneg R hR j _))

end KEBall.Cegrell
