import KEBall.BedfordTaylorCenteredHessian
import KEBall.BedfordTaylorOrderedMollification
import KEBall.BedfordTaylorProductBoundaryDifference
import KEBall.BedfordTaylorProductFiberExtension

/-!
# The base Hessian of a mollified product envelope
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsDecreasingApproximation IsLocallyBoundedPshOn RelativelyCompactIn)
open PshLines.Regularization.HolomorphicPullback

/-- Distance to the fiber sphere on the interior, extended by zero to
the exterior. -/
noncomputable def fiberBoundaryDistance (n m : ℕ) (x : ComplexModel (n + m)) : ℝ :=
  max (1 - ‖(complexProductCoordinates n m x).1‖) 0

private theorem one_sub_fst_norm_sq_le {n m : ℕ} (x : ComplexModel (n + m)) :
    1 - ‖(complexProductCoordinates n m x).1‖ ^ 2 ≤ 2 * fiberBoundaryDistance n m x := by
  let a := ‖(complexProductCoordinates n m x).1‖
  change 1 - a ^ 2 ≤ 2 * max (1 - a) 0
  by_cases ha : a ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr ha)]
    nlinarith only [sq_nonneg (a - 1)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge ha))]
    have h₁ : 1 ≤ a := le_of_not_ge ha
    nlinarith only [h₁, mul_nonneg (sub_nonneg.mpr h₁) (show 0 ≤ a + 1 by linarith)]

private theorem fiberBoundaryDistance_add_le {n m : ℕ} (x t : ComplexModel (n + m)) :
    fiberBoundaryDistance n m (x + t) ≤ fiberBoundaryDistance n m x + ‖t‖ := by
  let e := complexProductCoordinates n m
  have h := norm_sub_le ((e x).1 + (e t).1) ((e t).1)
  rw [add_sub_cancel_right] at h
  have h' : ‖(e x).1‖ ≤ ‖(e (x + t)).1‖ + ‖t‖ := by
    rw [map_add, Prod.fst_add]
    exact h.trans (add_le_add le_rfl (norm_fst_complexProductCoordinates_le (n := n) (m := m) t))
  apply max_le
  · have hmax : 1 - ‖(e x).1‖ ≤ fiberBoundaryDistance n m x := le_max_left _ _
    change 1 - ‖(e (x + t)).1‖ ≤ _
    linarith only [h', hmax]
  · exact add_nonneg (le_max_right _ _) (norm_nonneg t)

set_option maxHeartbeats 900000 in
/-- Radial regularization of the potential extended by a fiberwise
quadratic has a base Hessian bound that vanishes at the fiber sphere in
the limit of the kernel radii. -/
theorem exists_productEnvelope_fiber_regularization {n m : ℕ} {R r δ : ℝ}
    (hR : 0 < R) (hR₁ : R < 1) (hδ : 0 < δ) (hrδ : r + δ < 1)
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x)
    {A : ℝ} (hA : 0 < A)
    (hvLower : ∀ x ∈ complexProductBall n m, A * productFiberQuadratic n m x ≤ v x)
    {W : Opens (ComplexModel (n + m))} (hW : RelativelyCompactIn W (complexProductCylinder n m)) :
    let p := gluedMax (complexProductBall n m : Set (ComplexModel (n + m))) v
      (fun x => A * productFiberQuadratic n m x)
    ∃ (q : ℕ → ComplexModel (n + m) → ℝ) (s : ℝ) (hs : 0 < s) (K : Set (ComplexModel (n + m))),
      IsCompact K ∧ K ⊆ complexProductCylinder n m ∧ (∀ x ∈ W, closedBall x s ⊆ K) ∧
      IsDecreasingApproximation W p q ∧ (∀ j, ContDiff ℝ ∞ (q j)) ∧
      (∀ j, q j = translationPairing volume (K.indicator p) (explicitRadialKernel s hs j)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) x, x ∈ W →
        ‖(complexProductCoordinates n m x).2‖ + s / ((j : ℝ) + 1) ≤ r →
        ∀ y : ComplexModel (n + m), (complexProductCoordinates n m y).1 = 0 →
          PshLines.realHessian (q j) x y y ≤
            C * (fiberBoundaryDistance n m x + s / ((j : ℝ) + 1)) * ‖y‖ ^ 2 := by
  let P := complexProductBall n m
  let e := complexProductCoordinates n m
  let Ω := complexProductCylinder n m
  let b (x : ComplexModel (n + m)) := A * productFiberQuadratic n m x
  let p := gluedMax (P : Set (ComplexModel (n + m))) v b
  have hv₀ (x : ComplexModel (n + m)) (hx : x ∈ P) : v x ≤ 0 := (hvf x hx).trans (by
    by_cases hxR : x ∈ ball 0 R
    · simpa only [indicator_of_mem hxR] using hu₀ x hxR
    · simp only [indicator_of_notMem hxR, le_refl])
  have hp : IsLocallyBoundedPshOn Ω p := locallyBoundedPsh_gluedMax_productFiberQuadratic hv hv₀ hA hvLower
  obtain ⟨C₀, hC₀, hbase⟩ :=
    exists_productEnvelope_base_difference_le hR hR₁ hδ.le hrδ hu hu₀ huBoundary hv hvf hgreatest
  have hpBase (a : ComplexModel (n + m)) (har : ‖(e a).2‖ ≤ r) (h : ComplexModel (n + m))
      (hfst : (e h).1 = 0) (hh : ‖h‖ ≤ δ) :
      p (a + h) + p (a - h) - 2 * p a ≤ 2 * C₀ * ‖h‖ ^ 2 * fiberBoundaryDistance n m a := by
    have hplus : (e (a + h)).1 = (e a).1 := by rw [map_add, Prod.fst_add, hfst, add_zero]
    have hminus : (e (a - h)).1 = (e a).1 := by rw [map_sub, Prod.fst_sub, hfst, sub_zero]
    have hnorm (k : ComplexModel (n + m)) (hk : ‖k‖ ≤ δ) :
        ‖(e (a + k)).2‖ < 1 := by
      rw [map_add, Prod.snd_add]
      exact ((norm_add_le _ _).trans (add_le_add har
        ((norm_snd_complexProductCoordinates_le (n := n) (m := m) k).trans hk))).trans_lt hrδ
    by_cases ha : a ∈ P
    · have ha₁ := (mem_complexProductBall.mp ha).1
      have hmem₁ : a + h ∈ P := mem_complexProductBall.mpr ⟨hplus ▸ ha₁, hnorm h hh⟩
      have hmem₂ : a - h ∈ P := mem_complexProductBall.mpr
        ⟨hminus ▸ ha₁, by simpa only [sub_eq_add_neg] using hnorm (-h) (by simpa only [norm_neg] using hh)⟩
      have hpv (x : ComplexModel (n + m)) (hx : x ∈ P) : p x = v x :=
        (gluedMax_eq_max hx).trans (max_eq_left (hvLower x hx))
      rw [hpv _ hmem₁, hpv _ hmem₂, hpv _ ha]
      calc
        _ ≤ C₀ * ‖h‖ ^ 2 * (1 - ‖(e a).1‖ ^ 2) := hbase a ha har h hfst hh
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_left (one_sub_fst_norm_sq_le (n := n) (m := m) a)
            (mul_nonneg hC₀ (sq_nonneg ‖h‖))
          exact h.trans_eq (by ring)
    · have ha₁ : ¬ ‖(e a).1‖ < 1 := fun h =>
        ha (mem_complexProductBall.mpr ⟨h, har.trans_lt (by linarith)⟩)
      have h₁ : a + h ∉ P := fun h => ha₁ (hplus ▸ (mem_complexProductBall.mp h).1)
      have h₂ : a - h ∉ P := fun h => ha₁ (hminus ▸ (mem_complexProductBall.mp h).1)
      have hpEq (x : ComplexModel (n + m)) (hx : x ∉ P) : p x = b x := by
        classical
        simp only [p, gluedMax, if_neg (show x ∉ (P : Set (ComplexModel (n + m))) from hx)]
      rw [hpEq _ h₁, hpEq _ h₂, hpEq _ ha]
      change A * (‖(e (a + h)).1‖ ^ 2 - 1) + A * (‖(e (a - h)).1‖ ^ 2 - 1) -
        2 * (A * (‖(e a).1‖ ^ 2 - 1)) ≤ _
      rw [hplus, hminus, ← two_mul, sub_self]
      exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hC₀) (sq_nonneg _)) (le_max_right _ _)
  obtain ⟨f, hf, _, _, s, hs, K, hK, hKΩ, _, hformula, hball⟩ :=
    exists_order_preserving_smoothApproximation_centered hW
  let q := f p
  have hpInt : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact
      (PshLines.FirstPass.MongeAmpere.locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)
      hK hKΩ).locallyIntegrable
  have hqSmooth (j : ℕ) : ContDiff ℝ ∞ (q j) := by
    rw [show q j = _ from hformula p j]
    exact contDiff_translationPairing hpInt (explicitRadialKernel_hasCompactSupport s hs j)
      (explicitRadialKernel_contDiff s hs j)
  refine ⟨q, s, hs, K, hK, hKΩ, hball, hf p hp, hqSmooth, hformula p, 2 * C₀, by positivity, ?_⟩
  intro j x hx hxr y hy
  let ε := s / ((j : ℝ) + 1)
  let C := 2 * C₀ * (fiberBoundaryDistance n m x + ε)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg zero_le_two hC₀)
    (add_nonneg (le_max_right _ _) (by dsimp [ε]; positivity))
  have hDiff (h : ComplexModel (n + m)) (hfst : (e h).1 = 0) (hh : ‖h‖ ≤ δ)
      (hplus : x + h ∈ W) (hminus : x - h ∈ W) :
      q j (x + h) + q j (x - h) - 2 * q j x ≤ C * ‖h‖ ^ 2 := by
    rw [show q j = _ from hformula p j]
    apply centered_difference_translationPairing_le hpInt
      (explicitRadialKernel_hasCompactSupport s hs j)
      (explicitRadialKernel_contDiff s hs j).continuous
      (explicitRadialKernel_nonneg s hs j) (explicitRadialKernel_integral_one s hs j)
    intro t ht
    have htS := subset_tsupport (explicitRadialKernel s hs j) ht
    have htε : ‖t‖ ≤ ε := by simpa only [explicitRadialKernel_tsupport, mem_closedBall,
      dist_zero_right, ε] using htS
    have htK (a : ComplexModel (n + m)) (ha : a ∈ W) : a + t ∈ K := by
      apply hball a ha
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact htε.trans (div_le_self hs.le (le_add_of_nonneg_left (Nat.cast_nonneg j)))
    have hr : ‖(e (x + t)).2‖ ≤ r := by
      rw [map_add, Prod.snd_add]
      exact ((norm_add_le _ _).trans (add_le_add le_rfl
        ((norm_snd_complexProductCoordinates_le (n := n) (m := m) t).trans htε))).trans hxr
    have he₁ : x + h + t = x + t + h := by abel
    have he₂ : x - h + t = x + t - h := by abel
    rw [indicator_of_mem (htK _ hplus), indicator_of_mem (htK _ hminus),
      indicator_of_mem (htK _ hx), he₁, he₂]
    calc
      _ ≤ 2 * C₀ * ‖h‖ ^ 2 * fiberBoundaryDistance n m (x + t) := hpBase (x + t) hr h hfst hh
      _ ≤ 2 * C₀ * ‖h‖ ^ 2 * (fiberBoundaryDistance n m x + ε) :=
        mul_le_mul_of_nonneg_left
          ((fiberBoundaryDistance_add_le x t).trans (add_le_add le_rfl htε)) (by positivity)
      _ = _ := by dsimp [C]; ring
  have hu₂ : ContDiffAt ℝ 2 (q j) x := ((hqSmooth j).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  apply realHessian_le_of_eventually_centered_line hu₂ y
  have ht : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 (0 : ComplexModel (n + m))) := by
    have hc : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hb : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, ‖h‖ ≤ δ := by
    filter_upwards [ball_mem_nhds (0 : ComplexModel (n + m)) hδ] with h hh
    exact (mem_ball_zero_iff.mp hh).le
  have hplus : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, x + h ∈ W := by
    have hc : Continuous (fun h : ComplexModel (n + m) => x + h) := continuous_const.add continuous_id
    exact hc.continuousAt (x := 0) (W.isOpen.mem_nhds (by simpa only [add_zero] using (show x ∈ (W : Set (ComplexModel (n + m))) from hx)))
  have hminus : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, x - h ∈ W := by
    have hc : Continuous (fun h : ComplexModel (n + m) => x - h) := continuous_const.sub continuous_id
    exact hc.continuousAt (x := 0) (W.isOpen.mem_nhds (by simpa only [sub_zero] using (show x ∈ (W : Set (ComplexModel (n + m))) from hx)))
  filter_upwards [ht.eventually hb, ht.eventually hplus, ht.eventually hminus] with t ht₀ ht₁ ht₂
  have hty : (e (t • y)).1 = 0 := by
    let er : ComplexModel (n + m) →L[ℝ] ComplexModel n × ComplexModel m :=
      e.toContinuousLinearMap.restrictScalars ℝ
    have hmap : e (t • y) = t • e y := er.map_smul t y
    rw [hmap, Prod.smul_fst, hy, smul_zero]
  have h := hDiff (t • y) hty ht₀ ht₁ ht₂
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
  exact h.trans_eq (by dsimp only [C]; ring)

end KEBall.BedfordTaylor
