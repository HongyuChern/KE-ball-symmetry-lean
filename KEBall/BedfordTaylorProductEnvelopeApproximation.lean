import KEBall.BedfordTaylorProductObstacle
import KEBall.BedfordTaylorCenteredHessian
import KEBall.BedfordTaylorBoundedHessianLimit
import KEBall.BedfordTaylorOrderedMollification
import KEBall.BedfordTaylorSmoothObstacle

/-!
# Locally bounded Hessians for smooth approximants of product-ball envelopes
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff NNReal Topology

namespace KEBall.BedfordTaylor

open PshLines (translationPairing)
open PshLines.FirstPass (ComplexModel)
open PshLines.Regularization.HolomorphicPullback (explicitRadialKernel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn IsDecreasingApproximation RelativelyCompactIn)

set_option maxHeartbeats 800000 in
/-- On a neighborhood of every point of the product ball, the envelope of
a zero-extended smooth potential has decreasing smooth PSH approximants
with uniformly bounded full real Hessians. -/
theorem exists_boundedHessianApproximation_productEnvelope {n m : ℕ} {R : ℝ}
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x)
    {a : ComplexModel (n + m)} (ha : a ∈ complexProductBall n m) :
    ∃ W : Opens (ComplexModel (n + m)), a ∈ W ∧ RelativelyCompactIn W (complexProductBall n m) ∧
      Convex ℝ (W : Set (ComplexModel (n + m))) ∧ ∃ q : ℕ → ComplexModel (n + m) → ℝ, IsDecreasingApproximation W v q ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j x, x ∈ W → ‖fderiv ℝ (fderiv ℝ (q j)) x‖ ≤ C) ∧
      ∃ (ρ : ℝ) (hρ : 0 < ρ) (K : Set (ComplexModel (n + m))),
        IsCompact K ∧ K ⊆ complexProductBall n m ∧ (W : Set (ComplexModel (n + m))) ⊆ interior K ∧
        ∀ j, q j = translationPairing volume (K.indicator v) (explicitRadialKernel ρ hρ j) := by
  let e := complexProductCoordinates n m
  obtain ⟨ha₁, ha₂⟩ := mem_complexProductBall.mp ha
  let r := (max ‖(e a).1‖ ‖(e a).2‖ + 1) / 2
  have hmax : max ‖(e a).1‖ ‖(e a).2‖ < 1 := max_lt ha₁ ha₂
  have hr : r < 1 := by dsimp only [r]; linarith
  have hcenter : max ‖(e a).1‖ ‖(e a).2‖ < r := by dsimp only [r]; linarith
  let δ := (1 - r) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hr)
  have hrδ : r + δ < 1 := by dsimp only [δ]; linarith
  let Ω : Opens (ComplexModel (n + m)) := ⟨e ⁻¹' (ball 0 r ×ˢ ball 0 r),
    (isOpen_ball.prod isOpen_ball).preimage e.continuous⟩
  have hmem (x : ComplexModel (n + m)) : x ∈ Ω ↔ ‖(e x).1‖ < r ∧ ‖(e x).2‖ < r := by
    change e x ∈ ball 0 r ×ˢ ball 0 r ↔ _
    simp only [mem_prod, mem_ball, dist_zero_right]
  have hΩ : Ω ≤ complexProductBall n m := by
    intro x hx
    obtain ⟨h₁, h₂⟩ := (hmem x).mp hx
    exact mem_complexProductBall.mpr ⟨h₁.trans hr, h₂.trans hr⟩
  have haΩ : a ∈ Ω := (hmem a).mpr
    ⟨(le_max_left _ _).trans_lt hcenter, (le_max_right _ _).trans_lt hcenter⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen a haΩ
  let W : Opens (ComplexModel (n + m)) := ⟨ball a (ε / 2), isOpen_ball⟩
  have hrel : RelativelyCompactIn W Ω :=
    ⟨(isCompact_closedBall a (ε / 2)).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hε)).trans hball)⟩
  obtain ⟨C₀, L₀, hC₀, hL₀, hsupport⟩ := exists_quadratic_upper_support_smooth_zeroExtension hu hu₀ huBoundary
  obtain ⟨C, hC, hdiff⟩ := exists_obstacleEnvelope_centered_difference_bound_product hδ.le hrδ hC₀ hL₀
    hv hvf hgreatest (fun x _ => by
      obtain ⟨p, hp, hpx⟩ := hsupport x
      exact ⟨p, hp, fun y _ => hpx y⟩)
  have hdiffΩ (x : ComplexModel (n + m)) (hx : x ∈ Ω) (h : ComplexModel (n + m)) (hh : ‖h‖ ≤ δ) :
      v (x + h) + v (x - h) - 2 * v x ≤ C * ‖h‖ ^ 2 :=
    hdiff x ((hmem x).mp hx).1.le ((hmem x).mp hx).2.le h hh
  obtain ⟨f, hf, _, hpreserve, ρ, hρ, K, hK, hKΩ, hWK, hformula, _⟩ := exists_order_preserving_smoothApproximation_centered hrel
  let hvΩ := IsLocallyBoundedPshOn.mono hv hΩ
  refine ⟨W, mem_ball_self (half_pos hε), ⟨hrel.1, hrel.2.trans hΩ⟩, convex_ball _ _, f v, hf v hvΩ,
    ⟨C, hC, fun j x hx => ?_⟩, ρ, hρ, K, hK, hKΩ.trans hΩ, hWK, hformula v⟩
  apply norm_fderiv_fderiv_le_of_eventually_centered_difference ((hf v hvΩ).1 j) hx hC
  have hd : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, ‖h‖ ≤ δ := by
    filter_upwards [ball_mem_nhds (0 : ComplexModel (n + m)) hδ] with h hh
    exact (show ‖h‖ < δ by simpa only [mem_ball, dist_zero_right] using hh).le
  have hplus : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, x + h ∈ W := by
    have hcont : Continuous (fun h : ComplexModel (n + m) => x + h) := continuous_const.add continuous_id
    have hx' : x + (0 : ComplexModel (n + m)) ∈ W := by rwa [add_zero]
    exact hcont.continuousAt (x := 0) (W.isOpen.mem_nhds hx')
  have hminus : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, x - h ∈ W := by
    have hcont : Continuous (fun h : ComplexModel (n + m) => x - h) := continuous_const.sub continuous_id
    have hx' : x - (0 : ComplexModel (n + m)) ∈ W := by rwa [sub_zero]
    exact hcont.continuousAt (x := 0) (W.isOpen.mem_nhds hx')
  filter_upwards [hd, hplus, hminus] with h hh hp hm
  exact hpreserve v hvΩ C δ hdiffΩ j x hx h hh hp hm

/-- The envelope of a zero-extended smooth potential is locally C¹,¹
inside the product ball. -/
theorem exists_lipschitz_fderiv_productEnvelope {n m : ℕ} {R : ℝ}
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x)
    {a : ComplexModel (n + m)} (ha : a ∈ complexProductBall n m) :
    ∃ W : Opens (ComplexModel (n + m)), a ∈ W ∧ RelativelyCompactIn W (complexProductBall n m) ∧
      DifferentiableOn ℝ v W ∧ ∃ C : ℝ≥0, LipschitzOnWith C (fderiv ℝ v) W := by
  obtain ⟨W, haW, hrel, hW, q, hq, ⟨C, hC, hess⟩, _⟩ :=
    exists_boundedHessianApproximation_productEnvelope hu hu₀ huBoundary hv hvf hgreatest ha
  have hWle : W ≤ complexProductBall n m := subset_closure.trans hrel.2
  have h := differentiableOn_lipschitz_fderiv_of_boundedHessian
    (IsLocallyBoundedPshOn.mono hv hWle) hW hq hC hess
  exact ⟨W, haW, hrel, h.1, ⟨⟨C, hC⟩, h.2⟩⟩

end KEBall.BedfordTaylor
