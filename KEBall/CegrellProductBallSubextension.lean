import KEBall.BedfordTaylorProductEnvelopeContact
import KEBall.CegrellObstacleSubextension
import KEBall.BedfordTaylorProductEnvelopeApproximation

/-!
# A mass-controlled subextension from a ball to a product ball
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn isSmoothPshOn_norm_sq)

set_option maxHeartbeats 600000 in
/-- A smooth nonpositive bounded Cegrell potential on the smaller ball
admits a bounded zero-boundary subextension to the product ball. Its
Monge–Ampère measure is dominated by the original one extended by zero. -/
theorem exists_productBall_subextension_withEnvelope {n m : ℕ} (hn : 0 < n + m)
    {R : ℝ} (hR : 0 < R) (hR₁ : R < 1)
    {u : ComplexModel (n + m) → ℝ} (hu : IsE0 (⟨ball 0 R, isOpen_ball⟩ : Opens (ComplexModel (n + m))) u)
    (huSmooth : ContDiff ℝ 2 u) (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0)
    (huBoundary : ∀ x ∈ sphere 0 R, u x = 0) :
    ∃ v : ComplexModel (n + m) → ℝ, ∃ hv : IsE0 (complexProductBall n m) v,
      topMeasure hv.locallyBoundedPsh ≤ topMeasure hu.locallyBoundedPsh ∧
      (∀ x ∈ ball 0 R, v x ≤ u x) ∧
      ContinuousOn v (complexProductBall n m) ∧
      (∀ x ∈ complexProductBall n m, v x ≤ 0) ∧
      (∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) ∧
      (∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
        (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x) ∧
      ∃ A > 0, ∀ x ∈ complexProductBall n m,
        A * max (‖(complexProductCoordinates n m x).1‖ ^ 2 - 1)
          (‖(complexProductCoordinates n m x).2‖ ^ 2 - 1) ≤ v x := by
  let X := ComplexModel (n + m)
  let P := complexProductBall n m
  let B : Opens X := ⟨ball 0 R, isOpen_ball⟩
  let e := complexProductCoordinates n m
  have hBP : B ≤ P := by
    intro x hx
    have hxR : ‖x‖ < R := by
      change x ∈ ball 0 R at hx
      simpa only [mem_ball, dist_zero_right] using hx
    exact mem_complexProductBall.mpr
      ⟨(norm_fst_complexProductCoordinates_le x).trans_lt (hxR.trans hR₁),
       (norm_snd_complexProductCoordinates_le x).trans_lt (hxR.trans hR₁)⟩
  have hvol : (volume : Measure X) (P : Set X) < ⊤ := by
    apply (measure_mono (t := closedBall (0 : X) 2) ?_).trans_lt
      (isCompact_closedBall (0 : X) 2).measure_lt_top
    intro x hx
    obtain ⟨h₁, h₂⟩ := mem_complexProductBall.mp hx
    rw [mem_closedBall, dist_zero_right]
    exact (norm_le_complexProductCoordinates x).trans (by linarith)
  let ρ (x : X) := max (‖(e x).1‖ ^ 2 - 1) (‖(e x).2‖ ^ 2 - 1)
  have hρCont : Continuous ρ :=
    (e.continuous.fst.norm.pow 2 |>.sub continuous_const).max
      (e.continuous.snd.norm.pow 2 |>.sub continuous_const)
  have hterm (k : ℕ) : IsLocallyBoundedPshOn (⊤ : Opens (ComplexModel k))
      (fun x => ‖x‖ ^ 2 - 1) := by
    simpa only [sub_eq_add_neg] using locallyBoundedPsh_add_const
      (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_norm_sq (⊤ : Opens (ComplexModel k)))) (-1)
  have hρ : IsLocallyBoundedPshOn P ρ := by
    exact locallyBoundedPsh_max
      (locallyBoundedPsh_comp_holomorphic (hterm n) (e.differentiable.differentiableOn.fst) (fun _ _ => by simp))
      (locallyBoundedPsh_comp_holomorphic (hterm m) (e.differentiable.differentiableOn.snd) (fun _ _ => by simp))
  have hρlt (x : X) : x ∈ P ↔ ρ x < 0 := by
    rw [mem_complexProductBall]
    change (‖(e x).1‖ < 1 ∧ ‖(e x).2‖ < 1) ↔
      max (‖(e x).1‖ ^ 2 - 1) (‖(e x).2‖ ^ 2 - 1) < 0
    rw [max_lt_iff]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨by nlinarith only [hx, norm_nonneg (e x).1],
        by nlinarith only [hy, norm_nonneg (e x).2]⟩
    · rintro ⟨hx, hy⟩
      exact ⟨by nlinarith only [hx, norm_nonneg (e x).1],
        by nlinarith only [hy, norm_nonneg (e x).2]⟩
  have hρboundary (z : X) (hz : z ∈ frontier (P : Set X)) : Tendsto ρ (𝓝[P] z) (𝓝 0) := by
    have hz' := hz
    rw [frontier, P.isOpen.interior_eq] at hz'
    have hρclosed : IsClosed {x : X | ρ x ≤ 0} := isClosed_le hρCont continuous_const
    have hzle : ρ z ≤ 0 := closure_minimal
      (fun x hx => ((hρlt x).mp hx).le) hρclosed hz'.1
    have hzge : 0 ≤ ρ z := le_of_not_gt (fun h => hz'.2 ((hρlt z).mpr h))
    have heq := hzle.antisymm hzge
    rw [← heq]
    exact hρCont.continuousAt.continuousWithinAt
  have hη : 0 < 1 - R ^ 2 := by nlinarith only [hR, hR₁]
  have hρB (x : X) (hx : x ∈ B) : ρ x ≤ -(1 - R ^ 2) := by
    have hxR : ‖x‖ < R := by
      change x ∈ ball 0 R at hx
      simpa only [mem_ball, dist_zero_right] using hx
    have h₁ := pow_le_pow_left₀ (norm_nonneg (e x).1)
      ((norm_fst_complexProductCoordinates_le x).trans hxR.le) 2
    have h₂ := pow_le_pow_left₀ (norm_nonneg (e x).2)
      ((norm_snd_complexProductCoordinates_le x).trans hxR.le) 2
    exact max_le (by linarith only [h₁]) (by linarith only [h₂])
  obtain ⟨v, hv, hvB, hvf, hvBoundary, hvGreatest, hLower⟩ :=
    exists_zeroExtendedObstacle_envelope (Ω := B) (V := P) hu hu₀ hvol hρ
      (fun x hx => ((hρlt x).mp hx).le) hρboundary hη hρB
  have hcontact := topMeasure_productEnvelope_off_contact_eq_zero hn huSmooth hu₀ huBoundary hv hvf hvGreatest
  obtain ⟨hvE0, hμ, hle⟩ := IsE0.of_zeroExtendedObstacle_contact hn hu hu₀ hBP hv hvB hvf hvBoundary hcontact
  have hvCont : ContinuousOn v P := by
    intro x hx
    obtain ⟨W, hxW, _, hD, _⟩ := exists_lipschitz_fderiv_productEnvelope
      huSmooth hu₀ huBoundary hv hvf hvGreatest hx
    exact ((hD x hxW).differentiableAt (W.isOpen.mem_nhds hxW)).continuousAt.continuousWithinAt
  have hvNonpos (x : X) (hx : x ∈ P) : v x ≤ 0 := (hvf x hx).trans (by
    by_cases hxB : x ∈ B
    · simpa only [Set.indicator_of_mem hxB] using hu₀ x hxB
    · rw [Set.indicator_of_notMem hxB])
  exact ⟨v, hvE0, hμ, hle, hvCont, hvNonpos, hvf, hvGreatest, hLower⟩

/-- The bounded zero-boundary subextension with its dominated top measure. -/
theorem exists_productBall_subextension {n m : ℕ} (hn : 0 < n + m)
    {R : ℝ} (hR : 0 < R) (hR₁ : R < 1)
    {u : ComplexModel (n + m) → ℝ} (hu : IsE0 (⟨ball 0 R, isOpen_ball⟩ : Opens (ComplexModel (n + m))) u)
    (huSmooth : ContDiff ℝ 2 u) (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0)
    (huBoundary : ∀ x ∈ sphere 0 R, u x = 0) :
    ∃ v : ComplexModel (n + m) → ℝ, ∃ hv : IsE0 (complexProductBall n m) v,
      topMeasure hv.locallyBoundedPsh ≤ topMeasure hu.locallyBoundedPsh ∧
      (∀ x ∈ ball 0 R, v x ≤ u x) ∧
      ContinuousOn v (complexProductBall n m) ∧
      (∀ x ∈ complexProductBall n m, v x ≤ 0) ∧
      ∃ A > 0, ∀ x ∈ complexProductBall n m,
        A * max (‖(complexProductCoordinates n m x).1‖ ^ 2 - 1)
          (‖(complexProductCoordinates n m x).2‖ ^ 2 - 1) ≤ v x := by
  obtain ⟨v, hv, hm, hle, hc, hv₀, _, _, hb⟩ :=
    exists_productBall_subextension_withEnvelope hn hR hR₁ hu huSmooth hu₀ huBoundary
  exact ⟨v, hv, hm, hle, hc, hv₀, hb⟩

end KEBall.Cegrell
