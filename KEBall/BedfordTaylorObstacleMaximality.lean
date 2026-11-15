import KEBall.BedfordTaylorObstacleEnvelope
import KEBall.BedfordTaylorQuadraticPerturbation

/-!
# Local competitors for a plurisubharmonic obstacle envelope
-/

set_option autoImplicit false

open Filter Metric Set TopologicalSpace
open scoped Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω V : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

private theorem locallyBoundedPsh_of_local {w : ComplexModel n → ℝ}
    (h : ∀ x ∈ Ω, ∃ W : Opens (ComplexModel n), x ∈ W ∧ W ≤ Ω ∧
      ∃ q, IsLocallyBoundedPshOn W q ∧ EqOn w q W) :
    IsLocallyBoundedPshOn Ω w := by
  constructor
  · intro x hx
    obtain ⟨W, hxW, _, q, hq, heq⟩ := h x hx
    apply (hq.1 x hxW).congr
    filter_upwards [W.isOpen.mem_nhds hxW] with y hy
    rw [heq hy]
  · intro x hx
    obtain ⟨W, hxW, hWΩ, q, hq, heq⟩ := h x hx
    obtain ⟨W', hxW', hW'W, C, hC⟩ := hq.2 x hxW
    exact ⟨W', hxW', hW'W.trans hWΩ, C, fun y hy => by rw [heq (hW'W hy)]; exact hC y hy⟩

theorem locallyBoundedPsh_gluedMax_of_relative_closure
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn V v)
    (hV : V ≤ Ω) {K : Set (ComplexModel n)} (hK : closure K ∩ Ω ⊆ V)
    (hcollar : ∀ x ∈ (V : Set (ComplexModel n)) \ K, v x ≤ u x) :
    IsLocallyBoundedPshOn Ω (gluedMax (V : Set (ComplexModel n)) v u) := by
  apply locallyBoundedPsh_of_local
  intro x hx
  by_cases hxV : x ∈ V
  · exact ⟨V, hxV, hV, _, locallyBoundedPsh_max hv (IsLocallyBoundedPshOn.mono hu hV),
      fun _ hy => gluedMax_eq_max hy⟩
  · let W : Opens (ComplexModel n) := ⟨Ω \ closure K, Ω.isOpen.sdiff isClosed_closure⟩
    exact ⟨W, ⟨hx, fun h => hxV (hK ⟨h, hx⟩)⟩, sdiff_subset, u,
      IsLocallyBoundedPshOn.mono hu sdiff_subset,
      fun _ hy => gluedMax_eq_global hcollar (fun h => hy.2 (subset_closure h))⟩

theorem locallyBoundedPsh_gluedMax
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn V v)
    (hV : V ≤ Ω) {K : Set (ComplexModel n)} (hK : closure K ⊆ V)
    (hcollar : ∀ x ∈ (V : Set (ComplexModel n)) \ K, v x ≤ u x) :
    IsLocallyBoundedPshOn Ω (gluedMax (V : Set (ComplexModel n)) v u) :=
  locallyBoundedPsh_gluedMax_of_relative_closure hu hv hV (fun _ hx => hK hx.1) hcollar

/-- A greatest PSH minorant cannot be raised by a local PSH competitor
under the obstacle that is below the minorant on a collar. -/
theorem le_of_obstacle_minorant {f : ComplexModel n → EReal}
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, (u x : EReal) ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, (w x : EReal) ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    (hv : IsLocallyBoundedPshOn V v) (hV : V ≤ Ω) {K : Set (ComplexModel n)}
    (hK : closure K ⊆ V) (hcollar : ∀ x ∈ (V : Set (ComplexModel n)) \ K, v x ≤ u x)
    (hvf : ∀ x ∈ V, (v x : EReal) ≤ f x) :
    ∀ x ∈ V, v x ≤ u x := by
  let w := gluedMax (V : Set (ComplexModel n)) v u
  have hw : IsLocallyBoundedPshOn Ω w := locallyBoundedPsh_gluedMax hu hv hV hK hcollar
  have hwf (x : ComplexModel n) (hx : x ∈ Ω) : (w x : EReal) ≤ f x := by
    by_cases hxV : x ∈ V
    · rcases le_total (v x) (u x) with h | h
      · rw [show w x = u x from (gluedMax_eq_max hxV).trans (max_eq_right h)]
        exact huf x hx
      · rw [show w x = v x from (gluedMax_eq_max hxV).trans (max_eq_left h)]
        exact hvf x hxV
    · rw [show w x = u x from gluedMax_eq_global hcollar (fun h => hxV (hK (subset_closure h)))]
      exact huf x hx
  intro x hx
  exact ((le_max_left (v x) (u x)).trans_eq (gluedMax_eq_max hx).symm).trans
    (hgreatest w hw hwf x (hV hx))

/-- Off contact with a continuous obstacle, a lower touching function
cannot remain plurisubharmonic after subtracting a positive quadratic. -/
theorem no_strictly_psh_lower_touch_off_contact {f : ComplexModel n → EReal}
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, (u x : EReal) ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, (w x : EReal) ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    {x : ComplexModel n} (hx : x ∈ V) (hV : V ≤ Ω) (hgap : (u x : EReal) < f x)
    (hf : ContinuousAt f x) (hv : ContinuousAt v x)
    (hvu : ∀ y ∈ V, v y ≤ u y) (heq : v x = u x)
    {c : ℝ} (hc : 0 < c) :
    ¬ IsLocallyBoundedPshOn V (fun y => v y - c * ‖y - x‖ ^ 2) := by
  intro hq
  have hvf : (v x : EReal) < f x := heq ▸ hgap
  obtain ⟨a, hax, haf⟩ := EReal.exists_rat_btwn_of_lt hvf
  have hax' : v x < (a : ℝ) := EReal.coe_lt_coe_iff.mp hax
  let d := ((a : ℝ) - v x) / 2
  have hd : 0 < d := half_pos (sub_pos.mpr hax')
  have hlarge : ∀ᶠ y in 𝓝 x, ((a : ℝ) : EReal) < f y :=
    hf.eventually_const_lt haf
  have hsmall : ∀ᶠ y in 𝓝 x, v y < v x + d :=
    hv.eventually_lt_const (lt_add_of_pos_right _ hd)
  have hdom : ∀ᶠ y in 𝓝 x, y ∈ V := V.isOpen.mem_nhds hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hdom.and (hsmall.and hlarge))
  let W : Opens (ComplexModel n) := ⟨ball x r, isOpen_ball⟩
  have hWV : W ≤ V := fun _ hy => (hball hy).1
  let K := ball x (r / 2)
  have hK : closure K ⊆ W :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hr))
  let b := min d (c * (r / 2) ^ 2)
  have hb : 0 < b := lt_min hd (mul_pos hc (pow_pos (half_pos hr) _))
  let w (y : ComplexModel n) := v y - c * ‖y - x‖ ^ 2 + b
  have hw : IsLocallyBoundedPshOn W w :=
    locallyBoundedPsh_add_const (IsLocallyBoundedPshOn.mono hq hWV) b
  have hwf (y : ComplexModel n) (hy : y ∈ W) : (w y : EReal) ≤ f y := by
    have hyb := hball hy
    have hbd : b ≤ d := min_le_left _ _
    have hq0 : 0 ≤ c * ‖y - x‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    have hyl := hyb.2.1
    have hwa : w y ≤ (a : ℝ) := by
      dsimp only [w, d] at hbd hyl ⊢
      linarith
    exact (EReal.coe_le_coe_iff.mpr hwa).trans hyb.2.2.le
  have hwCollar (y : ComplexModel n) (hy : y ∈ (W : Set (ComplexModel n)) \ K) :
      w y ≤ u y := by
    have hdist : r / 2 ≤ ‖y - x‖ := by
      simpa only [K, mem_ball, dist_eq_norm, not_lt] using hy.2
    have hbq : b ≤ c * ‖y - x‖ ^ 2 := (min_le_right _ _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (half_pos hr).le hdist 2) hc.le)
    dsimp [w]
    linarith [hvu y (hWV hy.1)]
  have h := le_of_obstacle_minorant hu huf hgreatest hw (hWV.trans hV) hK hwCollar hwf
    x (mem_ball_self hr)
  simp only [w, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, heq] at h
  linarith

theorem locallyBoundedPsh_comp_holomorphic {k : ℕ}
    {U : Opens (ComplexModel k)} {F : ComplexModel k → ComplexModel n}
    (hu : IsLocallyBoundedPshOn Ω u) (hF : DifferentiableOn ℂ F U) (hmap : MapsTo F U Ω) :
    IsLocallyBoundedPshOn U (fun x => u (F x)) := by
  refine ⟨PshLines.Regularization.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    U.isOpen hF hmap hu.1, ?_⟩
  intro x hx
  obtain ⟨W, hxW, _, C, hC⟩ := hu.2 (F x) (hmap hx)
  have hFcont : ContinuousAt F x := hF.continuousOn.continuousAt (U.isOpen.mem_nhds hx)
  have hFW : ∀ᶠ y in 𝓝 x, F y ∈ W := hFcont (W.isOpen.mem_nhds hxW)
  have hU : ∀ᶠ y in 𝓝 x, y ∈ U := U.isOpen.mem_nhds hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.and hFW)
  exact ⟨⟨ball x r, isOpen_ball⟩, mem_ball_self hr, fun _ hy => (hball hy).1,
    C, fun y hy => hC (F y) (hball hy).2⟩

/-- A PSH correction to the sum of two holomorphic translates of the
obstacle gives the same correction for its envelope. -/
theorem obstacleEnvelope_centered_difference_of_psh_correction
    {f b : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, u x ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, w x ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    {F G : ComplexModel n → ComplexModel n} (hF : DifferentiableOn ℂ F Ω)
    (hG : DifferentiableOn ℂ G Ω) (hFmap : MapsTo F Ω Ω) (hGmap : MapsTo G Ω Ω)
    (hb : IsLocallyBoundedPshOn Ω b)
    (hf : ∀ x ∈ Ω, f (F x) + f (G x) - 2 * f x ≤ -b x) :
    ∀ x ∈ Ω, u (F x) + u (G x) - 2 * u x ≤ -b x := by
  let w (x : ComplexModel n) := (1 / 2 : ℝ) * (u (F x) + u (G x) + b x)
  have hw : IsLocallyBoundedPshOn Ω w :=
    locallyBoundedPsh_const_mul
      (locallyBoundedPsh_add
        (locallyBoundedPsh_add (locallyBoundedPsh_comp_holomorphic hu hF hFmap)
          (locallyBoundedPsh_comp_holomorphic hu hG hGmap)) hb) (by norm_num)
  have hwf (x : ComplexModel n) (hx : x ∈ Ω) : w x ≤ f x := by
    dsimp [w]
    linarith [huf (F x) (hFmap hx), huf (G x) (hGmap hx), hf x hx]
  intro x hx
  have h := hgreatest w hw hwf x hx
  dsimp [w] at h
  linarith

/-- A centered difference bound on a real obstacle along two holomorphic
self-maps passes to its plurisubharmonic envelope. -/
theorem obstacleEnvelope_centered_difference {f : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, u x ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, w x ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    {F G : ComplexModel n → ComplexModel n} (hF : DifferentiableOn ℂ F Ω)
    (hG : DifferentiableOn ℂ G Ω) (hFmap : MapsTo F Ω Ω) (hGmap : MapsTo G Ω Ω)
    {C : ℝ} (hf : ∀ x ∈ Ω, f (F x) + f (G x) - 2 * f x ≤ C) :
    ∀ x ∈ Ω, u (F x) + u (G x) - 2 * u x ≤ C := by
  simpa only [neg_neg] using
    obstacleEnvelope_centered_difference_of_psh_correction hu huf hgreatest hF hG hFmap hGmap
      (locallyBoundedPsh_const (-C)) (fun x hx => by simpa only [neg_neg] using hf x hx)

end KEBall.BedfordTaylor
