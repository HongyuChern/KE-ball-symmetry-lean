import Drafts.KEBall.WirtingerConjugation
import Drafts.KEBall.AuxiliaryPPositivity

/-!
Stage09 SOURCE_DRAFT_UNCOMPILED.
Dirichlet uniqueness for actual CR functions in the fixed real coordinate model.
The proof uses the already derived local maximum sign and the actual solution
as a strict barrier, since L_u u = n. No global maximum principle is postulated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall

theorem mem_unitBall_of_pos_and_boundary_nonpos {n : ℕ} {h : E n → ℝ}
    (hb : ∀ y ∈ unitSphere n, h y ≤ 0) {x : E n}
    (hx : x ∈ closedUnitBall n) (hpos : 0 < h x) : x ∈ unitBall n := by
  by_contra hnot
  have hn : ‖x‖ ≤ 1 := by
    simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
  have hn' : ¬ ‖x‖ < 1 := by
    simpa [unitBall, Metric.mem_ball, dist_zero_right] using hnot
  have hs : x ∈ unitSphere n := by
    simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using
      le_antisymm hn (le_of_not_gt hn')
  exact (not_le_of_gt hpos) (hb x hs)

theorem IsSolution.strict_subharmonic_nonpos_closedBall {n : ℕ}
    {μ : ℝ} {u h : E n → ℝ} (hu : IsSolution n μ u)
    (hc : ContinuousOn h (closedUnitBall n))
    (hs : ContDiffOn ℝ ∞ h (unitBall n))
    (hL : ∀ x ∈ unitBall n, 0 < complexLaplacian u h x)
    (hb : ∀ x ∈ unitSphere n, h x ≤ 0) :
    ∀ x ∈ closedUnitBall n, h x ≤ 0 := by
  intro p hp
  by_contra hnot
  have hpos : 0 < h p := lt_of_not_ge hnot
  have hne : (closedUnitBall n).Nonempty := ⟨0, by simp [closedUnitBall]⟩
  obtain ⟨q, hq, hmaxOn⟩ :=
    (isCompact_closedBall (0 : E n) 1).exists_isMaxOn hne hc
  have hqi := mem_unitBall_of_pos_and_boundary_nonpos hb hq (hpos.trans_le (hmaxOn hp))
  have hmax : IsLocalMax h q := hmaxOn.isLocalMax
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hqi) Metric.ball_subset_closedBall)
  have hnonpos := complexLaplacian_nonpos_of_isLocalMax (hu.2.2.1 q hqi)
    (hs.contDiffAt (Metric.isOpen_ball.mem_nhds hqi)) hmax
  exact (not_le_of_gt (hL q hqi)) hnonpos

/-- The perturbation coefficient is explicitly chosen at a hypothetical
positive point. Its strict positivity follows from u<0 in the ball. -/
theorem IsSolution.subharmonic_nonpos_closedBall {n : ℕ} (hn : 0 < n)
    {μ : ℝ} {u h : E n → ℝ} (hu : IsSolution n μ u)
    (hc : ContinuousOn h (closedUnitBall n))
    (hs : ContDiffOn ℝ ∞ h (unitBall n))
    (hL : ∀ x ∈ unitBall n, 0 ≤ complexLaplacian u h x)
    (hb : ∀ x ∈ unitSphere n, h x ≤ 0) :
    ∀ x ∈ closedUnitBall n, h x ≤ 0 := by
  intro p hp
  by_contra hnot
  have hpos : 0 < h p := lt_of_not_ge hnot
  have hpi := mem_unitBall_of_pos_and_boundary_nonpos hb hp hpos
  have hup := hu.neg_unitBall hn hpi
  let c : ℝ := h p / (-2 * u p)
  have hcpos : 0 < c := div_pos hpos (by nlinarith)
  let f : E n → ℝ := fun y => h y - (-c) * u y
  have huCont : ContinuousOn u (closedUnitBall n) :=
    fun y hy => (hu.2.1.contDiffAt hy).continuousAt.continuousWithinAt
  have huSmooth : ContDiffOn ℝ ∞ u (unitBall n) :=
    fun y hy => (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hy)).contDiffWithinAt
  have hfCont : ContinuousOn f (closedUnitBall n) := hc.sub (continuousOn_const.mul huCont)
  have hfSmooth : ContDiffOn ℝ ∞ f (unitBall n) := hs.sub (contDiffOn_const.mul huSmooth)
  have hfLap (y : E n) (hy : y ∈ unitBall n) : 0 < complexLaplacian u f y := by
    have hhAt := hs.contDiffAt (Metric.isOpen_ball.mem_nhds hy)
    have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hy)
    change 0 < complexLaplacian u (fun z => h z - (-c) * u z) y
    rw [complexLaplacian_sub_at u hhAt (contDiffAt_const.mul huAt),
      complexLaplacian_const_mul_at u huAt,
      hu.complexLaplacian_self (Metric.ball_subset_closedBall hy)]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hprod := mul_pos hcpos hnR
    nlinarith [hL y hy]
  have hfBoundary (y : E n) (hy : y ∈ unitSphere n) : f y ≤ 0 := by
    simpa [f, hu.2.2.2.2 y hy] using hb y hy
  have hfnonpos := hu.strict_subharmonic_nonpos_closedBall hfCont hfSmooth hfLap hfBoundary p hp
  have hfp : f p = h p / 2 := by
    dsimp [f, c]
    field_simp [ne_of_lt hup]
    <;> ring
  rw [hfp] at hfnonpos
  linarith

theorem IsSolution.harmonic_zero_boundary {n : ℕ} (hn : 0 < n)
    {μ : ℝ} {u h : E n → ℝ} (hu : IsSolution n μ u)
    (hc : ContinuousOn h (closedUnitBall n))
    (hs : ContDiffOn ℝ ∞ h (unitBall n))
    (hL : ∀ x ∈ unitBall n, complexLaplacian u h x = 0)
    (hb : ∀ x ∈ unitSphere n, h x = 0) :
    ∀ x ∈ closedUnitBall n, h x = 0 := by
  have hupper := hu.subharmonic_nonpos_closedBall hn hc hs
    (fun x hx => (hL x hx).ge) (fun x hx => (hb x hx).le)
  have hlower := hu.subharmonic_nonpos_closedBall hn
    (continuousOn_const.mul hc : ContinuousOn (fun x => (-1 : ℝ) * h x) (closedUnitBall n))
    (contDiffOn_const.mul hs : ContDiffOn ℝ ∞ (fun x => (-1 : ℝ) * h x) (unitBall n))
    (by
      intro x hx
      change 0 ≤ complexLaplacian u (fun y => (-1 : ℝ) * h y) x
      rw [complexLaplacian_const_mul_at u (hs.contDiffAt (Metric.isOpen_ball.mem_nhds hx)), hL x hx]
      norm_num)
    (by intro x hx; change (-1 : ℝ) * h x ≤ 0; rw [hb x hx]; norm_num)
  intro x hx
  have hupp := hupper x hx
  have hlow := hlower x hx
  change (-1 : ℝ) * h x ≤ 0 at hlow
  linarith

/-- Zero-boundary uniqueness for CR functions, proved via their actual real
and imaginary parts. It does not assume a complex maximum modulus theorem. -/
theorem IsSolution.CR_zero_boundary {n : ℕ} (hn : 0 < n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {f : E n → ℂ}
    (hc : ContinuousOn f (closedUnitBall n))
    (hs : ContDiffOn ℝ ∞ f (unitBall n))
    (hCR : ∀ x ∈ unitBall n, ∀ j : Fin n, partialBar j f x = 0)
    (hb : ∀ x ∈ unitSphere n, f x = 0) :
    ∀ x ∈ closedUnitBall n, f x = 0 := by
  have hR := hu.harmonic_zero_boundary hn
    (Complex.reCLM.continuous.comp_continuousOn hc)
    (Complex.reCLM.contDiff.comp_contDiffOn hs)
    (by
      intro x hx
      change complexLaplacian u (fun y => (f y).re) x = 0
      rw [complexLaplacian_eq_trace, complexHessian_re_eq_zero_of_CR Metric.isOpen_ball hs hCR hx]
      simp)
    (by intro x hx; simp [hb x hx])
  have hI := hu.harmonic_zero_boundary hn
    (Complex.imCLM.continuous.comp_continuousOn hc)
    (Complex.imCLM.contDiff.comp_contDiffOn hs)
    (by
      intro x hx
      change complexLaplacian u (fun y => (f y).im) x = 0
      rw [complexLaplacian_eq_trace, complexHessian_im_eq_zero_of_CR Metric.isOpen_ball hs hCR hx]
      simp)
    (by intro x hx; simp [hb x hx])
  intro x hx
  apply Complex.ext
  · exact hR x hx
  · exact hI x hx

#print axioms IsSolution.CR_zero_boundary

end KEBall
