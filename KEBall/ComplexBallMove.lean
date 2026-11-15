import KEBall.ComplexBallInvolution
import KEBall.SecondOrderMeanValue

/-!
# Holomorphic changes of center and their uniform displacement estimates
-/

set_option autoImplicit false

open Metric Set
open scoped ContDiff

namespace KEBall

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A ball automorphism sending the center parameter to its translate. -/
noncomputable def complexBallMove (a h z : H) : H :=
  complexBallInvolution (a + h) (complexBallInvolution a z)

theorem complexBallMove_mapsTo_unitBall {a h : H} (ha : ‖a‖ < 1) (hah : ‖a + h‖ < 1) :
    MapsTo (complexBallMove a h) (ball 0 1) (ball 0 1) :=
  (complexBallInvolution_mapsTo_unitBall hah).comp (complexBallInvolution_mapsTo_unitBall ha)

theorem differentiableOn_complexBallMove {a h : H} (ha : ‖a‖ < 1) (hah : ‖a + h‖ < 1) :
    DifferentiableOn ℂ (complexBallMove a h) (ball 0 1) :=
  (differentiableOn_complexBallInvolution hah).comp
    (differentiableOn_complexBallInvolution ha) (complexBallInvolution_mapsTo_unitBall ha)

theorem complexBallMove_at_center {a h : H} (ha : ‖a‖ < 1) (hah : ‖a + h‖ < 1) :
    complexBallMove a h a = a + h := by
  rw [complexBallMove, complexBallInvolution_center ha, complexBallInvolution_zero hah]

theorem complexBallMove_zero_shift {a z : H} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    complexBallMove a 0 z = z := by
  simpa only [complexBallMove, add_zero] using complexBallInvolution_involutive ha hz

theorem contDiffAt_complexBallMove [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    {a h z : H} (ha : ‖a‖ < 1) (hah : ‖a + h‖ < 1) (hz : ‖z‖ ≤ 1) :
    ContDiffAt ℝ ∞ (fun p : H × H × H => complexBallMove p.1 p.2.1 p.2.2) (a, h, z) := by
  have hz' : ‖complexBallInvolution a z‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using complexBallInvolution_mapsTo_closedUnitBall ha
      (show z ∈ closedBall 0 1 by simpa only [mem_closedBall, dist_zero_right] using hz)
  have hleft : ContDiffAt ℝ ∞ (fun p : H × H × H => p.1 + p.2.1) (a, h, z) :=
    (contDiff_fst.add (contDiff_fst.comp contDiff_snd)).contDiffAt
  have hfst : ContDiffAt ℝ ∞ (fun p : H × H × H => p.1) (a, h, z) := contDiff_fst.contDiffAt
  have hsnd : ContDiffAt ℝ ∞ (fun p : H × H × H => p.2.2) (a, h, z) :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hright : ContDiffAt ℝ ∞ (fun p : H × H × H => complexBallInvolution p.1 p.2.2) (a, h, z) :=
    (contDiffAt_complexBallInvolution ha hz).comp₂ hfst hsnd
  exact (contDiffAt_complexBallInvolution hah hz').comp₂ hleft hright

/-- On compact center and shift ranges, a change of center has linear
displacement and its opposite shifts have quadratic combined displacement. -/
theorem exists_complexBallMove_displacement [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    [ProperSpace H] {r δ : ℝ} (hδ : 0 ≤ δ) (hrδ : r + δ < 1) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
      ∀ a : H, ‖a‖ ≤ r → ∀ h : H, ‖h‖ ≤ δ → ∀ z : H, ‖z‖ ≤ 1 →
        ‖complexBallMove a h z - z‖ ≤ L * ‖h‖ ∧
        ‖(complexBallMove a h z - z) + (complexBallMove a (-h) z - z)‖ ≤ C * ‖h‖ ^ 2 := by
  let K : Set (H × H × H) := closedBall 0 r ×ˢ (closedBall 0 δ ×ˢ closedBall 0 1)
  let F (p : H × H × H) := complexBallMove p.1 p.2.1 p.2.2
  have hK : IsCompact K := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hconvex : Convex ℝ K := (convex_closedBall _ _).prod
    ((convex_closedBall _ _).prod (convex_closedBall _ _))
  have hlt (a : H) (ha : ‖a‖ ≤ r) : ‖a‖ < 1 := by linarith
  have hF (p : H × H × H) (hp : p ∈ K) : ContDiffAt ℝ 2 F p := by
    have ha : ‖p.1‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hp.1
    have hh : ‖p.2.1‖ ≤ δ := by simpa only [mem_closedBall, dist_zero_right] using hp.2.1
    have hz : ‖p.2.2‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hp.2.2
    have hah : ‖p.1 + p.2.1‖ < 1 :=
      ((norm_add_le _ _).trans (add_le_add ha hh)).trans_lt hrδ
    exact (contDiffAt_complexBallMove (hlt p.1 ha) hah hz).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨C, L, hC, hL, hbound⟩ := exists_uniform_linearization_bounds hK hconvex hF
  refine ⟨2 * C, L + C * δ, by positivity, by positivity, ?_⟩
  intro a ha h hh z hz
  let p : H × H × H := (a, 0, z)
  let q (k : H) : H × H × H := (a, k, z)
  have hq (k : H) (hk : ‖k‖ ≤ δ) : q k ∈ K := ⟨
    by simpa only [mem_closedBall, dist_zero_right] using ha,
    by simpa only [mem_closedBall, dist_zero_right] using hk,
    by simpa only [mem_closedBall, dist_zero_right] using hz⟩
  have hp : p ∈ K := hq 0 (by simpa only [norm_zero] using hδ)
  have hFp : F p = z := complexBallMove_zero_shift (hlt a ha) hz
  let D := fderiv ℝ F p
  have hqsub (k : H) : q k - p = (0, k, 0) := by ext <;> simp [q, p]
  have hqnorm (k : H) : ‖q k - p‖ = ‖k‖ := by
    rw [hqsub]
    simp [Prod.norm_def]
  have hrem (k : H) (hk : ‖k‖ ≤ δ) :
      ‖complexBallMove a k z - z - D (0, k, 0)‖ ≤ C * ‖k‖ ^ 2 := by
    have he := (hbound p hp).2 (q k) (hq k hk)
    rw [hFp, hqnorm, hqsub] at he
    exact he
  have hlin : ‖D (0, h, 0)‖ ≤ L * ‖h‖ := by
    have hb := mul_le_mul_of_nonneg_right (hbound p hp).1 (norm_nonneg h)
    exact (D.le_opNorm (0, h, 0)).trans (by simpa [Prod.norm_def] using hb)
  have hcancel : D (0, -h, 0) = -D (0, h, 0) := by
    rw [show ((0, -h, 0) : H × H × H) = -(0, h, 0) by ext <;> simp, map_neg]
  constructor
  · calc
      ‖complexBallMove a h z - z‖ =
          ‖(complexBallMove a h z - z - D (0, h, 0)) + D (0, h, 0)‖ := by rw [sub_add_cancel]
      _ ≤ C * ‖h‖ ^ 2 + L * ‖h‖ :=
        (norm_add_le _ _).trans (add_le_add (hrem h hh) hlin)
      _ ≤ (L + C * δ) * ‖h‖ := by
        nlinarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg hC (norm_nonneg h))]
  · have hrem' := hrem (-h) (by simpa only [norm_neg] using hh)
    rw [hcancel, norm_neg] at hrem'
    calc
      ‖(complexBallMove a h z - z) + (complexBallMove a (-h) z - z)‖ =
          ‖(complexBallMove a h z - z - D (0, h, 0)) +
            (complexBallMove a (-h) z - z - -D (0, h, 0))‖ := by congr 1; abel
      _ ≤ C * ‖h‖ ^ 2 + C * ‖h‖ ^ 2 :=
        (norm_add_le _ _).trans (add_le_add (hrem h hh) hrem')
      _ = (2 * C) * ‖h‖ ^ 2 := by ring

end KEBall
