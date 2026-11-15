import KEBall.BedfordTaylorSmoothObstacle
import KEBall.ComplexProductBall

/-!
# Base differences of a product envelope near the fiber boundary
-/

set_option autoImplicit false

open Metric Set TopologicalSpace
open scoped ContDiff

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn isSmoothPshOn_norm_sq)

private theorem norm_eq_norm_snd_of_fst_eq_zero {n m : ℕ}
    {x : ComplexModel (n + m)} (hx : (complexProductCoordinates n m x).1 = 0) :
    ‖x‖ = ‖(complexProductCoordinates n m x).2‖ := by
  apply le_antisymm _ (norm_snd_complexProductCoordinates_le (n := n) (m := m) x)
  simpa only [hx, norm_zero, zero_add] using norm_le_complexProductCoordinates (n := n) (m := m) x

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Moving only the base coordinate gives a second difference bound
proportional to the quadratic defining function of the fiber ball. -/
theorem exists_productEnvelope_base_difference_le {n m : ℕ} {R r δ : ℝ}
    (hR : 0 < R) (hR₁ : R < 1) (hδ : 0 ≤ δ) (hrδ : r + δ < 1)
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a ∈ complexProductBall n m,
      ‖(complexProductCoordinates n m a).2‖ ≤ r →
      ∀ h : ComplexModel (n + m), (complexProductCoordinates n m h).1 = 0 → ‖h‖ ≤ δ →
        v (a + h) + v (a - h) - 2 * v a ≤
          A * ‖h‖ ^ 2 * (1 - ‖(complexProductCoordinates n m a).1‖ ^ 2) := by
  let P := complexProductBall n m
  let e := complexProductCoordinates n m
  let f := (ball (0 : ComplexModel (n + m)) R).indicator u
  let ρ (x : ComplexModel (n + m)) := ‖(e x).1‖ ^ 2 - 1
  let η := 1 - R ^ 2
  have hη : 0 < η := by dsimp [η]; nlinarith only [hR, hR₁]
  obtain ⟨C₀, L₀, hC₀, hL₀, hf⟩ :=
    exists_quadratic_upper_support_smooth_zeroExtension hu hu₀ huBoundary
  obtain ⟨C, L, hC, hL, hdisp⟩ :=
    exists_complexBallMove_displacement (H := ComplexModel m) hδ hrδ
  let B := L₀ * C + C₀ * (2 * L ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let A := (B + 1) / η
  have hA : 0 < A := div_pos (by linarith) hη
  have hAη : A * η = B + 1 := div_mul_cancel₀ _ hη.ne'
  refine ⟨A, hA.le, ?_⟩
  intro a ha har h hh₁ hh
  by_cases hh₀ : h = 0
  · simp [hh₀]
    ring_nf
    exact le_rfl
  have ha' := mem_complexProductBall.mp ha
  have hshift (k : ComplexModel (n + m)) (hk₁ : (e k).1 = 0) (hk : ‖k‖ ≤ δ) :
      a + k ∈ P := by
    apply mem_complexProductBall.mpr
    rw [map_add, Prod.fst_add, Prod.snd_add, hk₁, add_zero]
    exact ⟨ha'.1, ((norm_add_le _ _).trans (add_le_add har
      ((norm_snd_complexProductCoordinates_le (n := n) (m := m) k).trans hk))).trans_lt hrδ⟩
  have hnh₁ : (e (-h)).1 = 0 := by simp [hh₁, e]
  have hnh : ‖-h‖ ≤ δ := by simpa only [norm_neg] using hh
  let F := complexProductBallMove (n := n) (m := m) a h
  let G := complexProductBallMove (n := n) (m := m) a (-h)
  have hF := differentiableOn_complexProductBallMove ha (hshift h hh₁ hh)
  have hG := differentiableOn_complexProductBallMove ha (hshift (-h) hnh₁ hnh)
  have hFmap := complexProductBallMove_mapsTo ha (hshift h hh₁ hh)
  have hGmap := complexProductBallMove_mapsTo ha (hshift (-h) hnh₁ hnh)
  have hfst (k z : ComplexModel (n + m)) (hk : (e k).1 = 0) (hz : z ∈ P) :
      (e (complexProductBallMove (n := n) (m := m) a k z - z)).1 = 0 := by
    change (complexProductCoordinates n m
      (complexProductBallMove (n := n) (m := m) a k z - z)).1 = 0
    rw [map_sub, Prod.fst_sub, complexProductCoordinates_ballMove,
      show (complexProductCoordinates n m k).1 = 0 from hk,
      complexBallMove_zero_shift ha'.1 (mem_complexProductBall.mp hz).1.le, sub_self]
  have hlin (k z : ComplexModel (n + m)) (hk : (e k).1 = 0) (hkδ : ‖k‖ ≤ δ) (hz : z ∈ P) :
      ‖complexProductBallMove (n := n) (m := m) a k z - z‖ ≤ L * ‖k‖ := by
    rw [norm_eq_norm_snd_of_fst_eq_zero (hfst k z hk hz)]
    simp only [map_sub, Prod.snd_sub, complexProductCoordinates_ballMove]
    have hk₂ : ‖(e k).2‖ ≤ ‖k‖ := norm_snd_complexProductCoordinates_le (n := n) (m := m) k
    have hz₂ : ‖(e z).2‖ ≤ 1 := (mem_complexProductBall.mp hz).2.le
    have he : ‖complexBallMove (e a).2 (e k).2 (e z).2 - (e z).2‖ ≤ L * ‖k‖ :=
      ((hdisp (e a).2 har (e k).2 (hk₂.trans hkδ) (e z).2 hz₂).1).trans
        (mul_le_mul_of_nonneg_left hk₂ hL)
    simpa only [e] using he
  have hquad (z : ComplexModel (n + m)) (hz : z ∈ P) :
      ‖F z - z‖ ^ 2 + ‖G z - z‖ ^ 2 ≤ (2 * L ^ 2) * ‖h‖ ^ 2 := by
    have hF' := hlin h z hh₁ hh hz
    have hG' := hlin (-h) z hnh₁ hnh hz
    rw [norm_neg] at hG'
    calc
      _ ≤ (L * ‖h‖) ^ 2 + (L * ‖h‖) ^ 2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) hF' 2)
          (pow_le_pow_left₀ (norm_nonneg _) hG' 2)
      _ = _ := by ring
  have hdrift (z : ComplexModel (n + m)) (hz : z ∈ P) :
      ‖(F z - z) + (G z - z)‖ ≤ C * ‖h‖ ^ 2 := by
    have hzero : (e ((F z - z) + (G z - z))).1 = 0 := by
      rw [map_add, Prod.fst_add, hfst h z hh₁ hz, hfst (-h) z hnh₁ hz, add_zero]
    rw [norm_eq_norm_snd_of_fst_eq_zero hzero]
    have hd := (hdisp (e a).2 har (e h).2
      ((norm_snd_complexProductCoordinates_le (n := n) (m := m) h).trans hh) (e z).2
      (mem_complexProductBall.mp hz).2.le).2
    refine le_trans ?_ (b := C * ‖(e h).2‖ ^ 2) ?_
    · simpa only [F, G, e, map_add, map_sub, map_neg, Prod.snd_add, Prod.snd_sub,
        Prod.snd_neg, complexProductCoordinates_ballMove] using hd
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_complexProductCoordinates_le (n := n) (m := m) h) 2) hC
  have hρ : IsLocallyBoundedPshOn P ρ := by
    have hq : IsLocallyBoundedPshOn (⊤ : Opens (ComplexModel n)) (fun z => ‖z‖ ^ 2 - 1) := by
      simpa only [sub_eq_add_neg] using locallyBoundedPsh_add_const
        (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_norm_sq (⊤ : Opens (ComplexModel n)))) (-1)
    exact locallyBoundedPsh_comp_holomorphic hq e.differentiable.differentiableOn.fst (fun _ _ => by simp)
  have hρ₀ (x : ComplexModel (n + m)) (hx : x ∈ P) : ρ x ≤ 0 := by
    have hx' := (mem_complexProductBall.mp hx).1
    dsimp [ρ, e]
    nlinarith only [hx', norm_nonneg (complexProductCoordinates n m x).1]
  have hρB (x : ComplexModel (n + m)) (hx : x ∈ ball 0 R) : ρ x ≤ -η := by
    have hx' : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using hx
    have h := pow_le_pow_left₀ (norm_nonneg (e x).1)
      ((norm_fst_complexProductCoordinates_le (n := n) (m := m) x).trans hx'.le) 2
    dsimp [ρ, η]
    linarith
  have hf₀ (x : ComplexModel (n + m)) : f x ≤ 0 := by
    by_cases hx : x ∈ ball 0 R
    · simpa only [f, indicator_of_mem hx] using hu₀ x hx
    · simp only [f, indicator_of_notMem hx, le_refl]
  have hs : 0 < A * ‖h‖ ^ 2 := mul_pos hA (sq_pos_of_pos (norm_pos_iff.mpr hh₀))
  have hfDiff (z : ComplexModel (n + m)) (hz : z ∈ P) :
      f (F z) + f (G z) - 2 * f z ≤ -(A * ‖h‖ ^ 2 * ρ z) := by
    by_cases hzB : z ∈ ball 0 R
    · obtain ⟨p, hp, hpz⟩ := hf z
      have hd := centered_difference_le_of_quadratic_support hC₀ hL₀
        (f := f) ⟨p, hp, hpz (F z), hpz (G z)⟩ (hquad z hz) (hdrift z hz)
      have h₁ : f (F z) + f (G z) - 2 * f z ≤ B * ‖h‖ ^ 2 :=
        hd.trans_eq (by dsimp [B]; ring)
      have h₂ := mul_le_mul_of_nonneg_left (hρB z hzB) hs.le
      have he : A * ‖h‖ ^ 2 * -η = -(B + 1) * ‖h‖ ^ 2 := by
        rw [show A * ‖h‖ ^ 2 * -η = -(A * η) * ‖h‖ ^ 2 by ring, hAη]
      rw [he] at h₂
      linarith only [h₁, h₂, sq_nonneg ‖h‖]
    · have h₁ : f z = 0 := indicator_of_notMem hzB _
      have h₂ := mul_nonpos_of_nonneg_of_nonpos hs.le (hρ₀ z hz)
      linarith [hf₀ (F z), hf₀ (G z)]
  have hd := obstacleEnvelope_centered_difference_of_psh_correction hv hvf hgreatest
    hF hG hFmap hGmap (locallyBoundedPsh_const_mul hρ hs) hfDiff a ha
  change v (complexProductBallMove (n := n) (m := m) a h a) +
    v (complexProductBallMove (n := n) (m := m) a (-h) a) - 2 * v a ≤
      -(A * ‖h‖ ^ 2 * ρ a) at hd
  rw [complexProductBallMove_at_center ha (hshift h hh₁ hh),
    complexProductBallMove_at_center ha (hshift (-h) hnh₁ hnh), ← sub_eq_add_neg] at hd
  exact hd.trans_eq (by dsimp [ρ, e]; ring)

end KEBall.BedfordTaylor
