import KEBall.BedfordTaylorObstacleQuadraticSupport
import KEBall.ComplexProductBall

/-!
# Centered second differences of a PSH envelope on a product ball
-/

set_option autoImplicit false

open Set

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- An obstacle with bounded quadratic upper supports gives a uniform
centered second difference bound for its envelope on smaller product balls. -/
theorem exists_obstacleEnvelope_centered_difference_bound_product
    {n m : ℕ} {u f : ComplexModel (n + m) → ℝ} {r δ C₀ L₀ : ℝ}
    (hδ : 0 ≤ δ) (hrδ : r + δ < 1) (hC₀ : 0 ≤ C₀) (hL₀ : 0 ≤ L₀)
    (hu : IsLocallyBoundedPshOn (complexProductBall n m) u)
    (huf : ∀ x ∈ complexProductBall n m, u x ≤ f x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ f x) → ∀ x ∈ complexProductBall n m, w x ≤ u x)
    (hf : ∀ x ∈ complexProductBall n m, ∃ p : ComplexModel (n + m) →L[ℝ] ℝ, ‖p‖ ≤ L₀ ∧
      ∀ y ∈ complexProductBall n m, f y ≤ f x + p (y - x) + C₀ * ‖y - x‖ ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ a : ComplexModel (n + m), ‖(complexProductCoordinates n m a).1‖ ≤ r →
        ‖(complexProductCoordinates n m a).2‖ ≤ r →
      ∀ h : ComplexModel (n + m), ‖h‖ ≤ δ →
        u (a + h) + u (a - h) - 2 * u a ≤ A * ‖h‖ ^ 2 := by
  obtain ⟨C, L, hC, hL, hdisp⟩ := exists_complexProductBallMove_displacement n m hδ hrδ
  refine ⟨L₀ * C + C₀ * (2 * L ^ 2), by positivity, ?_⟩
  intro a ha₁ ha₂ h hh
  have ha : a ∈ complexProductBall n m := mem_complexProductBall.mpr
    ⟨by linarith, by linarith⟩
  have hshift (k : ComplexModel (n + m)) (hk : ‖k‖ ≤ δ) :
      a + k ∈ complexProductBall n m := by
    apply mem_complexProductBall.mpr
    rw [map_add, Prod.fst_add, Prod.snd_add]
    exact ⟨((norm_add_le _ _).trans (add_le_add ha₁
      ((norm_fst_complexProductCoordinates_le k).trans hk))).trans_lt hrδ,
      ((norm_add_le _ _).trans (add_le_add ha₂
        ((norm_snd_complexProductCoordinates_le k).trans hk))).trans_lt hrδ⟩
  have hnh : ‖-h‖ ≤ δ := by simpa only [norm_neg] using hh
  let F := complexProductBallMove (n := n) (m := m) a h
  let G := complexProductBallMove (n := n) (m := m) a (-h)
  have hF := differentiableOn_complexProductBallMove ha (hshift h hh)
  have hG := differentiableOn_complexProductBallMove ha (hshift (-h) hnh)
  have hFmap := complexProductBallMove_mapsTo ha (hshift h hh)
  have hGmap := complexProductBallMove_mapsTo ha (hshift (-h) hnh)
  have hquad (z : ComplexModel (n + m)) (hz : z ∈ complexProductBall n m) :
      ‖F z - z‖ ^ 2 + ‖G z - z‖ ^ 2 ≤ (2 * L ^ 2) * ‖h‖ ^ 2 := by
    have hF' : ‖F z - z‖ ≤ L * ‖h‖ := (hdisp a ha₁ ha₂ h hh z hz).1
    have hG' : ‖G z - z‖ ≤ L * ‖h‖ := by
      simpa only [norm_neg] using (hdisp a ha₁ ha₂ (-h) hnh z hz).1
    calc
      _ ≤ (L * ‖h‖) ^ 2 + (L * ‖h‖) ^ 2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) hF' 2) (pow_le_pow_left₀ (norm_nonneg _) hG' 2)
      _ = _ := by ring
  have hdiff := obstacleEnvelope_centered_difference_of_quadratic_support hC₀ hL₀ hu huf hgreatest hf
    hF hG hFmap hGmap hquad (fun z hz => (hdisp a ha₁ ha₂ h hh z hz).2) a ha
  rw [complexProductBallMove_at_center ha (hshift h hh),
    complexProductBallMove_at_center ha (hshift (-h) hnh), ← sub_eq_add_neg] at hdiff
  exact hdiff.trans_eq (by ring)

end KEBall.BedfordTaylor
