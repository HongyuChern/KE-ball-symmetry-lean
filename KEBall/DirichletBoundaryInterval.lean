import KEBall.DirichletBoundaryCapGeometry

/-! Nested interval refinement after a uniform boundary defect improvement. -/

set_option autoImplicit false

open Metric Set

namespace KEBall

theorem dirichlet_interval_refinement_of_alternative {X : Type*} {s : Set X}
    (hs : s.Nonempty) (q : X → ℝ) {m M δ err : ℝ}
    (hBounds : ∀ x ∈ s, m ≤ q x ∧ q x ≤ M)
    (hAlt : (∀ x ∈ s, δ * (M - m) - err ≤ q x - m) ∨
      (∀ x ∈ s, δ * (M - m) - err ≤ M - q x)) :
    ∃ a b : ℝ, m ≤ a ∧ b ≤ M ∧ a ≤ b ∧
      (∀ x ∈ s, a ≤ q x ∧ q x ≤ b) ∧ b - a ≤ (1 - δ) * (M - m) + err := by
  obtain ⟨x₀, hx₀⟩ := hs
  rcases hAlt with hLo | hHi
  · let a : ℝ := max m (m + δ * (M - m) - err)
    have hNew (x : X) (hx : x ∈ s) : a ≤ q x := by
      apply max_le (hBounds x hx).1
      linarith only [hLo x hx]
    refine ⟨a, M, le_max_left _ _, le_rfl,
      (hNew x₀ hx₀).trans (hBounds x₀ hx₀).2,
      fun x hx => ⟨hNew x hx, (hBounds x hx).2⟩, ?_⟩
    have h := le_max_right m (m + δ * (M - m) - err)
    change M - a ≤ _
    change m + δ * (M - m) - err ≤ a at h
    nlinarith only [h]
  · let b : ℝ := min M (M - (δ * (M - m) - err))
    have hNew (x : X) (hx : x ∈ s) : q x ≤ b := by
      apply le_min (hBounds x hx).2
      linarith only [hHi x hx]
    refine ⟨m, b, le_rfl, min_le_left _ _,
      (hBounds x₀ hx₀).1.trans (hNew x₀ hx₀),
      fun x hx => ⟨(hBounds x hx).1, hNew x hx⟩, ?_⟩
    have h := min_le_right M (M - (δ * (M - m) - err))
    change b - m ≤ _
    change b ≤ M - (δ * (M - m) - err) at h
    nlinarith only [h]

theorem dirichlet_boundary_small_cap_nonempty {n : ℕ} {p : E n}
    (hp : p ∈ unitSphere n) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    (unitBall n ∩ ball p (R / 64)).Nonempty := by
  refine ⟨dirichletTangentBallCenter p (R / 128), ?_, ?_⟩
  · apply mem_ball_zero_iff.mpr
    rw [norm_dirichletTangentBallCenter hp (by linarith : R / 128 ≤ 1)]
    linarith
  · apply mem_ball.mpr
    rw [dist_dirichletTangentBallCenter_self hp (by positivity : 0 ≤ R / 128)]
    linarith

end KEBall
