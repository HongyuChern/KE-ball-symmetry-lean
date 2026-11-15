import KEBall.DirichletTangentQuotient

/-! Explicit constants for the tangent-annulus boundary improvement. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

namespace KEBall

noncomputable def dirichletBoundaryBarrierScale (n : ℕ) (c K : ℝ) : ℝ :=
  1 + 1024 * (2 * n : ℝ) * K / c

noncomputable def dirichletBoundaryGain (H τ : ℝ) : ℝ :=
  τ * Real.exp (-τ) / (8 * H)

noncomputable def dirichletBoundaryLoss (n : ℕ) (c τ : ℝ) : ℝ :=
  (τ * Real.exp (-τ) / 4 + 4) / (4 * n * c)

theorem dirichletBoundaryBarrierScale_pos (n : ℕ) {c K : ℝ}
    (hc : 0 < c) (hK : 0 ≤ K) : 0 < dirichletBoundaryBarrierScale n c K := by
  unfold dirichletBoundaryBarrierScale
  positivity

theorem dirichletBoundaryGain_pos {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ) :
    0 < dirichletBoundaryGain H τ := by
  unfold dirichletBoundaryGain
  positivity

theorem dirichletBoundaryLoss_nonneg (n : ℕ) {c τ : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) :
    0 ≤ dirichletBoundaryLoss n c τ := by
  unfold dirichletBoundaryLoss
  positivity

theorem dirichletBoundaryBarrierScale_elliptic {n : ℕ} {c K R : ℝ}
    (hc : 0 < c) (hR : 0 < R) :
    (2 * n : ℝ) * K ≤
      (dirichletBoundaryBarrierScale n c K / R ^ 2) * c * (R / 32) ^ 2 := by
  have he : (dirichletBoundaryBarrierScale n c K / R ^ 2) * c * (R / 32) ^ 2 =
      c / 1024 + (2 * n : ℝ) * K := by
    unfold dirichletBoundaryBarrierScale
    field_simp [hR.ne', hc.ne']
    <;> ring
  rw [he]
  linarith

theorem dirichlet_source_coefficient_scale {n : ℕ} (hn : 0 < n) {c S : ℝ}
    (hc : 0 < c) : 2 * (S / (4 * n * c)) * (2 * n : ℝ) * c = S := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0, hc.ne']
  <;> ring

theorem dirichlet_boundary_gain_from_inner_lower {n : ℕ} (hn : 0 < n)
    {c H τ R S ω m : ℝ} (hc : 0 < c) (hH : 0 < H) (hτ : 0 < τ) (hR : 0 < R)
    (hm : ω * R / (8 * H) - (S / (4 * n * c)) * R ^ 2 / 4 ≤ m) :
    dirichletBoundaryGain H τ * ω - dirichletBoundaryLoss n c τ * S * R ≤
      m * (τ / R ^ 2) * R * Real.exp (-(τ / R ^ 2) * R ^ 2) -
        4 * (S / (4 * n * c)) * R := by
  have he : -(τ / R ^ 2) * R ^ 2 = -τ := by field_simp
  rw [he]
  have h := mul_le_mul_of_nonneg_right hm
    (by positivity : 0 ≤ (τ / R ^ 2) * R * Real.exp (-τ))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hid :
      (ω * R / (8 * H) - (S / (4 * n * c)) * R ^ 2 / 4) *
        ((τ / R ^ 2) * R * Real.exp (-τ)) - 4 * (S / (4 * n * c)) * R =
      dirichletBoundaryGain H τ * ω - dirichletBoundaryLoss n c τ * S * R := by
    unfold dirichletBoundaryGain dirichletBoundaryLoss
    field_simp [hn0, hc.ne', hH.ne', hR.ne']
    <;> ring
  rw [← hid]
  nlinarith only [h]

end KEBall
