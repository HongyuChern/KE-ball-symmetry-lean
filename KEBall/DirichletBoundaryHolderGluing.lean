import KEBall.DirichletBoundaryQuotientBound
import KEBall.DirichletBoundaryInterpolation

/-!
# Gluing a boundary power estimate to an interior scaled Holder estimate

The conclusion is a genuine two-point estimate on the closed ball.  The
interior coefficient may grow as the inverse power of the distance to the
sphere.  A nearest-point boundary estimate compensates for that growth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Metric Set
open scoped NNReal

namespace KEBall

theorem exists_dirichlet_closedBall_holder_of_boundary_power {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] {f : E n → F}
    {B C H K α β η : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hη : 0 < η)
    (hBound : ∀ x ∈ closedUnitBall n, ‖f x‖ ≤ B)
    (hBoundary : ∀ p ∈ unitSphere n, ∀ q ∈ unitSphere n,
      ‖f p - f q‖ ≤ K * dist p q ^ α)
    (hApproach : ∀ x ∈ closedUnitBall n, 1 - ‖x‖ ≤ 1 / 2 →
      ∀ p ∈ unitSphere n, dist x p = 1 - ‖x‖ →
        ‖f x - f p‖ ≤ C * (1 - ‖x‖) ^ η)
    (hInterior : ∀ x ∈ unitBall n, ∀ y ∈ ball x ((1 - ‖x‖) / 8),
      ‖f x - f y‖ ≤ (H / (1 - ‖x‖) ^ β) * dist x y ^ β) :
    ∃ θ : ℝ≥0, (θ : ℝ) = min η (min α β) / 2 ∧ 0 < θ ∧ θ < 1 ∧ ∃ M : ℝ≥0,
      HolderOnWith M θ f (closedUnitBall n) := by
  let θ : ℝ := min η (min α β) / 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθη : θ ≤ η / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hθα : θ ≤ α / 2 := div_le_div_of_nonneg_right
    ((min_le_right η (min α β)).trans (min_le_left α β)) (by norm_num)
  have hθβ : θ ≤ β / 2 := div_le_div_of_nonneg_right
    ((min_le_right η (min α β)).trans (min_le_right α β)) (by norm_num)
  let D : ℝ := C * ((8 : ℝ) ^ η + (9 : ℝ) ^ η) + K * (18 : ℝ) ^ α
  let M : ℝ := H + D + 2 * B / (1 / 1024 : ℝ) ^ θ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hFarCoeff : 0 ≤ 2 * B / (1 / 1024 : ℝ) ^ θ := by positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨⟨θ, hθ.le⟩, rfl, hθ, (show θ < 1 by linarith), ⟨M, hM⟩,
    dirichlet_holderOnWith_of_norm_bound hM hθ.le ?_⟩
  intro x hx y hy
  conv_rhs => rw [← dist_eq_norm]
  by_cases he : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self]
    positivity
  let d : ℝ := dist x y
  have hd : 0 < d := dist_pos.mpr he
  have hnorm : ‖f x - f y‖ ≤ 2 * B := by
    exact (norm_sub_le _ _).trans (by linarith [hBound x hx, hBound y hy])
  by_cases hsmall : d ≤ 1 / 1024
  · have hd1 : d ≤ 1 := by linarith
    let s : ℝ := Real.sqrt d
    have hs : 0 < s := Real.sqrt_pos.2 hd
    have hs2 : s ^ 2 = d := Real.sq_sqrt hd.le
    have hsSmall : s ≤ 1 / 32 := by
      have := Real.sqrt_nonneg d
      nlinarith
    have hds : d < s := by nlinarith
    have hsPow (a : ℝ) : s ^ a = d ^ (a / 2) := by
      dsimp [s]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd.le]
      congr 1
      ring
    have hPower (a : ℝ) (ha : θ ≤ a / 2) : s ^ a ≤ d ^ θ := by
      rw [hsPow]
      exact Real.rpow_le_rpow_of_exponent_ge hd hd1 ha
    by_cases hNear : 1 - ‖x‖ ≤ 8 * s
    · obtain ⟨p, hp, hxp⟩ := exists_dirichlet_nearest_sphere_point hn hx
      obtain ⟨q, hq, hyq⟩ := exists_dirichlet_nearest_sphere_point hn hy
      have hDy : 1 - ‖y‖ ≤ 9 * s := by
        have h := norm_sub_norm_le x y
        rw [← dist_eq_norm] at h
        change ‖x‖ - ‖y‖ ≤ d at h
        linarith
      have hDx0 : 0 ≤ 1 - ‖x‖ := sub_nonneg.mpr (mem_closedBall_zero_iff.mp hx)
      have hDy0 : 0 ≤ 1 - ‖y‖ := sub_nonneg.mpr (mem_closedBall_zero_iff.mp hy)
      have hpq : dist p q ≤ 18 * s := by
        have ht₁ := dist_triangle p x q
        have ht₂ := dist_triangle x y q
        rw [dist_comm p x, hxp] at ht₁
        rw [hyq] at ht₂
        change dist x q ≤ d + (1 - ‖y‖) at ht₂
        linarith
      have hEx : ‖f x - f p‖ ≤ (C * (8 : ℝ) ^ η) * d ^ θ := by
        calc
          _ ≤ C * (1 - ‖x‖) ^ η := hApproach x hx (by linarith) p hp hxp
          _ ≤ C * (8 * s) ^ η := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hDx0 hNear hη.le) hC
          _ = (C * (8 : ℝ) ^ η) * s ^ η := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hs.le]
            ring
          _ ≤ (C * (8 : ℝ) ^ η) * d ^ θ :=
            mul_le_mul_of_nonneg_left (hPower η hθη) (by positivity)
      have hEy : ‖f y - f q‖ ≤ (C * (9 : ℝ) ^ η) * d ^ θ := by
        calc
          _ ≤ C * (1 - ‖y‖) ^ η := hApproach y hy (by linarith) q hq hyq
          _ ≤ C * (9 * s) ^ η := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hDy0 hDy hη.le) hC
          _ = (C * (9 : ℝ) ^ η) * s ^ η := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) hs.le]
            ring
          _ ≤ (C * (9 : ℝ) ^ η) * d ^ θ :=
            mul_le_mul_of_nonneg_left (hPower η hθη) (by positivity)
      have hEpq : ‖f p - f q‖ ≤ (K * (18 : ℝ) ^ α) * d ^ θ := by
        calc
          _ ≤ K * dist p q ^ α := hBoundary p hp q hq
          _ ≤ K * (18 * s) ^ α := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hpq hα.le) hK
          _ = (K * (18 : ℝ) ^ α) * s ^ α := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 18) hs.le]
            ring
          _ ≤ (K * (18 : ℝ) ^ α) * d ^ θ :=
            mul_le_mul_of_nonneg_left (hPower α hθα) (by positivity)
      have hsum : ‖f x - f y‖ ≤ D * d ^ θ := by
        have ht₁ := norm_sub_le_norm_sub_add_norm_sub (f x) (f p) (f y)
        have ht₂ := norm_sub_le_norm_sub_add_norm_sub (f p) (f q) (f y)
        rw [norm_sub_rev (f q) (f y)] at ht₂
        dsimp [D]
        nlinarith only [ht₁, ht₂, hEx, hEy, hEpq]
      exact hsum.trans (mul_le_mul_of_nonneg_right
        (by dsimp [M]; linarith : D ≤ M) (Real.rpow_nonneg hd.le _))
    · have hAway : 8 * s < 1 - ‖x‖ := lt_of_not_ge hNear
      have hxOpen : x ∈ unitBall n := mem_ball_zero_iff.mpr (by linarith)
      have hyLocal : y ∈ ball x ((1 - ‖x‖) / 8) := by
        rw [mem_ball, dist_comm y x]
        change d < (1 - ‖x‖) / 8
        linarith
      have hr : 0 < 1 - ‖x‖ := by linarith
      have hDiv : (H / (1 - ‖x‖) ^ β) * d ^ β ≤ H * d ^ (β / 2) := by
        have hPowLe : s ^ β ≤ (1 - ‖x‖) ^ β :=
          Real.rpow_le_rpow hs.le (by linarith) hβ.le
        calc
          _ ≤ (H / s ^ β) * d ^ β :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hH
              (Real.rpow_pos_of_pos hs _) hPowLe) (Real.rpow_nonneg hd.le _)
          _ = H * d ^ (β / 2) := by
            rw [hsPow]
            have hp : d ^ β = d ^ (β / 2) * d ^ (β / 2) := by
              rw [← Real.rpow_add hd]
              congr 1
              ring
            rw [hp]
            field_simp [(Real.rpow_pos_of_pos hd (β / 2)).ne']
      have hEst : ‖f x - f y‖ ≤ H * d ^ θ :=
        (hInterior x hxOpen y hyLocal).trans (hDiv.trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hd hd1 hθβ) hH))
      exact hEst.trans (mul_le_mul_of_nonneg_right
        (by dsimp [M]; linarith : H ≤ M) (Real.rpow_nonneg hd.le _))
  · have hFar : 1 / 1024 ≤ d := le_of_lt (lt_of_not_ge hsmall)
    have hPow : (1 / 1024 : ℝ) ^ θ ≤ d ^ θ :=
      Real.rpow_le_rpow (by norm_num) hFar hθ.le
    have hCoeff : 2 * B ≤ (2 * B / (1 / 1024 : ℝ) ^ θ) * d ^ θ := by
      calc
        _ = (2 * B / (1 / 1024 : ℝ) ^ θ) * (1 / 1024 : ℝ) ^ θ := by
          field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 1024) θ).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left hPow (by positivity)
    exact hnorm.trans (hCoeff.trans (mul_le_mul_of_nonneg_right
      (by dsimp [M]; linarith : 2 * B / (1 / 1024 : ℝ) ^ θ ≤ M)
      (Real.rpow_nonneg hd.le _)))

end KEBall
