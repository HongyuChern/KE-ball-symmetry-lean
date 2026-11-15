import KEBall.Domain
import DifferentialGeometry.Analysis.Schauder.Holder.Interpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Local derivative interpolation at a boundary-dependent scale

The imported interpolation theorem is applied with explicit value and
derivative-modulus bounds.  The final algebra records a scale smaller than
the distance to the boundary and a remainder that tends to zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace KEBall

theorem dirichlet_holderOnWith_of_norm_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {f : E n → F} {s : Set (E n)} {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    HolderOnWith ⟨C, hC⟩ ⟨α, hα⟩ f s := by
  intro x hx y hy
  have hd : dist (f x) (f y) ≤ C * dist x y ^ α := by
    simpa only [dist_eq_norm] using h x hx y hy
  have he := ENNReal.ofReal_le_ofReal hd
  rw [ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα] at he
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist (f x) (f y)) ≤
    ENNReal.ofNNReal ⟨C, hC⟩ * ENNReal.ofReal (dist x y) ^ α
  simpa only [ENNReal.ofReal_eq_coe_nnreal hC, NNReal.mk] using he

theorem norm_dirichlet_fderiv_le_at_scale {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F}
    {x : E n} {r ε M H β : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hε : 0 < ε) (hεr : ε < r)
    (hf : ∀ z ∈ ball x r, DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ H * ‖y - z‖ ^ β)
    (hBound : ∀ z ∈ ball x r, ‖f z‖ ≤ M) :
    ‖fderiv ℝ f x‖ ≤ 2 * M / ε + H * ε ^ β := by
  have hHolder := dirichlet_holderOnWith_of_norm_bound hH hβ hDf
  have hx : x ∈ ball x r := mem_ball_self (hε.trans hεr)
  have hstep (v : E n) (hv : ‖v‖ = 1) : x + ε • v ∈ ball x r := by
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le, hv, mul_one] using hεr
  exact DifferentialGeometry.Analysis.Schauder.norm_fderiv_le_at_scale_on
    (M := ⟨M, hM⟩) (convex_ball x r) hf hHolder hBound hε hx hstep

theorem dirichlet_boundary_interpolation_scale {r α : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hα : 0 ≤ α) :
    0 < r * r ^ (α / 2) / 8 ∧ r * r ^ (α / 2) / 8 ≤ r / 8 := by
  refine ⟨by positivity, ?_⟩
  have hp : r ^ (α / 2) ≤ 1 := Real.rpow_le_one hr.le hr1 (by positivity)
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hr.le hp) (by norm_num)

theorem dirichlet_boundary_interpolation_error_identity {r A H α β : ℝ} (hr : 0 < r) :
    2 * (A * r ^ (1 + α)) / (r * r ^ (α / 2) / 8) +
        (H / r ^ β) * (r * r ^ (α / 2) / 8) ^ β =
      16 * A * r ^ (α / 2) + (H / (8 : ℝ) ^ β) * r ^ (α * β / 2) := by
  have hPow : r ^ (1 + α) = r * (r ^ (α / 2) * r ^ (α / 2)) := by
    calc
      r ^ (1 + α) = r ^ (1 : ℝ) * r ^ (α / 2 + α / 2) := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one, Real.rpow_add hr]
  have hScale : (r * r ^ (α / 2) / 8) ^ β =
      r ^ β * r ^ (α * β / 2) / (8 : ℝ) ^ β := by
    rw [Real.div_rpow (by positivity) (by norm_num),
      Real.mul_rpow hr.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
    congr 2
    ring
  rw [hPow, hScale]
  have hr0 : r ≠ 0 := hr.ne'
  have hpa : r ^ (α / 2) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hpb : r ^ β ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have h8 : (8 : ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [hr0, hpa, hpb, h8]
  <;> ring

theorem tendsto_dirichlet_boundary_interpolation_error {A H α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun r : ℝ => 16 * A * r ^ (α / 2) +
      (H / (8 : ℝ) ^ β) * r ^ (α * β / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hId : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have h1 := (hId.rpow_const_nhds_zero (by positivity : 0 < α / 2)).const_mul (16 * A)
  have h2 := (hId.rpow_const_nhds_zero (by positivity : 0 < α * β / 2)).const_mul
    (H / (8 : ℝ) ^ β)
  simpa only [mul_zero, add_zero] using h1.add h2

end KEBall
