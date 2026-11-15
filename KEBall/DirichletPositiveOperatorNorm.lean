import Mathlib.Analysis.InnerProductSpace.Dual

/-! An operator-norm estimate from a nonnegative symmetric quadratic form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

theorem norm_le_of_symmetric_nonneg_quadratic_bound (A : V →L[ℝ] V)
    (hSym : ∀ v w : V, inner ℝ (A v) w = inner ℝ (A w) v)
    {C : ℝ} (hC : 0 ≤ C)
    (hNonneg : ∀ v : V, 0 ≤ inner ℝ (A v) v)
    (hUpper : ∀ v : V, inner ℝ (A v) v ≤ C * ‖v‖ ^ 2) :
    ‖A‖ ≤ C := by
  have hPair (v w : V) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : inner ℝ (A v) w ≤ C := by
    have hnorm : ‖v + w‖ ≤ 2 := by
      calc
        _ ≤ ‖v‖ + ‖w‖ := norm_add_le _ _
        _ = 2 := by rw [hv, hw]; norm_num
    have hsquare : ‖v + w‖ ^ 2 ≤ 4 := by nlinarith only [hnorm, norm_nonneg (v + w)]
    have hp := (hUpper (v + w)).trans (mul_le_mul_of_nonneg_left hsquare hC)
    have hm := hNonneg (v - w)
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right] at hp hm
    rw [hSym w v] at hp hm
    nlinarith only [hp, hm]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro v hv
  rw [← (InnerProductSpace.toDual ℝ V).norm_map (A v)]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro w hw
  change ‖inner ℝ (A v) w‖ ≤ C
  rw [Real.norm_eq_abs, abs_le]
  have hneg := hPair v (-w) hv (by simpa only [norm_neg] using hw)
  rw [inner_neg_right] at hneg
  exact ⟨by linarith only [hneg], hPair v w hv hw⟩

end KEBall
