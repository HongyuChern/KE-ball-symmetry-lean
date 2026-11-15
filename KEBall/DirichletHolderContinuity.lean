import KEBall.Domain
import Mathlib.Topology.MetricSpace.Holder

/-! A real-valued power modulus gives continuity on the same set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped NNReal ENNReal

namespace KEBall

theorem continuousOn_of_dirichlet_holder_bound {n : ℕ}
    {q : E n → ℝ} {s : Set (E n)} {α C : ℝ} (hα : 0 < α)
    (h : ∀ x ∈ s, ∀ y ∈ s, |q x - q y| ≤ C * ‖x - y‖ ^ α) :
    ContinuousOn q s := by
  let a : ℝ≥0 := ⟨α, hα.le⟩
  let c : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hc : 0 ≤ max C 0 := le_max_right _ _
  have hHolder : HolderOnWith c a q s := by
    intro x hx y hy
    have hd : dist (q x) (q y) ≤ (max C 0) * dist x y ^ α := by
      rw [Real.dist_eq, dist_eq_norm]
      exact (h x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (norm_nonneg _) _))
    have he := ENNReal.ofReal_le_ofReal hd
    rw [ENNReal.ofReal_mul hc, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le] at he
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (q x) (q y)) ≤
      (c : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ α
    simpa only [c, ENNReal.ofReal_eq_coe_nnreal hc, NNReal.mk] using he
  exact hHolder.continuousOn (show 0 < a from hα)

end KEBall
