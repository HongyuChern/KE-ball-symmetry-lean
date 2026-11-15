import KEBall.DirichletBoundaryOscillation
import KEBall.DirichletBoundaryOscillationPower

/-!
# Uniform all-radius power decay on boundary caps

The constants are chosen before the function, boundary point and initial
radius.  The geometric error at ratio 1/256 is bounded by the previously
verified quarter-scale geometric budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Metric Set

namespace KEBall

theorem exists_dirichlet_boundary_power_decay_budget {n : ℕ}
    {θ C B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ (f : E n → ℝ), (∀ x ∈ unitBall n, |f x| ≤ B) →
        (∀ p ∈ unitSphere n, ∀ R : ℝ, 0 < R → R ≤ 1 →
          dirichletBoundaryOscillation f p (R / 256) ≤
            θ * dirichletBoundaryOscillation f p R + C * R) →
        ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
          ∀ r : ℝ, 0 < r → r ≤ R₀ →
            dirichletBoundaryOscillation f p r ≤ (D * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  obtain ⟨τ, D, hτ0, hτ1, hD, hBudget⟩ :=
    exists_dirichlet_oscillation_geometric_budget hθ0 hθ1 hC (by positivity : 0 ≤ 2 * B)
  obtain ⟨α, hα0, hα1, hτα⟩ := exists_dirichlet_boundary_decay_exponent hτ0 hτ1
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro f hBound hStep p hp R₀ hR₀ hR₀1 r hr hrR
  let rseq : ℕ → ℝ := fun k => R₀ * (1 / 256 : ℝ) ^ k
  let o : ℕ → ℝ := fun k => dirichletBoundaryOscillation f p (rseq k)
  have hrPos (k : ℕ) : 0 < rseq k := mul_pos hR₀ (pow_pos (by norm_num) _)
  have hrLe (k : ℕ) : rseq k ≤ R₀ :=
    mul_le_of_le_one_right hR₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hInitial : o 0 ≤ 2 * B := by
    have h := (dirichletBoundaryOscillation_le_of_bounds f hp hR₀
      (fun x hx => abs_le.mp (hBound x hx.1))).2
    simpa only [o, rseq, pow_zero, mul_one, sub_neg_eq_add, two_mul] using h
  have hRec (k : ℕ) : o (k + 1) ≤ θ * o k + C * (1 / 4 : ℝ) ^ k := by
    have hRadius : rseq (k + 1) = rseq k / 256 := by dsimp [rseq]; rw [pow_succ]; ring
    have h := hStep p hp (rseq k) (hrPos k) ((hrLe k).trans hR₀1)
    change dirichletBoundaryOscillation f p (rseq (k + 1)) ≤ _
    rw [hRadius]
    apply h.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hC
    calc
      rseq k ≤ (1 / 256 : ℝ) ^ k :=
        mul_le_of_le_one_left (pow_nonneg (by norm_num) _) hR₀1
      _ ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hGeo := hBudget o hInitial hRec
  apply dirichlet_boundary_power_bound_of_geometric
    (fun t => dirichletBoundaryOscillation f p t) hR₀ hD hτ0.le hα0.le hτα ?_ hGeo hr hrR
  intro a b ha hab hb
  exact dirichletBoundaryOscillation_mono f hp ha hab
    (fun x hx => abs_le.mp (hBound x hx.1))

end KEBall
