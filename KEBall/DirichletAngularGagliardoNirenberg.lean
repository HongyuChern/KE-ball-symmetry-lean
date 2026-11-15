import KEBall.DirichletAngularInterpolationStep
import KEBall.DirichletInterpolationDiscrete

/-!
# Gagliardo-Nirenberg interpolation for actual angular derivative chains

The domain is the actual closed Euclidean ball.  The proof uses its
tangential skew field, the proved Lp integration-by-parts steps, and a
pure real-sequence interpolation lemma.  No boundaryless-manifold
instance is used for the ball, and the scalar chain has no boundary
vanishing assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichlet_angular_chain_gagliardo_nirenberg {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    (F : ℕ → E n → ℝ) (hF : ∀ i, i ≤ k → ContDiffOn ℝ 1 (F i) U)
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hChain : ∀ i, i < k → ∀ x ∈ unitBall n,
      fderiv ℝ (F i) x (T x) = F (i + 1) x)
    {B : ℝ} (hB : 0 ≤ B) (hBase : ∀ x ∈ unitBall n, |F 0 x| ≤ B)
    {j : ℕ} (hj : 0 < j) (hjk : j < k) :
    (dirichletLpSize (F j) (2 * (k : ℝ) / j)) ^ k ≤
      (2 * (k : ℝ)) ^ (k ^ 3) * B ^ (k - j) * (dirichletLpSize (F k) 2) ^ j := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let a (i : ℕ) : ℝ := if i = 0 then B else dirichletLpSize (F i) (2 * (k : ℝ) / i)
  have ha (i : ℕ) : 0 ≤ a i := by
    dsimp only [a]
    split_ifs
    · exact hB
    · exact dirichletLpSize_nonneg _ _
  have hStep (i : ℕ) (hi : i + 1 < k) :
      a (i + 1) ^ 2 ≤ (2 * (k : ℝ)) * a i * a (i + 2) := by
    have hiK : i ≤ k := by omega
    have hi1K : i + 1 ≤ k := by omega
    have hi2K : i + 2 ≤ k := by omega
    have hSmall : (i : ℝ) + 1 < k := by exact_mod_cast hi
    have hiNonneg : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    let p : ℝ := 2 * (k : ℝ) / ((i : ℝ) + 1)
    have hp : 2 < p := by
      dsimp [p]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < i + 1)]
      linarith
    have hpBound : p - 1 ≤ 2 * (k : ℝ) := by
      have hdiv : p ≤ 2 * (k : ℝ) := by
        dsimp [p]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < i + 1)]
        nlinarith only [mul_nonneg hkR.le hiNonneg]
      linarith only [hdiv]
    by_cases hi0 : i = 0
    · subst i
      have h := dirichlet_angular_lp_logconvex_sup hn hU hSub (hF 0 (by omega))
        (hF 1 (by omega)) ((hF 2 (by omega)).continuousOn.mono hSub) T hT
        (hChain 0 (by omega)) (hChain 1 (by omega)) hp hB hBase
      have h' := h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpBound hB) (dirichletLpSize_nonneg (F 2) (p / 2)))
      simpa [a, p] using h'
    · have hiR : (0 : ℝ) < i := by exact_mod_cast (Nat.pos_of_ne_zero hi0)
      have hBalance : (2 * (k : ℝ) / i)⁻¹ + (2 * (k : ℝ) / (i + 2))⁻¹ = 2 / p := by
        dsimp [p]
        rw [inv_div, inv_div]
        field_simp
        ring
      have h := dirichlet_angular_lp_logconvex hn hU hSub (hF i hiK) (hF (i + 1) hi1K)
        ((hF (i + 2) hi2K).continuousOn.mono hSub) T hT
        (hChain i (by omega)) (hChain (i + 1) hi) hp
        (show 0 < 2 * (k : ℝ) / i by positivity)
        (show 0 < 2 * (k : ℝ) / (i + 2) by positivity) hBalance
      have h' := h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpBound (dirichletLpSize_nonneg (F i) _))
          (dirichletLpSize_nonneg (F (i + 2)) _))
      simpa [a, hi0, p, Nat.cast_add, Nat.cast_one] using h'
  have h := dirichlet_discrete_log_convex_power_interpolation a ha (2 * (k : ℝ))
    (by have h := hkR; exact_mod_cast (by omega : 1 ≤ 2 * k)) j k hStep hj hjk
  have hEnd : a k = dirichletLpSize (F k) 2 := by
    dsimp [a]
    rw [if_neg (by omega), mul_div_cancel_right₀ _ hkR.ne']
  rw [hEnd] at h
  simpa only [a, if_pos rfl, if_neg (Nat.ne_of_gt hj)] using h

end KEBall
