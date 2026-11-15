import KEBall.Domain
import Mathlib.Tactic

/-!
Stage20 SOURCE_DRAFT_UNCOMPILED.
An explicit positive remainder proves a uniform quadratic deficit for the
unchanged boundary polynomial. All dimensions are handled by induction,
not by finite-dimensional polynomial tests.
-/
set_option autoImplicit false
open scoped BigOperators

namespace KEBall

/-- The positive polynomial remainder for the two-variable power identity. -/
noncomputable def weightedPowerRemainder : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | m + 1, a, s => a * weightedPowerRemainder m a s + (m + 2 : ℝ) * s ^ (m + 1)

theorem weightedPowerRemainder_identity (m : ℕ) (a s : ℝ) :
    (a - s) ^ 2 * weightedPowerRemainder m a s =
      a ^ (m + 2) - (m + 2 : ℝ) * a * s ^ (m + 1) +
        (m + 1 : ℝ) * s ^ (m + 2) := by
  induction m with
  | zero => simp only [weightedPowerRemainder, pow_one]; norm_num; ring
  | succ m ih =>
    rw [weightedPowerRemainder]
    calc
      _ = a * ((a - s) ^ 2 * weightedPowerRemainder m a s) +
          (m + 2 : ℝ) * (a - s) ^ 2 * s ^ (m + 1) := by
        push_cast
        ring
      _ = _ := by
        rw [ih]
        simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
        ring

theorem weightedPowerRemainder_ge_pow (m : ℕ) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) : a ^ m ≤ weightedPowerRemainder m a s := by
  induction m with
  | zero => simp [weightedPowerRemainder]
  | succ m ih =>
    rw [weightedPowerRemainder, pow_succ]
    have hpos : 0 ≤ (m + 2 : ℝ) * s ^ (m + 1) :=
      mul_nonneg (by positivity) (pow_nonneg hs _)
    calc
      a ^ m * a = a * a ^ m := mul_comm _ _
      _ ≤ a * weightedPowerRemainder m a s := mul_le_mul_of_nonneg_left ih ha
      _ ≤ _ := le_add_of_nonneg_right hpos

/-- The exact critical remainder; its coefficients are nonnegative for s≥0. -/
theorem boundaryPolynomial_peak_deficit_factorization {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    (n + 1 : ℝ) * (criticalCoefficient n - boundaryPolynomial n s) =
      (s - (n : ℝ)) ^ 2 *
        (s ^ (n - 1) + weightedPowerRemainder (n - 2) (n : ℝ) s) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have hp : m + 2 - 1 = m + 1 := by omega
  have hm : m + 2 - 2 = m := by omega
  rw [hp, hm]
  have hid := weightedPowerRemainder_identity m (m + 2 : ℝ) s
  calc
    _ = s ^ (m + 3) - (m + 3 : ℝ) * s ^ (m + 2) +
        (m + 2 : ℝ) ^ (m + 2) := by
      unfold criticalCoefficient boundaryPolynomial
      have hk : (m + 3 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      simp only [pow_succ]
      ring
    _ = _ := by
      simp only [pow_succ, Nat.cast_add, Nat.cast_ofNat] at hid ⊢
      linear_combination -hid

/-- A global lower bound for the deficit, with no upper bound on s. -/
theorem boundaryPolynomial_quadratic_deficit {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : 0 ≤ s) :
    (n : ℝ) ^ (n - 2) * (s - (n : ℝ)) ^ 2 ≤
      (n + 1 : ℝ) * (criticalCoefficient n - boundaryPolynomial n s) := by
  rw [boundaryPolynomial_peak_deficit_factorization hn]
  have hrem := weightedPowerRemainder_ge_pow (n - 2) (a := (n : ℝ))
    (by positivity) hs
  have hcoef : (n : ℝ) ^ (n - 2) ≤
      s ^ (n - 1) + weightedPowerRemainder (n - 2) (n : ℝ) s := by
    exact hrem.trans (le_add_of_nonneg_left (pow_nonneg hs _))
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcoef
    (sq_nonneg (s - (n : ℝ)))

end KEBall
