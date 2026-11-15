import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The C1 odd power used in angular Lp integration by parts, including at zero. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace KEBall

noncomputable def dirichletSignedPower (r x : ℝ) : ℝ := x * |x| ^ r

private theorem hasDerivAt_dirichletSignedPower_of_ne_zero (r : ℝ) {x : ℝ}
    (hx : x ≠ 0) :
    HasDerivAt (dirichletSignedPower r) ((r + 1) * |x| ^ r) x := by
  have hPow : |x| ^ (r - 1) * |x| = |x| ^ r := by
    rw [← Real.rpow_add_one (abs_ne_zero.mpr hx)]
    congr 1
    ring
  rcases hx.lt_or_gt with hx | hx
  · have h := (hasDerivAt_id x).fun_mul
      ((hasDerivAt_abs_neg hx).rpow_const (p := r) (Or.inl (abs_ne_zero.mpr hx.ne)))
    have he : 1 * |x| ^ r + x * ((-1) * r * |x| ^ (r - 1)) =
        (r + 1) * |x| ^ r := by
      calc
        _ = |x| ^ r + r * (|x| ^ (r - 1) * |x|) := by rw [abs_of_neg hx]; ring
        _ = _ := by rw [hPow]; ring
    change HasDerivAt (fun y : ℝ => y * |y| ^ r) ((r + 1) * |x| ^ r) x
    simpa only [id_eq, he] using h
  · have h := (hasDerivAt_id x).fun_mul
      ((hasDerivAt_abs_pos hx).rpow_const (p := r) (Or.inl (abs_ne_zero.mpr hx.ne')))
    have he : 1 * |x| ^ r + x * (1 * r * |x| ^ (r - 1)) =
        (r + 1) * |x| ^ r := by
      calc
        _ = |x| ^ r + r * (|x| ^ (r - 1) * |x|) := by rw [abs_of_pos hx]; ring
        _ = _ := by rw [hPow]; ring
    change HasDerivAt (fun y : ℝ => y * |y| ^ r) ((r + 1) * |x| ^ r) x
    simpa only [id_eq, he] using h

theorem hasDerivAt_dirichletSignedPower {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    HasDerivAt (dirichletSignedPower r) ((r + 1) * |x| ^ r) x := by
  by_cases hx : x = 0
  · subst x
    apply hasDerivAt_of_hasDerivAt_of_ne
      (fun y hy => hasDerivAt_dirichletSignedPower_of_ne_zero r hy)
    · exact continuousAt_id.mul (continuous_abs.continuousAt.rpow_const (Or.inr hr))
    · exact continuousAt_const.mul (continuous_abs.continuousAt.rpow_const (Or.inr hr))
  · exact hasDerivAt_dirichletSignedPower_of_ne_zero r hx

theorem contDiff_dirichletSignedPower {r : ℝ} (hr : 0 ≤ r) :
    ContDiff ℝ 1 (dirichletSignedPower r) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_dirichletSignedPower hr x).differentiableAt, ?_⟩
  have he : deriv (dirichletSignedPower r) = fun x => (r + 1) * |x| ^ r :=
    funext fun x => (hasDerivAt_dirichletSignedPower hr x).deriv
  rw [he]
  exact continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr hr))

theorem mul_dirichletSignedPower {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    x * dirichletSignedPower r x = |x| ^ (r + 2) := by
  by_cases hx : x = 0
  · subst x
    simp only [dirichletSignedPower, zero_mul, abs_zero,
      Real.zero_rpow (show r + 2 ≠ 0 by linarith)]
  · rw [Real.rpow_add (abs_pos.mpr hx), Real.rpow_two, sq_abs]
    dsimp only [dirichletSignedPower]
    ring

end KEBall
