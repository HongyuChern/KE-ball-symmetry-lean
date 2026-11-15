import KEBall.DirichletWholeRegularity
import Mathlib.Analysis.Calculus.Taylor

/-! Relating Taylor's theorem on a chord to derivatives in Euclidean space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Interval Topology

namespace KEBall

theorem iteratedDeriv_segmentParam {n : ℕ} {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : E n) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => f (x + s • v)) t =
      iteratedFDeriv ℝ k f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] E n := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let g (y : E n) := f (x + y)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  change iteratedDeriv k (g ∘ L) t = _
  rw [iteratedDeriv_eq_iteratedFDeriv, L.iteratedFDeriv_comp_right hg t (i := k) (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ k g (t • v) (fun _ => (1 : ℝ) • v) = _
  rw [show iteratedFDeriv ℝ k g (t • v) = iteratedFDeriv ℝ k f (x + t • v) from
    iteratedFDeriv_comp_add_left k x (t • v)]
  simp

/-- Taylor's integral formula along the chord from `y` to `x`. -/
theorem segment_taylor_integral {n : ℕ} {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x y : E n) (m : ℕ) :
    f x = (∑ k ∈ Finset.range (m + 1), (k.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ k f y (fun _ => x - y)) +
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ m / m.factorial) *
        iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ => x - y) := by
  let g (s : ℝ) := f (y + s • (x - y))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hU : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hgM : ContDiff ℝ (m + 1 : ℕ) g :=
    hg.of_le (show ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have h := taylor_integral_remainder
    (x₀ := (0 : ℝ)) (x := 1) (n := m) hgM.contDiffOn
  have hTaylor : taylorWithinEval g m (uIcc (0 : ℝ) 1) 0 1 =
      ∑ k ∈ Finset.range (m + 1), (k.factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ k f y (fun _ => x - y) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hgK : ContDiff ℝ (k : ℕ) g := hg.of_le (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    rw [iteratedDerivWithin_eq_iteratedDeriv hU hgK.contDiffAt (left_mem_uIcc),
      iteratedDeriv_segmentParam hf]
    simp
  have hRem :
      (∫ t in (0 : ℝ)..1, ((1 - t) ^ m / m.factorial) •
        iteratedDerivWithin (m + 1) g (uIcc (0 : ℝ) 1) t) =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ m / m.factorial) *
        iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ => x - y) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv hU hgM.contDiffAt ht,
      iteratedDeriv_segmentParam hf, smul_eq_mul]
  change g 1 - taylorWithinEval g m (uIcc (0 : ℝ) 1) 0 1 = _ at h
  rw [hTaylor, hRem] at h
  have hx : g 1 = f x := by simp [g]
  rw [hx] at h
  linarith only [h]

end KEBall
