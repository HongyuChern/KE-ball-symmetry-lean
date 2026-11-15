import KEBall.DirichletAngularIntegrationByParts
import KEBall.DirichletSignedPower

/-!
# The exact angular Lp identity

The odd C1 power is differentiable even where the angular derivative
vanishes.  Thus no regularization limit or nonvanishing hypothesis is
hidden in the weighted integration by parts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem integral_dirichlet_angular_power_identity {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f g h : E n → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hDf : ∀ x ∈ unitBall n, fderiv ℝ f x (T x) = g x)
    (hDg : ∀ x ∈ unitBall n, fderiv ℝ g x (T x) = h x)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in unitBall n, |g x| ^ (r + 2) ∂volume0 n) =
      -(r + 1) * ∫ x in unitBall n, f x * |g x| ^ r * h x ∂volume0 n := by
  let μ := (volume0 n).restrict (unitBall n)
  let P (x : E n) := dirichletSignedPower r (g x)
  have hP : ContDiffOn ℝ 1 P U := (contDiff_dirichletSignedPower hr).comp_contDiffOn hg
  have hPD (x : E n) (hx : x ∈ unitBall n) :
      fderiv ℝ P x (T x) = (r + 1) * |g x| ^ r * h x := by
    have hgD := (hg.contDiffAt (hU.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
      (by norm_num)
    have hd := (hasDerivAt_dirichletSignedPower hr (g x)).comp_hasFDerivAt x hgD.hasFDerivAt
    change HasFDerivAt P _ x at hd
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul, hDg x hx]
  calc
    _ = ∫ x, fderiv ℝ f x (T x) * P x ∂μ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      change |g x| ^ (r + 2) = fderiv ℝ f x (T x) * P x
      rw [hDf x hx]
      exact (mul_dirichletSignedPower hr (g x)).symm
    _ = -(∫ x, f x * fderiv ℝ P x (T x) ∂μ) :=
      integral_dirichlet_skew_derivative_mul hn hU hSub hf hP T hT
    _ = -(∫ x, (r + 1) * (f x * |g x| ^ r * h x) ∂μ) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      change f x * fderiv ℝ P x (T x) = (r + 1) * (f x * |g x| ^ r * h x)
      rw [hPD x hx]
      ring
    _ = _ := by rw [integral_const_mul, neg_mul]

end KEBall
