import KEBall.BedfordTaylorLeviMeasure
import KEBall.SecondOrderMeanValue
import KEBall.BedfordTaylorLocalLevi

/-!
# Differentiability of a limit with uniformly bounded real Hessians
-/

set_option autoImplicit false

open Filter Metric Set TopologicalSpace
open scoped ContDiff NNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn IsDecreasingApproximation)

variable {n : ℕ} {W : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

set_option maxHeartbeats 800000 in
/-- A decreasing smooth approximation with a common real Hessian bound
on an open convex domain converges to a differentiable potential with
Lipschitz derivative. -/
theorem differentiableOn_lipschitz_fderiv_of_boundedHessian
    (hu : IsLocallyBoundedPshOn W u) (hW : Convex ℝ (W : Set (ComplexModel n)))
    {p : ℕ → ComplexModel n → ℝ} (hp : IsDecreasingApproximation W u p)
    {C : ℝ} (hC : 0 ≤ C) (hess : ∀ j x, x ∈ W → ‖fderiv ℝ (fderiv ℝ (p j)) x‖ ≤ C) :
    DifferentiableOn ℝ u W ∧ LipschitzOnWith ⟨C, hC⟩ (fderiv ℝ u) W := by
  let E := ComplexModel n
  let T := E →L[ℝ] ℝ
  let _ : ProperSpace T := FiniteDimensional.proper ℝ T
  let D (j : ℕ) (x : E) : T := fderiv ℝ (p j) x
  have hcont (j : ℕ) (x : E) (hx : x ∈ W) : ContDiffAt ℝ ∞ (p j) x :=
    (hp.1 j).1.contDiffAt (W.isOpen.mem_nhds hx)
  have hdiff (j : ℕ) (x : E) (hx : x ∈ W) : DifferentiableAt ℝ (p j) x :=
    (hcont j x hx).differentiableAt (by simp)
  have hDdiff (j : ℕ) (x : E) (hx : x ∈ W) : DifferentiableAt ℝ (D j) x :=
    ((hcont j x hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hrem (j : ℕ) (x y : E) (hx : x ∈ W) (hy : y ∈ W) :
      ‖p j y - p j x - D j x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 :=
    norm_sub_linearization_le hW (hdiff j) (hDdiff j) hC (hess j) hx hy
  have hDlip (j : ℕ) (x y : E) (hx : x ∈ W) (hy : y ∈ W) :
      ‖D j y - D j x‖ ≤ C * ‖y - x‖ :=
    hW.norm_image_sub_le_of_norm_fderiv_le (hDdiff j) (hess j) hx hy
  have hDbdd (x : E) (hx : x ∈ W) : ∃ B : ℝ, ∀ j, ‖D j x‖ ≤ B := by
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp W.isOpen x hx
    let t := r / 2
    have ht : 0 < t := half_pos hr
    have hball : closedBall x t ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hrW
    obtain ⟨M, hM, hvalues⟩ := exists_compact_abs_bound_of_antitone hu
      (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp.1 j)) hp.2.1 hp.2.2
      (isCompact_closedBall x t) hball
    refine ⟨2 * M / t + C * t, fun j => ?_⟩
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro v hv
    let y := x + t • v
    have hxy : y - x = t • v := by dsimp only [y]; abel
    have hdist : ‖y - x‖ = t := by rw [hxy, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    have hy : y ∈ closedBall x t := by rw [mem_closedBall, dist_eq_norm, hdist]
    have hbX : ‖p j x‖ ≤ M := by
      simpa only [Real.norm_eq_abs] using hvalues j x (mem_closedBall_self ht.le)
    have hbY : ‖p j y‖ ≤ M := by simpa only [Real.norm_eq_abs] using hvalues j y hy
    have hR := hrem j x y hx (hball hy)
    rw [hdist] at hR
    have hD : ‖D j x (y - x)‖ ≤ 2 * M + C * t ^ 2 := calc
      _ = ‖(p j y - p j x) - (p j y - p j x - D j x (y - x))‖ := by rw [sub_sub_cancel]
      _ ≤ (‖p j y‖ + ‖p j x‖) + ‖p j y - p j x - D j x (y - x)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by linarith
    rw [hxy, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hD
    have he : (2 * M + C * t ^ 2) / t = 2 * M / t + C * t := by field_simp [ht.ne']
    rw [mul_comm t] at hD
    exact ((le_div_iff₀ ht).mpr hD).trans_eq he
  have hderiv {x : E} (hx : x ∈ W) {L : T} {s : ℕ → ℕ} (hs : StrictMono s)
      (hlim : Tendsto (fun j => D (s j) x) atTop (𝓝 L)) :
      HasFDerivAt u L x := by
    have hR (y : E) (hy : y ∈ W) : ‖u y - u x - L (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
      have hEval : Tendsto (fun j => D (s j) x (y - x)) atTop (𝓝 (L (y - x))) :=
        (ContinuousLinearMap.apply ℝ ℝ (y - x)).continuous.continuousAt.tendsto.comp hlim
      exact le_of_tendsto (((((hp.2.2 y hy).comp hs.tendsto_atTop).sub
        ((hp.2.2 x hx).comp hs.tendsto_atTop)).sub hEval).norm)
        (Eventually.of_forall fun j => hrem (s j) x y hx hy)
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have hWnear : ∀ᶠ h : E in 𝓝 0, x + h ∈ W := by
      have hc : Continuous (fun h : E => x + h) := continuous_const.add continuous_id
      have hx' : x + (0 : E) ∈ W := by rwa [add_zero]
      exact hc.continuousAt (x := 0) (W.isOpen.mem_nhds hx')
    have hsmall : ∀ᶠ h : E in 𝓝 0, C * ‖h‖ < ε := by
      have hc : Continuous (fun h : E => C * ‖h‖) := continuous_const.mul continuous_norm
      exact hc.continuousAt.eventually_lt_const (by simpa only [norm_zero, mul_zero] using hε)
    filter_upwards [hWnear, hsmall] with h hh hε'
    have hrem := hR (x + h) hh
    rw [add_sub_cancel_left] at hrem
    exact hrem.trans (by nlinarith only [mul_le_mul_of_nonneg_right hε'.le (norm_nonneg h)])
  have hCompact {x : E} (hx : x ∈ W) : ∃ K : Set T, IsCompact K ∧ ∀ j, D j x ∈ K := by
    obtain ⟨B, hB⟩ := hDbdd x hx
    exact ⟨closedBall 0 B, isCompact_closedBall _ _, fun j => by
      simpa only [mem_closedBall, dist_zero_right] using hB j⟩
  constructor
  · intro x hx
    obtain ⟨K, hK, hDK⟩ := hCompact hx
    obtain ⟨L, _, s, hs, hlim⟩ := hK.isSeqCompact hDK
    exact (hderiv hx hs hlim).differentiableAt.differentiableWithinAt
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    obtain ⟨K, hK, hxK⟩ := hCompact hx
    obtain ⟨M, hM, hyM⟩ := hCompact hy
    have hpair (j : ℕ) : (D j x, D j y) ∈ K ×ˢ M := ⟨hxK j, hyM j⟩
    obtain ⟨L, _, s, hs, hlim⟩ := (hK.prod hM).isSeqCompact hpair
    have hlimX : Tendsto (fun j => D (s j) x) atTop (𝓝 L.1) := continuous_fst.continuousAt.tendsto.comp hlim
    have hlimY : Tendsto (fun j => D (s j) y) atTop (𝓝 L.2) := continuous_snd.continuousAt.tendsto.comp hlim
    have hfx := (hderiv hx hs hlimX).fderiv
    have hfy := (hderiv hy hs hlimY).fderiv
    have hb : ‖L.1 - L.2‖ ≤ C * ‖x - y‖ :=
      le_of_tendsto (hlimX.sub hlimY).norm (Eventually.of_forall fun j => hDlip (s j) y x hy hx)
    rw [dist_eq_norm, dist_eq_norm, hfx, hfy]
    exact hb

end KEBall.BedfordTaylor
