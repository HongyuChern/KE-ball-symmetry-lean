import KEBall.CegrellL1Bound
import KEBall.BedfordTaylorCommonRegularization
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# A uniform interior approximation by radial mollifiers
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions NNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ}

private theorem integrable_translationPairing_of_integrable
    {f k : ComplexModel n → ℝ} (hf : Integrable f volume) (hk : Integrable k volume)
    (heven : ∀ x, k (-x) = k x) :
    Integrable (translationPairing volume f k) volume := by
  rw [translationPairing_eq_convolution, show (fun x => k (-x)) = k from funext heven]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hk

private theorem integral_mul_translationPairing_swap
    {f g k : ComplexModel n → ℝ}
    (hf : Integrable f volume) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Integrable k volume) (heven : ∀ x, k (-x) = k x) :
    (∫ x, g x * translationPairing volume f k x) =
      ∫ x, f x * translationPairing volume g k x := by
  obtain ⟨C, hC⟩ := hgs.exists_bound_of_continuous hg
  have hF : Integrable (fun z : ComplexModel n × ComplexModel n =>
      (f z.2 * k (z.1 - z.2)) * g z.1) (volume.prod volume) :=
    (hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk).mul_bdd
      (hg.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun z => hC z.1)
  calc
    _ = ∫ x, ∫ y, (f y * k (x - y)) * g x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [translationPairing, mul_comm (g x), ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      rw [show x - y = -(y - x) by abel, heven]
    _ = ∫ y, ∫ x, (f y * k (x - y)) * g x := integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [translationPairing, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

private theorem dist_translationPairing_cutoff_le
    (χ : 𝓓(complexUnitBall n, ℝ)) {L : ℝ≥0} (hL : LipschitzWith L χ)
    {R : ℝ} (hR : 0 < R) (j : ℕ) (z : ComplexModel n) :
    dist (translationPairing volume χ (explicitRadialKernel R hR j) z) (χ z) ≤
      (L : ℝ) * (2 * (shrinkingBump (E := ComplexModel n) R hR j).rOut) := by
  let k := explicitRadialKernel (n := n) R hR j
  let r := (shrinkingBump (E := ComplexModel n) R hR j).rOut
  have hr : 0 < r := (shrinkingBump (E := ComplexModel n) R hR j).rOut_pos
  have hSupp : Function.support k ⊆ ball 0 (2 * r) := by
    apply subset_tsupport k |>.trans
    rw [explicitRadialKernel_tsupport R hR j]
    apply closedBall_subset_ball
    change r < 2 * r
    linarith
  have hMul : ContinuousLinearMap.mul ℝ ℝ = (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := rfl
  rw [translationPairing_eq_convolution, show (fun x => k (-x)) = k from
    funext (explicitRadialKernel_neg R hR j), ← convolution_flip, hMul]
  have hFlip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    exact mul_comm y x
  rw [hFlip]
  apply dist_convolution_le (μ := volume) (mul_nonneg L.coe_nonneg (by linarith : 0 ≤ 2 * r)) hSupp
    (explicitRadialKernel_nonneg R hR j) (explicitRadialKernel_integral_one R hR j)
    χ.continuous.aestronglyMeasurable
  intro x hx
  exact (hL.dist_le_mul x z).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hx).le L.coe_nonneg)

/-- A common radial kernel can be used for every bounded potential on the
support of a fixed interior cutoff. -/
theorem exists_radialKernel_le_negativePotential (χ : 𝓓(complexUnitBall n, ℝ)) :
    ∃ R : ℝ, ∃ hR : 0 < R,
      ∀ {u : ComplexModel n → ℝ}, IsE0 (complexUnitBall n) u →
      ∀ j x, x ∈ tsupport χ →
        translationPairing volume (negativePotential (fun x => (u x : EReal)))
          (explicitRadialKernel R hR j) x ≤ negativePotential (fun x => (u x : EReal)) x := by
  let B := complexUnitBall n
  let K₀ := tsupport χ
  obtain ⟨R, hR, N, K, hN, hK₀N, hNK, hK, hKB, hball⟩ :=
    exists_open_compact_closedBall_neighborhood χ.hasCompactSupport B.isOpen χ.tsupport_subset
  refine ⟨R, hR, ?_⟩
  intro u hu j x hx
  let A : Opens (ComplexModel n) := ⟨N, hN⟩
  let p (l : ℕ) := translationPairing volume (K.indicator u) (explicitRadialKernel R hR l)
  have hp := decreasing_explicitRegularization (A := A) hu.locallyBoundedPsh hR hN
    (subset_refl N) (hNK.trans hKB) hK hKB hball
  have hxN : x ∈ N := hK₀N hx
  have hpx : u x ≤ p j x :=
    le_of_tendsto (hp.2.2 x hxN)
      ((eventually_ge_atTop j).mono fun _ hj => hp.2.1 x hxN hj)
  have hpair : translationPairing volume (negativePotential (fun x => (u x : EReal)))
      (explicitRadialKernel R hR j) x = -p j x := by
    rw [show p j x = translationPairing volume (K.indicator u) (explicitRadialKernel R hR j) x from rfl,
      translationPairing, translationPairing, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ tsupport (fun y => explicitRadialKernel R hR j (y - x))
    · have hyK := hball x hxN (closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j)
        (tsupport_explicitRadialKernel_translate_subset R hR j x hy))
      rw [negativePotential, indicator_of_mem (hKB hyK), indicator_of_mem hyK,
        EReal.toReal_coe, neg_mul]
    · have hk0 : explicitRadialKernel R hR j (y - x) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => explicitRadialKernel R hR j (y - x)) hy
      simp only [hk0, mul_zero, neg_zero]
  rw [hpair, negativePotential, indicator_of_mem (χ.tsupport_subset hx), EReal.toReal_coe]
  exact neg_le_neg hpx

/-- Integrating the error against a cutoff transfers the convolution to
the cutoff. This gives an interior error estimate uniform in the potential. -/
theorem integral_cutoff_mollification_error_le (hn : 0 < n)
    {u : ComplexModel n → ℝ} (hu : IsE0 (complexUnitBall n) u)
    (χ : 𝓓(complexUnitBall n, ℝ))
    {L : ℝ≥0} (hL : LipschitzWith L χ) {R : ℝ} (hR : 0 < R) (j : ℕ)
    (horder : ∀ x ∈ tsupport χ,
      translationPairing volume (negativePotential (fun x => (u x : EReal)))
        (explicitRadialKernel R hR j) x ≤ negativePotential (fun x => (u x : EReal)) x) :
    (∫ x, χ x * |negativePotential (fun x => (u x : EReal)) x -
        translationPairing volume (negativePotential (fun x => (u x : EReal)))
          (explicitRadialKernel R hR j) x|) ≤
      ((L : ℝ) * (2 * (shrinkingBump (E := ComplexModel n) R hR j).rOut)) *
        ∫ x, negativePotential (fun x => (u x : EReal)) x := by
  let f := negativePotential (fun x => (u x : EReal))
  let k := explicitRadialKernel (n := n) R hR j
  let g := translationPairing volume f k
  let d := (L : ℝ) * (2 * (shrinkingBump (E := ComplexModel n) R hR j).rOut)
  have hf := integrable_negativePotential hn hu.isE1
  have hk : Integrable k volume := integrable_of_integral_eq_one (explicitRadialKernel_integral_one R hR j)
  have heven : ∀ x, k (-x) = k x := explicitRadialKernel_neg R hR j
  have hg := integrable_translationPairing_of_integrable hf hk heven
  obtain ⟨C, hC⟩ := χ.hasCompactSupport.exists_bound_of_continuous χ.continuous
  have hfi : Integrable (fun x => f x * χ x) volume :=
    hf.mul_bdd χ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hχf : Integrable (fun x => χ x * f x) volume := by simpa only [mul_comm] using hfi
  have hχg : Integrable (fun x => χ x * g x) volume := hg.bdd_mul χ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hswap := integral_mul_translationPairing_swap hf χ.continuous χ.hasCompactSupport hk heven
  have hgf : Integrable (fun x => f x * translationPairing volume χ k x) volume := by
    have hχI : Integrable (χ : ComplexModel n → ℝ) volume :=
      χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
    have hC₀ : 0 ≤ C := (norm_nonneg (χ 0)).trans (hC 0)
    have hp : ∀ x, ‖translationPairing volume χ k x‖ ≤ C := by
      intro x
      rw [translationPairing]
      refine (norm_integral_le_of_norm_le ((hk.comp_sub_right x).const_mul C)
        (Eventually.of_forall fun y => ?_)).trans_eq ?_
      · rw [norm_mul, Real.norm_of_nonneg (explicitRadialKernel_nonneg R hR j _)]
        exact mul_le_mul_of_nonneg_right (hC y) (explicitRadialKernel_nonneg R hR j _)
      · rw [integral_const_mul, integral_sub_right_eq_self, explicitRadialKernel_integral_one, mul_one]
    have hc := contDiff_translationPairing hχI.locallyIntegrable
      (explicitRadialKernel_hasCompactSupport R hR j) (explicitRadialKernel_contDiff R hR j)
    exact hf.mul_bdd hc.continuous.aestronglyMeasurable (Eventually.of_forall hp)
  change (∫ x, χ x * |f x - g x|) ≤ d * ∫ x, f x
  calc
    _ = ∫ x, (χ x * f x) - (χ x * g x) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport χ
      · rw [abs_of_nonneg (sub_nonneg.mpr (horder x hx)), mul_sub]
      · rw [image_eq_zero_of_notMem_tsupport (f := χ) hx, zero_mul, zero_mul, zero_mul, sub_zero]
    _ = ∫ x, f x * (χ x - translationPairing volume χ k x) := by
      simp only [mul_sub]
      rw [integral_sub hχf hχg, show (∫ x, χ x * g x) = ∫ x, f x * translationPairing volume χ k x
        from hswap, integral_sub hfi hgf]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ ≤ ∫ x, d * f x := by
      have hi : Integrable (fun x => f x * (χ x - translationPairing volume χ k x)) volume := by
        simp only [mul_sub]
        exact hfi.sub hgf
      apply integral_mono hi (hf.const_mul d)
      intro x
      have hx : χ x - translationPairing volume χ k x ≤ d := by
        have h := dist_translationPairing_cutoff_le χ hL hR j x
        rw [dist_comm, Real.dist_eq] at h
        exact (le_abs_self _).trans h
      change f x * (χ x - translationPairing volume χ k x) ≤ d * f x
      rw [mul_comm d (f x)]
      exact mul_le_mul_of_nonneg_left hx (negativePotential_nonneg hn hu.isE1 x)
    _ = _ := integral_const_mul d f

end KEBall.Cegrell
