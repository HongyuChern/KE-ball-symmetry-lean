import PshLines.FirstPass.SmoothPshHessian
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth maximum with exact affine branches

The integral of a smooth transition supplies a convex function with
slopes zero and one outside its transition interval.
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ContDiff Interval Topology

namespace KEBall.BedfordTaylor

private noncomputable def hinge (t : ℝ) : ℝ :=
  ∫ s in 0..t, Real.smoothTransition s

private theorem hasDerivAt_hinge (t : ℝ) : HasDerivAt hinge (Real.smoothTransition t) t :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem deriv_hinge : deriv hinge = Real.smoothTransition :=
  funext fun t => (hasDerivAt_hinge t).deriv

private theorem contDiff_hinge : ContDiff ℝ ∞ hinge := by
  refine contDiff_infty_iff_deriv.2 ⟨fun t => (hasDerivAt_hinge t).differentiableAt, ?_⟩
  rw [deriv_hinge]
  exact Real.smoothTransition.contDiff

private theorem hinge_nonneg_deriv (t : ℝ) : 0 ≤ deriv hinge t := by
  rw [deriv_hinge]
  exact Real.smoothTransition.nonneg t

private theorem hinge_deriv_le_one (t : ℝ) : deriv hinge t ≤ 1 := by
  rw [deriv_hinge]
  exact Real.smoothTransition.le_one t

private theorem hinge_nonneg_second_deriv (t : ℝ) : 0 ≤ deriv (deriv hinge) t := by
  rw [deriv_hinge]
  exact Real.smoothTransition.monotone.deriv_nonneg

private theorem hinge_eq_zero {t : ℝ} (ht : t ≤ 0) : hinge t = 0 := by
  unfold hinge
  rw [show (∫ s in (0 : ℝ)..t, Real.smoothTransition s) = ∫ _ in (0 : ℝ)..t, (0 : ℝ) from
    intervalIntegral.integral_congr (by
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact Real.smoothTransition.zero_of_nonpos hs.2)]
  simp

private theorem hinge_eq_linear {t : ℝ} (ht : 1 ≤ t) : hinge t = hinge 1 + (t - 1) := by
  have h : (∫ s in (1 : ℝ)..t, Real.smoothTransition s) = t - 1 := by
    rw [show (∫ s in (1 : ℝ)..t, Real.smoothTransition s) = ∫ _ in (1 : ℝ)..t, (1 : ℝ) from
      intervalIntegral.integral_congr (by
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact Real.smoothTransition.one_of_one_le hs.1)]
    simp
  unfold hinge
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (Real.smoothTransition.continuous.intervalIntegrable 0 1)
    (Real.smoothTransition.continuous.intervalIntegrable 1 t), h]

private theorem hinge_one_bounds : 0 ≤ hinge 1 ∧ hinge 1 ≤ 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg zero_le_one fun x _ => Real.smoothTransition.nonneg x
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (g := fun _ : ℝ => (1 : ℝ)) (a := 0) (b := 1) zero_le_one
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) (fun x _ => Real.smoothTransition.le_one x)
    simpa [hinge] using h

/-- A smooth maximum which equals the larger input whenever the two
inputs differ by at least one. -/
noncomputable def smoothMax (a b : ℝ) : ℝ :=
  b + hinge (a - b + (1 - hinge 1))

theorem smoothMax_eq_left {a b : ℝ} (h : b + 1 ≤ a) : smoothMax a b = a := by
  unfold smoothMax
  rw [hinge_eq_linear (by linarith [hinge_one_bounds.2])]
  ring

theorem smoothMax_eq_right {a b : ℝ} (h : a + 1 ≤ b) : smoothMax a b = b := by
  unfold smoothMax
  rw [hinge_eq_zero (by linarith [hinge_one_bounds.1]), add_zero]

theorem monotone_smoothMax_left (b : ℝ) : Monotone (fun a => smoothMax a b) := by
  have h := monotone_of_deriv_nonneg (contDiff_hinge.differentiable (by simp)) hinge_nonneg_deriv
  intro a a' haa'
  unfold smoothMax
  exact add_le_add le_rfl (h (add_le_add (sub_le_sub_right haa' b) le_rfl))

theorem contDiff_smoothMax : ContDiff ℝ ∞ (fun z : ℝ × ℝ => smoothMax z.1 z.2) := by
  unfold smoothMax
  exact contDiff_snd.add (contDiff_hinge.comp ((contDiff_fst.sub contDiff_snd).add contDiff_const))

private theorem realHessian_hinge_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ ∞ g x) (a b : E) :
    PshLines.realHessian (hinge ∘ g) x a b =
      deriv (deriv hinge) (g x) * fderiv ℝ g x a * fderiv ℝ g x b +
        deriv hinge (g x) * PshLines.realHessian g x a b := by
  have hg₁ : ContDiffAt ℝ 1 g x := hg.of_le (by simp)
  have h₁ : fderiv ℝ (hinge ∘ g) =ᶠ[𝓝 x]
      fun y => deriv hinge (g y) • fderiv ℝ g y := by
    filter_upwards [hg₁.eventually (by simp)] with y hy
    exact (((hasDerivAt_hinge (g y)).comp_hasFDerivAt y
      (hy.differentiableAt one_ne_zero).hasFDerivAt).fderiv).trans
      (by rw [(hasDerivAt_hinge (g y)).deriv])
  have hD := ((contDiff_infty_iff_deriv.mp contDiff_hinge).2).differentiable (by simp)
  have h₂ := (hD (g x)).hasDerivAt.comp_hasFDerivAt x (hg.differentiableAt (by simp)).hasFDerivAt
  have h₃ : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  change HasFDerivAt (fun y => deriv hinge (g y)) _ x at h₂
  rw [PshLines.realHessian_eq_fderiv, PshLines.realHessian_eq_fderiv, h₁.fderiv_eq,
    fderiv_fun_smul h₂.differentiableAt h₃, h₂.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  ring

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh)

private theorem plurisubharmonicOn_of_local_levi_nonneg {n : ℕ} {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (hL : ∀ x ∈ Ω, ∀ a, 0 ≤ leviForm f x a) :
    PlurisubharmonicOn (fun y => (f y : EReal)) Ω := by
  intro x hx
  obtain ⟨g, hg, hfg⟩ :=
    PshLines.FirstPass.exists_contDiff_eventuallyEq_of_contDiffOn Ω.isOpen hf hx
  obtain ⟨V, hVsub, hVo, hxV⟩ :=
    mem_nhds_iff.mp (inter_mem hfg (Ω.isOpen.mem_nhds hx))
  have hgL (y : ComplexModel n) (hy : y ∈ V) (a : ComplexModel n) : 0 ≤ leviForm g y a := by
    have heq : f =ᶠ[𝓝 y] g := by
      filter_upwards [hVo.mem_nhds hy] with z hz
      exact (hVsub hz).1
    have hd : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := heq.fderiv.fderiv_eq
    simpa only [leviForm, PshLines.realHessian_eq_fderiv, hd] using hL y (hVsub hy).2 a
  have hgPsh := plurisubharmonicOn_of_levi_nonneg
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hVo hgL
  exact (hgPsh x hxV).congr (hfg.symm.mono fun _ hy => congrArg (fun t : ℝ => (t : EReal)) hy)

set_option maxHeartbeats 450000 in
/-- A smooth maximum of two smooth PSH functions is smooth and PSH on
their common open domain. -/
theorem isSmoothPshOn_smoothMax {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u b : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) (hb : IsSmoothPshOn Ω b) :
    IsSmoothPshOn Ω (fun x => smoothMax (u x) (b x)) := by
  let g : ComplexModel n → ℝ := fun x => u x - b x + (1 - hinge 1)
  have hg : ContDiffOn ℝ ∞ g Ω := (hu.1.sub hb.1).add contDiffOn_const
  have hs : ContDiffOn ℝ ∞ (fun x => smoothMax (u x) (b x)) Ω :=
    contDiff_smoothMax.comp_contDiffOn (hu.1.prodMk hb.1)
  apply isSmoothPshOn_of_psh hs (plurisubharmonicOn_of_local_levi_nonneg hs ?_)
  intro x hx v
  have huAt := hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)
  have hbAt := hb.1.contDiffAt (Ω.isOpen.mem_nhds hx)
  have hgAt := hg.contDiffAt (Ω.isOpen.mem_nhds hx)
  have hn : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hgEq : g = (u + -b) + (fun _ => 1 - hinge 1) := by
    funext y
    simp only [g, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  have hH (a : ComplexModel n) :
      PshLines.realHessian g x a a =
        PshLines.realHessian u x a a - PshLines.realHessian b x a a := by
    have hsum : ContDiffAt ℝ 2 (u + -b) x := (huAt.add hbAt.neg).of_le hn
    have hneg : ContDiffAt ℝ 2 (-b) x := hbAt.neg.of_le hn
    rw [hgEq, PshLines.realHessian_add hsum contDiffAt_const,
      PshLines.realHessian_add (huAt.of_le hn) hneg,
      PshLines.realHessian_const, PshLines.realHessian_neg, add_zero, sub_eq_add_neg]
  have h : ContDiffAt ℝ 2 (hinge ∘ g) x := (contDiff_hinge.contDiffAt.comp x hgAt).of_le hn
  change 0 ≤ leviForm (b + hinge ∘ g) x v
  rw [leviForm_add (hbAt.of_le hn) h]
  have heq : leviForm b x v + leviForm (hinge ∘ g) x v =
      (1 - deriv hinge (g x)) * leviForm b x v +
      deriv hinge (g x) * leviForm u x v +
      deriv (deriv hinge) (g x) *
        ((fderiv ℝ g x v) ^ 2 + (fderiv ℝ g x (Complex.I • v)) ^ 2) / 4 := by
    simp only [leviForm, realHessian_hinge_comp hgAt, hH]
    ring
  rw [heq]
  have hu₀ := PshLines.FirstPass.leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hu.1 hu.2.1 hx v
  have hb₀ := PshLines.FirstPass.leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hb.1 hb.2.1 hx v
  have h₀ := hinge_nonneg_deriv (g x)
  have h₁ := sub_nonneg.mpr (hinge_deriv_le_one (g x))
  have h₂ := hinge_nonneg_second_deriv (g x)
  positivity

end KEBall.BedfordTaylor
