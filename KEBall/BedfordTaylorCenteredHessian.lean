import PshLines.FirstPass.SmoothPshHessian
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema

/-!
# Real Hessian bounds from centered differences and plurisubharmonicity
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel leviForm_nonneg_of_contDiffOn_plurisubharmonicOn)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

private theorem iteratedDeriv_two_affineLine {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (v : E) :
    iteratedDeriv 2 (fun t : ℝ => u (x + t • v)) 0 = PshLines.realHessian u x v v := by
  let γ (t : ℝ) := x + t • v
  have hγ : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγ₀ : γ 0 = x := by simp [γ]
  have hγ₁ : deriv γ = fun _ => v := by
    funext t
    exact (show HasDerivAt γ v t by
      simpa only [γ, id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x).deriv
  have hγ₂ : iteratedDeriv 2 γ 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hγ₁, deriv_const]
  have hu' : ContDiffAt ℝ 2 u (γ 0) := by rw [hγ₀]; exact hu
  have h := iteratedDeriv_vcomp_two hu' hγ.contDiffAt
  rw [hγ₀, hγ₁, hγ₂, map_zero, add_zero] at h
  have hv : (fun _ : Fin 2 => v) = ![v, v] := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact h

/-- An upper bound for centered differences along one line bounds the
real Hessian in that direction. -/
theorem realHessian_le_of_eventually_centered_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {x : E} {a : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (v : E)
    (hcenter : ∀ᶠ t : ℝ in 𝓝 0, u (x + t • v) + u (x - t • v) - 2 * u x ≤ a * t ^ 2) :
    PshLines.realHessian u x v v ≤ a := by
  let p (t : ℝ) := u (x + t • v)
  let q (t : ℝ) := u (x + t • (-v))
  let g (t : ℝ) := p t + q t - a * t ^ 2
  have hφ (w : E) : ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • w)) 0 := by
    have hγ : ContDiff ℝ 2 (fun t : ℝ => x + t • w) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    exact (show ContDiffAt ℝ 2 u (x + (0 : ℝ) • w) by simpa using hu).comp 0 hγ.contDiffAt
  have hp : ContDiffAt ℝ 2 p 0 := hφ v
  have hq : ContDiffAt ℝ 2 q 0 := hφ (-v)
  have ha : ContDiffAt ℝ 2 (fun t : ℝ => a * t ^ 2) 0 :=
    (contDiff_const.mul (contDiff_id.pow 2)).contDiffAt
  have hg : ContDiffAt ℝ 2 g 0 := (hp.add hq).sub ha
  have hmax : IsLocalMax g 0 := by
    filter_upwards [hcenter] with t ht
    simp only [g, p, q, zero_smul, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, sub_zero, smul_neg, ← sub_eq_add_neg]
    linarith only [ht]
  have hdd : iteratedDeriv 2 g 0 ≤ 0 := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact PoincareMT.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax hmax hg.continuousAt
  have hqdd : iteratedDeriv 2 q 0 = PshLines.realHessian u x v v := by
    rw [show iteratedDeriv 2 q 0 = PshLines.realHessian u x (-v) (-v) from
      iteratedDeriv_two_affineLine hu (-v)]
    simp only [PshLines.realHessian_eq_fderiv, map_neg, neg_apply, neg_neg]
  have hquad : iteratedDeriv 2 (fun t : ℝ => a * t ^ 2) 0 = 2 * a := by
    have hpow : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2) 0 := (contDiff_id.pow 2).contDiffAt
    rw [iteratedDeriv_const_mul a hpow, iteratedDeriv_fun_pow_zero]
    norm_num
    ring
  change iteratedDeriv 2 (fun t => p t + q t - a * t ^ 2) 0 ≤ 0 at hdd
  rw [iteratedDeriv_fun_sub (hp.add hq) ha, iteratedDeriv_fun_add hp hq,
    show iteratedDeriv 2 p 0 = PshLines.realHessian u x v v from iteratedDeriv_two_affineLine hu v,
    hqdd, hquad] at hdd
  linarith

/-- An upper bound for all small centered differences bounds the real
Hessian at the center. -/
theorem realHessian_le_of_eventually_centered_difference {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {x : E} {C : ℝ}
    (hu : ContDiffAt ℝ 2 u x)
    (hcenter : ∀ᶠ h in 𝓝 (0 : E), u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2)
    (v : E) : PshLines.realHessian u x v v ≤ C * ‖v‖ ^ 2 := by
  apply realHessian_le_of_eventually_centered_line hu v
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  filter_upwards [ht.eventually hcenter] with t ht
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at ht
  exact ht.trans_eq (by ring)

/-- The real Hessian of a smooth PSH function is bounded on both sides
by the same constant when its centered differences have an upper bound. -/
theorem abs_realHessian_le_of_eventually_centered_difference {n : ℕ}
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ} {x : ComplexModel n} {C : ℝ}
    (hu : IsSmoothPshOn Ω u) (hx : x ∈ Ω)
    (hcenter : ∀ᶠ h in 𝓝 (0 : ComplexModel n),
      u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2)
    (v : ComplexModel n) :
    |PshLines.realHessian u x v v| ≤ C * ‖v‖ ^ 2 := by
  have hs : ContDiffAt ℝ 2 u x := (hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv := realHessian_le_of_eventually_centered_difference hs hcenter v
  have hIv := realHessian_le_of_eventually_centered_difference hs hcenter (Complex.I • v)
  rw [norm_smul, Complex.norm_I, one_mul] at hIv
  have hLevi := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hu.1 hu.2.1 hx v
  rw [leviForm] at hLevi
  exact abs_le.mpr ⟨by linarith, hv⟩

/-- The centered difference estimate gives the operator norm bound on the
entire real Hessian of a smooth PSH potential. -/
theorem norm_fderiv_fderiv_le_of_eventually_centered_difference {n : ℕ}
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ} {x : ComplexModel n} {C : ℝ}
    (hu : IsSmoothPshOn Ω u) (hx : x ∈ Ω) (hC : 0 ≤ C)
    (hcenter : ∀ᶠ h in 𝓝 (0 : ComplexModel n),
      u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C := by
  let D := fderiv ℝ (fderiv ℝ u) x
  have hs : ContDiffAt ℝ 2 u x := (hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsymm (v w : ComplexModel n) : D v w = D w v :=
    hs.isSymmSndFDerivAt (by norm_num) v w
  change ‖D‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro w hw
  have hdiag (y : ComplexModel n) : |D y y| ≤ C * ‖y‖ ^ 2 := by
    simpa only [D, PshLines.realHessian_eq_fderiv] using
      abs_realHessian_le_of_eventually_centered_difference hu hx hcenter y
  have hplus := abs_le.mp (hdiag (v + w))
  have hminus := abs_le.mp (hdiag (v - w))
  have hpar := congrArg (fun t : ℝ => C * t) (parallelogram_law_with_norm ℂ v w)
  rw [hv, hw] at hpar
  have hpol : D (v + w) (v + w) - D (v - w) (v - w) = 4 * D v w := by
    simp only [map_add, map_sub, add_apply, sub_apply, hsymm w v]
    ring
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith only [hplus.1, hminus.2, hpol, hpar],
    by linarith only [hplus.2, hminus.1, hpol, hpar]⟩

end KEBall.BedfordTaylor
