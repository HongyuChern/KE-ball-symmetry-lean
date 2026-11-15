import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The radial integral in Corollary 1.3

The one-dimensional integral in the manuscript has a finite critical limit.
Integration by parts expresses it using a kernel bounded by a polynomial.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped BigOperators Interval Topology

namespace KEBall.MoserTrudinger

/-- The integral giving the subcritical radial value after the change of variables. -/
noncomputable def radialValue (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, -(n : ℝ) * x ^ (n - 1) * Real.log (1 - t * x)

/-- The additive constant in Corollary 1.3, indexed from zero. -/
noncomputable def harmonicConstant (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1)

private theorem denominator_pos {t x : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (hx : x ≤ 1) : 0 < 1 - t * x := by
  have htx : t * x ≤ t := by simpa using mul_le_mul_of_nonneg_left hx ht₀
  linarith

theorem radialValue_eq_integral (n : ℕ) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    radialValue n t = ∫ x in (0 : ℝ)..1, t * (1 - x ^ n) / (1 - t * x) := by
  have hlog (x : ℝ) (hx : x ∈ [[(0 : ℝ), 1]]) :
      HasDerivAt (fun x => Real.log (1 - t * x)) (-t / (1 - t * x)) x := by
    have hx₁ : x ≤ 1 := (by simpa only [uIcc_of_le zero_le_one] using hx : x ∈ Icc 0 1).2
    have hlinear : HasDerivAt (fun x : ℝ => 1 - t * x) (-t) x := by
      simpa only [Pi.sub_def, id_eq, zero_sub, mul_one] using (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul t)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (ne_of_gt (denominator_pos ht₀ ht₁ hx₁))).comp x hlinear
  have hpower (x : ℝ) :
      HasDerivAt (fun x : ℝ => 1 - x ^ n) (-(n : ℝ) * x ^ (n - 1)) x := by
    simpa only [Pi.sub_def, Pi.pow_apply, id_eq, zero_sub, mul_one, neg_mul] using (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow n)
  have hpowInt : IntervalIntegrable (fun x : ℝ => -(n : ℝ) * x ^ (n - 1)) volume 0 1 :=
    (show Continuous (fun x : ℝ => -(n : ℝ) * x ^ (n - 1)) by fun_prop).intervalIntegrable _ _
  have hlogInt : IntervalIntegrable (fun x : ℝ => -t / (1 - t * x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.div (by fun_prop) ?_
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hx
    exact ne_of_gt (denominator_pos ht₀ ht₁ hx'.2)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := 1) (fun x _ => hpower x) hlog hpowInt hlogInt
  simp only [one_pow, sub_self, zero_mul, mul_zero, sub_zero, Real.log_one, zero_sub] at h
  have heq :
      (∫ x in (0 : ℝ)..1, (1 - x ^ n) * (-t / (1 - t * x))) =
        -(∫ x in (0 : ℝ)..1, t * (1 - x ^ n) / (1 - t * x)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [heq] at h
  exact neg_injective h.symm

private theorem integral_geometric_sum (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.range n, x ^ j) = harmonicConstant n := by
  rw [intervalIntegral.integral_finsetSum (f := fun (j : ℕ) (x : ℝ) => x ^ j)
    (fun j _ => (continuous_id.pow j).intervalIntegrable 0 1)]
  unfold harmonicConstant
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_pow]
  simp

private theorem kernel_bounds (n : ℕ) {t x : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ t * (1 - x ^ n) / (1 - t * x) ∧
    t * (1 - x ^ n) / (1 - t * x) ≤ ∑ j ∈ Finset.range n, x ^ j := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range n, x ^ j :=
    Finset.sum_nonneg fun j _ => pow_nonneg hx.1 j
  have hden := denominator_pos ht₀ ht₁ hx.2
  rw [← geom_sum_mul_neg]
  constructor
  · exact div_nonneg (mul_nonneg ht₀ (mul_nonneg hsum (sub_nonneg.mpr hx.2))) hden.le
  · apply (div_le_iff₀ hden).mpr
    calc
      t * ((∑ j ∈ Finset.range n, x ^ j) * (1 - x)) =
          (∑ j ∈ Finset.range n, x ^ j) * (t * (1 - x)) := by ring
      _ ≤ (∑ j ∈ Finset.range n, x ^ j) * (1 - t * x) :=
        mul_le_mul_of_nonneg_left (by linarith) hsum

theorem radialValue_le_harmonicConstant (n : ℕ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    radialValue n t ≤ harmonicConstant n := by
  rw [radialValue_eq_integral n ht₀ ht₁, ← integral_geometric_sum]
  apply intervalIntegral.integral_mono_on zero_le_one
  · apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact (by fun_prop : ContinuousOn (fun x : ℝ => t * (1 - x ^ n)) (Icc 0 1)).div
      (by fun_prop) (fun x hx => (denominator_pos ht₀ ht₁ hx.2).ne')
  · exact (continuous_finsetSum _ fun j _ => continuous_id.pow j).intervalIntegrable 0 1
  · intro x hx
    exact (kernel_bounds n ht₀ ht₁ hx).2

theorem tendsto_radialValue (n : ℕ) :
    Tendsto (radialValue n) (𝓝[<] (1 : ℝ)) (𝓝 (harmonicConstant n)) := by
  have ht : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ t ∧ t < 1 := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t h₀ h₁
    exact ⟨(show 0 < t from h₀).le, h₁⟩
  have hlimit : Tendsto
      (fun t : ℝ => ∫ x in (0 : ℝ)..1, t * (1 - x ^ n) / (1 - t * x))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.range n, x ^ j)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => ∑ j ∈ Finset.range n, x ^ j)
    · exact Eventually.of_forall fun t =>
        (show Measurable (fun x : ℝ => t * (1 - x ^ n) / (1 - t * x)) by fun_prop).aestronglyMeasurable
    · filter_upwards [ht] with t ht
      exact Eventually.of_forall fun x hx => by
        have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hx
        obtain ⟨h₀, h₁⟩ := kernel_bounds n ht.1 ht.2 ⟨hx'.1.le, hx'.2⟩
        simpa only [Real.norm_of_nonneg h₀] using h₁
    · exact (continuous_finsetSum _ fun j _ => continuous_id.pow j).intervalIntegrable 0 1
    · have hae : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff]
      filter_upwards [hae] with x hx_ne _
      have hx₁ : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx_ne)
      have hcont : ContinuousAt (fun t : ℝ => t * (1 - x ^ n) / (1 - t * x)) 1 := by
        apply ContinuousAt.div (by fun_prop) (by fun_prop)
        simpa using hx₁
      have hkernel : (1 : ℝ) * (1 - x ^ n) / (1 - (1 : ℝ) * x) =
          ∑ j ∈ Finset.range n, x ^ j := by
        rw [one_mul, one_mul, ← geom_sum_mul_neg, mul_div_cancel_right₀ _ hx₁]
      rw [← hkernel]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [integral_geometric_sum] at hlimit
  exact hlimit.congr' (ht.mono fun t ht => (radialValue_eq_integral n ht.1 ht.2).symm)

private theorem radial_denominator_pos {s t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (hs : 0 ≤ s) : 0 < 1 - t + t * s :=
  add_pos_of_pos_of_nonneg (sub_pos.mpr ht₁) (mul_nonneg ht₀ hs)

/-- The energy of the subcritical radial profile, reduced to one variable
and multiplied by `t`. The change of variables is `x = s/(1-t+ts)`. -/
theorem integral_radial_energy (n : ℕ) (hn : 0 < n) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (∫ s in (0 : ℝ)..1,
      (n : ℝ) * (1 - t) * s ^ (n - 1) / (1 - t + t * s) ^ (n + 1) *
        (-Real.log (1 - t + t * s))) =
      -Real.log (1 - t) - radialValue n t := by
  let d : ℝ → ℝ := fun s => 1 - t + t * s
  let f : ℝ → ℝ := fun s => s / d s
  let w : ℝ → ℝ := fun x => (n : ℝ) * x ^ (n - 1)
  let g : ℝ → ℝ := fun x => w x * (Real.log (1 - t * x) - Real.log (1 - t))
  have hd (s : ℝ) (hs : s ∈ [[(0 : ℝ), 1]]) : 0 < d s := by
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    exact radial_denominator_pos ht₀ ht₁ hs'.1
  have hds (s : ℝ) : HasDerivAt d t s := by
    simpa only [d, Pi.add_def, id_eq, zero_add, mul_one] using
      (hasDerivAt_const s (1 - t)).add ((hasDerivAt_id s).const_mul t)
  have hf (s : ℝ) (hs : s ∈ [[(0 : ℝ), 1]]) :
      HasDerivAt f ((1 - t) / d s ^ 2) s := by
    have h := (hasDerivAt_id s).div (hds s) (hd s hs).ne'
    simp only [id_eq, Pi.div_def, one_mul] at h
    have hnum : d s - s * t = 1 - t := by dsimp [d]; ring
    rw [hnum] at h
    exact h
  have hc : ContinuousOn (fun s => (1 - t) / d s ^ 2) [[(0 : ℝ), 1]] :=
    continuousOn_const.div (by dsimp [d]; fun_prop) (fun s hs => pow_ne_zero _ (hd s hs).ne')
  have hmap : f '' [[(0 : ℝ), 1]] ⊆ Icc (0 : ℝ) 1 := by
    rintro x ⟨s, hs, rfl⟩
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    refine ⟨div_nonneg hs'.1 (hd s hs).le, (div_le_one (hd s hs)).mpr ?_⟩
    dsimp [d]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₁.le) (sub_nonneg.mpr hs'.2)]
  have hlog : ContinuousOn (fun x : ℝ => Real.log (1 - t * x)) (Icc 0 1) :=
    (show ContinuousOn (fun x : ℝ => 1 - t * x) (Icc 0 1) by fun_prop).log
      (fun x hx => (denominator_pos ht₀ ht₁ hx.2).ne')
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hg : ContinuousOn g (Icc 0 1) :=
    hw.continuousOn.mul (hlog.sub continuousOn_const)
  have hsubst := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1)
    hf hc (hg.mono hmap)
  have hf₀ : f 0 = 0 := by simp [f]
  have hf₁ : f 1 = 1 := by
    have hd₁ : d 1 = 1 := by dsimp [d]; ring
    simp [f, hd₁]
  rw [hf₀, hf₁] at hsubst
  have hpoint (s : ℝ) (hs : s ∈ [[(0 : ℝ), 1]]) :
      (n : ℝ) * (1 - t) * s ^ (n - 1) / d s ^ (n + 1) * (-Real.log (d s)) =
        (g ∘ f) s * ((1 - t) / d s ^ 2) := by
    have hfrac : 1 - t * f s = (1 - t) / d s := by
      unfold f
      field_simp [(hd s hs).ne']
      dsimp [d]
      ring
    have hn' : n - 1 + 2 = n + 1 := by omega
    have hdlog := Real.log_div (sub_pos.mpr ht₁).ne' (hd s hs).ne'
    simp only [Function.comp_apply, g, w, hfrac, hdlog, sub_sub_cancel_left]
    unfold f
    rw [div_pow, ← hn', pow_add]
    ring
  change (∫ s in (0 : ℝ)..1,
      (n : ℝ) * (1 - t) * s ^ (n - 1) / d s ^ (n + 1) *
        (-Real.log (d s))) = _
  rw [intervalIntegral.integral_congr hpoint, hsubst]
  have hwlog : IntervalIntegrable (fun x => w x * Real.log (1 - t * x)) volume 0 1 := by
    refine (hw.continuousOn.mul hlog).intervalIntegrable_of_Icc zero_le_one
  have hwconst : IntervalIntegrable (fun x => w x * Real.log (1 - t)) volume 0 1 :=
    (hw.mul continuous_const).intervalIntegrable 0 1
  have hmass : (∫ x in (0 : ℝ)..1, w x) = 1 := by
    have hn' : n - 1 + 1 = n := by omega
    rw [show w = (fun x : ℝ => (n : ℝ) * x ^ (n - 1)) from rfl,
      intervalIntegral.integral_const_mul, integral_pow, hn']
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn'
    simp only [one_pow, zero_pow (Nat.ne_of_gt hn), sub_zero, hcast]
    field_simp [(show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)]
  have hrad :
      (∫ x in (0 : ℝ)..1, w x * Real.log (1 - t * x)) = -radialValue n t := by
    rw [radialValue, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [w]
    ring
  simp only [g, mul_sub]
  rw [intervalIntegral.integral_sub hwlog hwconst, hrad,
    intervalIntegral.integral_mul_const, hmass, one_mul]
  ring

#print axioms radialValue_eq_integral
#print axioms integral_radial_energy
#print axioms tendsto_radialValue

end KEBall.MoserTrudinger
