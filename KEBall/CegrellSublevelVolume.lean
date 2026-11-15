import KEBall.CegrellEnergyConvergence
import KEBall.CegrellQuadratic

/-!
# Volume estimates from the Cegrell energy
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

private theorem volume_sublevel_bounded {u : ComplexModel n → ℝ}
    (hu : IsE0 (complexUnitBall n) u) {t : ℝ} (ht : 0 < t) :
    (volume : Measure (ComplexModel n)).restrict (complexUnitBall n)
        {x ∈ complexUnitBall n | u x < -t} ≤
      boundedEnergy hu / ENNReal.ofReal (((n.factorial : ℝ) / Real.pi ^ n) * (t / 4) ^ (n + 1)) := by
  let B := complexUnitBall n
  let r := t / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let v (x : ComplexModel n) := r * ‖x‖ ^ 2 + -(t / 2)
  let hq := isLocallyBoundedPshOn_of_isSmoothPshOn (smoothPsh_norm_sq n)
  let hp := locallyBoundedPsh_const_mul hq hr
  let hv := locallyBoundedPsh_add_const hp (-(t / 2))
  let A : Set (ComplexModel n) := {x ∈ B | u x < v x}
  let D : Set (ComplexModel n) := {x ∈ B | u x < -t}
  have hA : MeasurableSet A := measurableSet_lt_of_locallyBoundedPsh hu.locallyBoundedPsh hv
  have hupper (x : ComplexModel n) (hx : x ∈ B) : v x ≤ -r := by
    have hnorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hp := mul_le_mul_of_nonneg_left hsq hr.le
    dsimp [v, r] at hp ⊢
    linarith
  have hD : D ⊆ A := by
    intro x hx
    have hlo : -t < v x := by
      have hm : 0 ≤ r * ‖x‖ ^ 2 := mul_nonneg hr.le (sq_nonneg _)
      dsimp [v]
      linarith
    exact ⟨hx.1, hx.2.trans hlo⟩
  have hcomp := hu.compare (isCompact_closure_complexUnitBall n) hv
    (fun x hx => (hupper x hx).trans (neg_nonpos.mpr hr.le))
  have htail : topMeasure hu.locallyBoundedPsh A ≤ boundedEnergy hu / ENNReal.ofReal r :=
    topMeasure_le_div_energy_of_sublevel hu.locallyBoundedPsh hA hr
      (fun x hx hxB => hx.2.le.trans (hupper x hxB)) le_rfl
  let c : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  have hc : 0 < c := by dsimp [c]; positivity
  have hMeasure : topMeasure hv =
      ENNReal.ofReal (c * r ^ n) • (volume : Measure (ComplexModel n)).restrict B := by
    rw [topMeasure_add_const hp, topMeasure_const_mul hq hr, topMeasure_norm_sq,
      smul_smul, ← ENNReal.ofReal_mul (pow_nonneg hr.le n), mul_comm]
  have hineq := (measure_mono (μ := topMeasure hv) hD).trans (hcomp.trans htail)
  rw [hMeasure, Measure.smul_apply, smul_eq_mul] at hineq
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)).mpr
  have hineq' := (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)).mp hineq
  change (volume.restrict B) D * ENNReal.ofReal (c * r ^ (n + 1)) ≤ boundedEnergy hu
  rw [pow_succ, ← mul_assoc, ENNReal.ofReal_mul (by positivity : 0 ≤ c * r ^ n),
    ← mul_assoc, mul_comm ((volume.restrict B) D)]
  exact hineq'

/-- A quadratic comparison potential bounds the volume of every strict
negative sublevel by a constant times the energy and the level to power `-(n+1)`. -/
theorem volume_sublevel_le (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) {t : ℝ} (ht : 0 < t) :
    (volume : Measure (ComplexModel n)).restrict (complexUnitBall n)
        {x ∈ complexUnitBall n | u x < ((-t : ℝ) : EReal)} ≤
      energy hu / ENNReal.ofReal (((n.factorial : ℝ) / Real.pi ^ n) * (t / 4) ^ (n + 1)) := by
  obtain ⟨p⟩ := hu.2
  let B := complexUnitBall n
  let A (j : ℕ) : Set (ComplexModel n) := {x ∈ B | p.term j x < -t}
  have hmono : Monotone A := fun i j hij x hx => ⟨hx.1, (p.antitone x hx.1 hij).trans_lt hx.2⟩
  have hEq : (⋃ j, A j) = {x ∈ B | u x < ((-t : ℝ) : EReal)} := by
    ext x
    rw [mem_iUnion]
    constructor
    · rintro ⟨j, hx⟩
      exact ⟨hx.1, (p.le_term j x hx.1).trans_lt (EReal.coe_lt_coe_iff.mpr hx.2)⟩
    · intro hx
      obtain ⟨j, hj⟩ := ((p.pointwise x hx.1).eventually_lt_const hx.2).exists
      exact ⟨j, hx.1, EReal.coe_lt_coe_iff.mp hj⟩
  rw [← hEq, hmono.measure_iUnion]
  apply iSup_le
  intro j
  exact (volume_sublevel_bounded (p.term_mem j) ht).trans
    (ENNReal.div_le_div_right ((le_iSup (fun j => boundedEnergy (p.term_mem j)) j).trans_eq
      (energy_eq_iSup hn hu p).symm) _)

end KEBall.Cegrell
