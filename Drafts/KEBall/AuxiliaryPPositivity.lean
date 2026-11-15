import KEBall.ComplexMaximum
import KEBall.BoundarySchurValues

/-!
# Strict positivity of the concrete logarithmic auxiliary function

DRAFT: this source has not been checked by Lean in the Stage 05 environment.
The argument uses the original `IsSolution` fields and previously constructed
operators. No positivity of the auxiliary function is included as a hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set Matrix
open scoped ContDiff BigOperators Topology ComplexOrder

namespace KEBall

/-- The zero boundary value and the actual identity `L_u u = n` give the weak
maximum principle needed here, by an attained maximum on the closed ball. -/
theorem IsSolution.nonpos_closedBall {n : ℕ} (hn : 0 < n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n}
    (hp : p ∈ closedUnitBall n) : u p ≤ 0 := by
  have hucont : ContinuousOn u (closedUnitBall n) :=
    fun y hy => (hu.2.1.contDiffAt hy).continuousAt.continuousWithinAt
  have hnonempty : (closedUnitBall n).Nonempty :=
    ⟨0, by simp [closedUnitBall]⟩
  by_contra hnot
  have hup : 0 < u p := lt_of_not_ge hnot
  obtain ⟨q, hq, hqmax⟩ :=
    (isCompact_closedBall (0 : E n) 1).exists_isMaxOn hnonempty hucont
  have huq : 0 < u q := hup.trans_le (hqmax hp)
  have hqint : q ∈ unitBall n := by
    by_contra hqnot
    have hqnorm : ‖q‖ ≤ 1 := by
      simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hq
    have hqnorm' : ¬ ‖q‖ < 1 := by
      simpa [unitBall, Metric.mem_ball, dist_zero_right] using hqnot
    have hqsphere : q ∈ unitSphere n := by
      simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using
        le_antisymm hqnorm (le_of_not_gt hqnorm')
    rw [hu.2.2.2.2 q hqsphere] at huq
    exact (lt_irrefl 0) huq
  have hmax : IsLocalMax u q :=
    hqmax.isLocalMax
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hqint)
        Metric.ball_subset_closedBall)
  have hL : complexLaplacian u u q ≤ 0 :=
    complexLaplacian_nonpos_of_isLocalMax (hu.2.2.1 q hqint)
      (hu.2.1.contDiffAt hq) hmax
  rw [hu.complexLaplacian_self hq] at hL
  have hdim : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (not_le_of_gt hdim) hL

/-- An interior zero would itself be a local maximum, contradicting `L_u u=n`.
This step does not invoke an unformalized strong maximum principle. -/
theorem IsSolution.neg_unitBall {n : ℕ} (hn : 0 < n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) : u x < 0 := by
  have hxclosed : x ∈ closedUnitBall n := Metric.ball_subset_closedBall hx
  by_contra hnot
  have hzero : u x = 0 :=
    le_antisymm (hu.nonpos_closedBall hn hxclosed) (le_of_not_gt hnot)
  have hmaxOn : IsMaxOn u (closedUnitBall n) x := by
    intro y hy
    change u y ≤ u x
    rw [hzero]
    exact hu.nonpos_closedBall hn hy
  have hmax : IsLocalMax u x :=
    hmaxOn.isLocalMax
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hx)
        Metric.ball_subset_closedBall)
  have hL : complexLaplacian u u x ≤ 0 :=
    complexLaplacian_nonpos_of_isLocalMax (hu.2.2.1 x hx)
      (hu.2.1.contDiffAt hxclosed) hmax
  rw [hu.complexLaplacian_self hxclosed] at hL
  have hdim : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (not_le_of_gt hdim) hL

/-- The transpose in `inverseCoefficient` is accounted for by interchanging
both finite sums; the resulting expression is the usual Hermitian pairing. -/
theorem gradientNormSq_eq_inverse_pairing {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) :
    gradientNormSq u x =
      (star (fun i : Fin n => partialZ i (fun y => (u y : ℂ)) x) ⬝ᵥ
        ((complexHessian u x)⁻¹.mulVec
          (fun i : Fin n => partialZ i (fun y => (u y : ℂ)) x))).re := by
  unfold gradientNormSq inverseCoefficient
  rw [Finset.sum_comm]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [partialBar_ofReal hu]
  ring

theorem gradientNormSq_nonneg_of_posDef {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (hpos : (complexHessian u x).PosDef) :
    0 ≤ gradientNormSq u x := by
  rw [gradientNormSq_eq_inverse_pairing hu]
  let p : Fin n → ℂ := fun i => partialZ i (fun y => (u y : ℂ)) x
  change 0 ≤ (star p ⬝ᵥ ((complexHessian u x)⁻¹.mulVec p)).re
  by_cases hp : p = 0
  · simp [hp]
  · exact (hpos.inv.re_dotProduct_pos hp).le

theorem IsSolution.gradientNormSq_nonneg_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) : 0 ≤ gradientNormSq u x :=
  gradientNormSq_nonneg_of_posDef
    ((hu.2.1.contDiffAt hx).differentiableAt (by simp))
    (hu.hessian_posDef_closedBall hx)

theorem IsSolution.expWeight_gt_one_unitBall {n : ℕ} (hn : 0 < n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) : 1 < expWeight u x := by
  unfold expWeight
  apply Real.one_lt_exp_iff.mpr
  exact div_pos (neg_pos.mpr (hu.neg_unitBall hn hx)) (by positivity)

theorem IsSolution.auxiliaryP_gt_one_unitBall {n : ℕ} (hn : 0 < n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) : 1 < auxiliaryP u x := by
  have he := hu.expWeight_gt_one_unitBall hn hx
  have hq := hu.gradientNormSq_nonneg_closedBall (Metric.ball_subset_closedBall hx)
  have hquot : 0 ≤ gradientNormSq u x / (n + 1 : ℝ) :=
    div_nonneg hq (by positivity)
  have hprod : 0 ≤ expWeight u x * (gradientNormSq u x / (n + 1 : ℝ)) :=
    mul_nonneg (le_of_lt (lt_trans (by norm_num) he)) hquot
  unfold auxiliaryP
  nlinarith

theorem IsSolution.auxiliaryP_on_sphere {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    auxiliaryP u x = 1 + gradientNormSq u x / (n + 1 : ℝ) := by
  simp [auxiliaryP, expWeight, hu.2.2.2.2 x hx]

theorem IsSolution.auxiliaryP_gt_one_sphere {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) : 1 < auxiliaryP u x := by
  have hq : 0 < gradientNormSq u x := by
    rw [hu.gradientNormSq_on_sphere hn hx]
    exact div_pos (pow_pos (hu.boundarySlope_pos hn hx) _) hu.1
  rw [hu.auxiliaryP_on_sphere hx]
  exact lt_add_of_pos_right _ (div_pos hq (by positivity))

/-- The first conjunct of the frozen `LogarithmicFluxStatement`, proved from
`IsSolution`; the interior and boundary mechanisms are distinct. -/
theorem IsSolution.auxiliaryP_gt_one_closedBall {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) : 1 < auxiliaryP u x := by
  by_cases hxint : x ∈ unitBall n
  · exact hu.auxiliaryP_gt_one_unitBall (by omega) hxint
  · have hxnorm : ‖x‖ ≤ 1 := by
      simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
    have hxnorm' : ¬ ‖x‖ < 1 := by
      simpa [unitBall, Metric.mem_ball, dist_zero_right] using hxint
    have hxsphere : x ∈ unitSphere n := by
      simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using
        le_antisymm hxnorm (le_of_not_gt hxnorm')
    exact hu.auxiliaryP_gt_one_sphere hn hxsphere

theorem IsSolution.auxiliaryP_sub_one_pos_closedBall {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) : 0 < auxiliaryP u x - 1 :=
  sub_pos.mpr (hu.auxiliaryP_gt_one_closedBall hn hx)

#print axioms IsSolution.nonpos_closedBall
#print axioms IsSolution.neg_unitBall
#print axioms IsSolution.gradientNormSq_nonneg_closedBall
#print axioms IsSolution.auxiliaryP_gt_one_closedBall

end KEBall
