import KEBall.DirichletSecondDifferenceLimit
import Mathlib.Algebra.Group.ForwardDiff

/-! The genuine arbitrary-order forward quotient limit, with all Taylor cancellations verified. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open Filter Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

noncomputable def dirichletForwardWeight (k i : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ)

theorem dirichlet_forward_weight_moment (k j : ℕ) (hj : j ≤ k) :
    (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i * (i : ℝ) ^ j) =
      if j = k then (k.factorial : ℝ) else 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℝ) (fun x : ℝ => x ^ j) k 0
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast] at h
  by_cases he : j = k
  · subst j
    rw [fwdDiff_iter_eq_factorial] at h
    simpa only [dirichletForwardWeight, if_pos rfl, ite_true, Pi.natCast_apply] using h.symm
  · have hjk : j < k := lt_of_le_of_ne hj he
    rw [fwdDiff_iter_pow_eq_zero_of_lt hjk] at h
    simpa only [dirichletForwardWeight, if_neg he, Pi.zero_apply] using h.symm

theorem dirichlet_forward_weight_taylor {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : ℝ → V) (k : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • taylorWithinEval F k univ 0 (i * t)) =
      t ^ k • iteratedDeriv k F 0 := by
  simp only [taylor_within_apply, sub_zero, iteratedDerivWithin_univ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hTerm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      (∑ i ∈ Finset.range (k + 1),
        (dirichletForwardWeight k i * ((j.factorial : ℝ)⁻¹ * ((i : ℝ) * t) ^ j)) • iteratedDeriv j F 0) =
      (((j.factorial : ℝ)⁻¹ * t ^ j) *
        (if j = k then (k.factorial : ℝ) else 0)) • iteratedDeriv j F 0 := by
    rw [← Finset.sum_smul]
    congr 1
    calc
      _ = ((j.factorial : ℝ)⁻¹ * t ^ j) *
          (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i * (i : ℝ) ^ j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow]
        ring
      _ = _ := by rw [dirichlet_forward_weight_moment k j (by have h := Finset.mem_range.mp hj; omega)]
  rw [Finset.sum_congr rfl hTerm, Finset.sum_eq_single k]
  · simp only [if_pos rfl, ite_true]
    have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    congr 1
    field_simp
    <;> ring
  · intro j hj hjk
    simp only [if_neg hjk, mul_zero, zero_smul]
  · intro hk
    exact (hk (Finset.mem_range.mpr (Nat.lt_succ_self k))).elim

theorem tendsto_dirichlet_higher_forward_quotient {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ → V} (k : ℕ) (hF : ContDiff ℝ k F) :
    Tendsto (fun t : ℝ => (t ^ k)⁻¹ •
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • F (i * t)))
      (𝓝[≠] 0) (𝓝 (iteratedDeriv k F 0)) := by
  let P (t : ℝ) := taylorWithinEval F k univ 0 t
  let r (t : ℝ) := (t ^ k)⁻¹ • (F t - P t)
  have hr : Tendsto r (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [nhdsWithin_univ, sub_zero, r, P] using
      taylor_tendsto (f := F) (n := k) convex_univ (mem_univ (0 : ℝ)) hF.contDiffOn
  have hLimit : Tendsto (fun t : ℝ =>
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • ((i : ℝ) ^ k • r (i * t))) +
        iteratedDeriv k F 0) (𝓝[≠] 0) (𝓝 (iteratedDeriv k F 0)) := by
    have hMul (i : ℕ) : Tendsto (fun t : ℝ => (i : ℝ) * t) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero, id_eq] using (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)))
    have h := (tendsto_finset_sum (Finset.range (k + 1)) (fun i _ =>
      ((hr.comp (hMul i)).const_smul ((i : ℝ) ^ k)).const_smul (dirichletForwardWeight k i))).add_const (iteratedDeriv k F 0)
    simpa only [Function.comp_def, smul_zero, Finset.sum_const_zero, zero_add] using h.mono_left nhdsWithin_le_nhds
  apply hLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hScale (a : ℝ) : a ^ k • r (a * t) = (t ^ k)⁻¹ • (F (a * t) - P (a * t)) := by
    by_cases ha : a = 0
    · subst a
      simp only [r, P, zero_mul, taylorWithinEval_self, sub_self, smul_zero]
    · dsimp only [r]
      rw [smul_smul]
      congr 1
      field_simp [ha, ht0]
      <;> ring
  have hTaylor : (t ^ k)⁻¹ •
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • P (i * t)) = iteratedDeriv k F 0 := by
    rw [dirichlet_forward_weight_taylor, smul_smul, inv_mul_cancel₀ (pow_ne_zero k ht0), one_smul]
  have hResidual : (t ^ k)⁻¹ •
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • (F (i * t) - P (i * t))) =
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • ((i : ℝ) ^ k • r (i * t))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_comm, hScale]
  have hSplit : (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • (F (i * t) - P (i * t))) =
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • F (i * t)) -
      (∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i • P (i * t)) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [hSplit, smul_sub, hTaylor] at hResidual
  exact (eq_add_of_sub_eq hResidual).symm

end KEBall
