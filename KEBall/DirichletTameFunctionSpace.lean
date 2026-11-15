import KEBall.DirichletHessianMonomialTame
import Mathlib.LinearAlgebra.Span.Basic

/-! The small-leading-coefficient energy property is stable under finite real linear combinations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem integral_dirichlet_norm_add_sq_le {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] (hn : 0 < n) {F G : E n → V}
    (hF : ContinuousOn F (closedUnitBall n)) (hG : ContinuousOn G (closedUnitBall n)) :
    (∫ x in unitBall n, ‖F x + G x‖ ^ 2 ∂volume0 n) ≤
      2 * (∫ x in unitBall n, ‖F x‖ ^ 2 ∂volume0 n) +
      2 * (∫ x in unitBall n, ‖G x‖ ^ 2 ∂volume0 n) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have h := setIntegral_mono_on (hInt ((hF.add hG).norm.pow 2))
    (hInt (((hF.norm.pow 2).const_mul 2).add ((hG.norm.pow 2).const_mul 2)))
    measurableSet_ball (fun x _ => by
      simp only [Pi.add_apply, Pi.pow_apply]
      have hN := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (F x) (G x)) 2
      nlinarith only [hN, sq_nonneg (‖F x‖ - ‖G x‖)])
  simp only [Pi.add_apply, Pi.pow_apply] at h
  have hFI : IntegrableOn (fun x => ‖F x‖ ^ 2) (unitBall n) (volume0 n) := hInt (hF.norm.pow 2)
  have hGI : IntegrableOn (fun x => ‖G x‖ ^ 2) (unitBall n) (volume0 n) := hInt (hG.norm.pow 2)
  rw [integral_add (hFI.const_mul 2) (hGI.const_mul 2), integral_const_mul, integral_const_mul] at h
  exact h

theorem integral_dirichlet_norm_real_smul_sq {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (F : E n → V) :
    (∫ x in unitBall n, ‖c • F x‖ ^ 2 ∂volume0 n) =
      c ^ 2 * (∫ x in unitBall n, ‖F x‖ ^ 2 ∂volume0 n) := by
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, integral_const_mul]

noncomputable def dirichletTameFunctionSpace {n : ℕ} (hn : 0 < n)
    (Top Low : ℝ → ℝ) (hTop : ∀ t, 0 ≤ Top t) : Submodule ℝ (ℝ → E n → ℂ) where
  carrier := {G | (∀ t : ℝ, t ≠ 0 → ContinuousOn (G t) (closedUnitBall n)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n, ‖G t x‖ ^ 2 ∂volume0 n) ≤ ε * Top t + C * Low t + C}
  zero_mem' := by
    constructor
    · intro t ht
      exact continuousOn_const
    · intro ε hε
      refine ⟨0, le_rfl, ?_⟩
      intro t ht
      simpa only [Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
        zero_mul, add_zero] using mul_nonneg hε.le (hTop t)
  add_mem' := by
    rintro F G ⟨hFC, hF⟩ ⟨hGC, hG⟩
    constructor
    · intro t ht
      exact (hFC t ht).add (hGC t ht)
    · intro ε hε
      obtain ⟨A, hA, hFA⟩ := hF (ε / 4) (by positivity)
      obtain ⟨B, hB, hGB⟩ := hG (ε / 4) (by positivity)
      refine ⟨2 * A + 2 * B, by positivity, ?_⟩
      intro t ht
      have hAdd := integral_dirichlet_norm_add_sq_le hn (hFC t ht) (hGC t ht)
      have h := hAdd.trans (add_le_add (mul_le_mul_of_nonneg_left (hFA t ht) (by positivity))
        (mul_le_mul_of_nonneg_left (hGB t ht) (by positivity)))
      exact h.trans_eq (by ring)
  smul_mem' := by
    rintro c F ⟨hFC, hF⟩
    constructor
    · intro t ht
      exact (hFC t ht).const_smul c
    · intro ε hε
      let ε' := ε / (c ^ 2 + 1)
      have hε' : 0 < ε' := div_pos hε (by positivity)
      obtain ⟨A, hA, hFA⟩ := hF ε' hε'
      refine ⟨c ^ 2 * A, mul_nonneg (sq_nonneg _) hA, ?_⟩
      intro t ht
      have hCap : c ^ 2 * ε' ≤ ε := by
        calc
          c ^ 2 * ε' ≤ (c ^ 2 + 1) * ε' := mul_le_mul_of_nonneg_right (by linarith) hε'.le
          _ = ε := mul_div_cancel₀ ε (by positivity : c ^ 2 + 1 ≠ 0)
      change (∫ x in unitBall n, ‖c • F t x‖ ^ 2 ∂volume0 n) ≤ _
      rw [integral_dirichlet_norm_real_smul_sq]
      refine (mul_le_mul_of_nonneg_left (hFA t ht) (sq_nonneg _)).trans ?_
      simp only [mul_add, ← mul_assoc]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCap (hTop t)) le_rfl) le_rfl

end KEBall
