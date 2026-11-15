/-
Copyright 2026 The DifferentialGeometry contributors.
Released under Apache-2.0; see vendor/de_giorgi/LICENSE and UPSTREAM-NOTICE.
The three-factor Holder proof is adapted from qinz1yang/differential-geometry
v0.1.3, commit 7a48598d35109aa99d1cc678e2724c213cdf4ff3,
Analysis/Sobolev/GagliardoNirenberg/FiberNorm/HolderIntegrability.lean.
The manifold measure is replaced by the actual normalized ball measure;
compact continuity supplies the required MemLp hypotheses below.
-/
import KEBall.DirichletAngularIntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace KEBall

theorem dirichlet_memLp_of_continuousOn {n : ℕ} (hn : 0 < n) {F : Type*}
    [NormedAddCommGroup F] {g : E n → F} (hg : ContinuousOn g (closedUnitBall n))
    (p : ℝ≥0∞) : MemLp g p ((volume0 n).restrict (unitBall n)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hg
  have hMeas := (hg.mono ball_subset_closedBall).aestronglyMeasurable (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)
  exact MemLp.of_bound hMeas C ((ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
      fun x hx => hC x (ball_subset_closedBall hx))

theorem dirichlet_integral_three_holder_nonneg {n : ℕ} (hn : 0 < n)
    (f₁ f₂ f₃ : E n → ℝ)
    (hf₁c : ContinuousOn f₁ (closedUnitBall n))
    (hf₂c : ContinuousOn f₂ (closedUnitBall n))
    (hf₃c : ContinuousOn f₃ (closedUnitBall n))
    (hf₁0 : ∀ x, 0 ≤ f₁ x) (hf₂0 : ∀ x, 0 ≤ f₂ x) (hf₃0 : ∀ x, 0 ≤ f₃ x)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hABC : α⁻¹ + β⁻¹ + γ⁻¹ = 1) :
    ∫ x in unitBall n, f₁ x * f₂ x * f₃ x ∂volume0 n ≤
      (∫ x in unitBall n, f₁ x ^ α ∂volume0 n) ^ (1 / α) *
        ((∫ x in unitBall n, f₂ x ^ β ∂volume0 n) ^ (1 / β) *
          (∫ x in unitBall n, f₃ x ^ γ ∂volume0 n) ^ (1 / γ)) := by
  let μ := (volume0 n).restrict (unitBall n)
  set α' : ℝ := (β⁻¹ + γ⁻¹)⁻¹ with hα'def
  have hβγpos : 0 < β⁻¹ + γ⁻¹ := by positivity
  have hα'pos : 0 < α' := by rw [hα'def]; positivity
  have hα'inv : α'⁻¹ = β⁻¹ + γ⁻¹ := by rw [hα'def, inv_inv]
  have hγinv_pos : (0 : ℝ) < γ⁻¹ := by positivity
  have hβinv_pos : (0 : ℝ) < β⁻¹ := by positivity
  have hconj1 : α.HolderConjugate α' := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · have hαinv_lt : α⁻¹ < 1 := by
        have hαeq : α⁻¹ = 1 - (β⁻¹ + γ⁻¹) := by linarith [hABC]
        rw [hαeq]; linarith [hβγpos]
      have hαinv_pos : (0 : ℝ) < α⁻¹ := by positivity
      rw [← inv_inv α]
      exact one_lt_inv_iff₀.mpr ⟨hαinv_pos, hαinv_lt⟩
    · rw [hα'inv]; linarith [hABC]
  have hf23_0 : ∀ x, 0 ≤ f₂ x * f₃ x := fun x => mul_nonneg (hf₂0 x) (hf₃0 x)
  have hf1_mem : MeasureTheory.MemLp f₁ (ENNReal.ofReal α) μ :=
    dirichlet_memLp_of_continuousOn hn hf₁c _
  have hf23_mem : MeasureTheory.MemLp (fun x => f₂ x * f₃ x) (ENNReal.ofReal α') μ :=
    dirichlet_memLp_of_continuousOn hn (hf₂c.mul hf₃c) _
  have hstep1 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj1
    (f := f₁) (g := fun x => f₂ x * f₃ x)
    (MeasureTheory.ae_of_all _ hf₁0) (MeasureTheory.ae_of_all _ hf23_0) hf1_mem hf23_mem
  have hβα' : 0 < β / α' := by positivity
  have hγα' : 0 < γ / α' := by positivity
  have hf2α'_mem : MeasureTheory.MemLp (fun x => f₂ x ^ α') (ENNReal.ofReal (β / α')) μ :=
    dirichlet_memLp_of_continuousOn hn
      (hf₂c.rpow_const (fun _ _ => Or.inr hα'pos.le)) _
  have hf3α'_mem : MeasureTheory.MemLp (fun x => f₃ x ^ α') (ENNReal.ofReal (γ / α')) μ :=
    dirichlet_memLp_of_continuousOn hn
      (hf₃c.rpow_const (fun _ _ => Or.inr hα'pos.le)) _
  have hα'ne : α' ≠ 0 := ne_of_gt hα'pos
  have hconj2 : (β / α').HolderConjugate (γ / α') := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [one_lt_div hα'pos]
      have hlt : β⁻¹ < α'⁻¹ := by rw [hα'inv]; linarith [hγinv_pos]
      exact (inv_lt_inv₀ hβ hα'pos).mp hlt
    · have hsplit : α' / β + α' / γ = α' * (β⁻¹ + γ⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_add]
      rw [inv_div, inv_div, hsplit, ← hα'inv, mul_inv_cancel₀ hα'ne]
  have hstep2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj2
    (f := fun x => f₂ x ^ α') (g := fun x => f₃ x ^ α')
    (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hf₂0 x) _))
    (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hf₃0 x) _)) hf2α'_mem hf3α'_mem
  have hprod_rpow : ∀ x, (f₂ x * f₃ x) ^ α' = f₂ x ^ α' * f₃ x ^ α' :=
    fun x => Real.mul_rpow (hf₂0 x) (hf₃0 x)
  have hmulcancel : ∀ t : ℝ, α' * (t / α') = t := by
    intro t; rw [mul_comm, div_mul_cancel₀ t hα'ne]
  have hpow2 : ∀ x, (f₂ x ^ α') ^ (β / α') = f₂ x ^ β := by
    intro x
    rw [← Real.rpow_mul (hf₂0 x), hmulcancel]
  have hpow3 : ∀ x, (f₃ x ^ α') ^ (γ / α') = f₃ x ^ γ := by
    intro x
    rw [← Real.rpow_mul (hf₃0 x), hmulcancel]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow2),
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow3)] at hstep2
  set Iβ : ℝ := ∫ x, f₂ x ^ β ∂μ with hIβ
  set Iγ : ℝ := ∫ x, f₃ x ^ γ ∂μ with hIγ
  have hIβ_nn : 0 ≤ Iβ := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₂0 x) _)
  have hIγ_nn : 0 ≤ Iγ := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₃0 x) _)
  have hI23 : (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) = ∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ :=
    MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hprod_rpow)
  have hmid : (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) ^ (1 / α') ≤ Iβ ^ (1 / β) * Iγ ^ (1 / γ) := by
    rw [hI23]
    have hbase_nn : 0 ≤ ∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ :=
      MeasureTheory.integral_nonneg (fun x =>
        mul_nonneg (Real.rpow_nonneg (hf₂0 x) _) (Real.rpow_nonneg (hf₃0 x) _))
    have hα'inv_pos : 0 < 1 / α' := by positivity
    calc (∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ) ^ (1 / α')
        ≤ (Iβ ^ (1 / (β / α')) * Iγ ^ (1 / (γ / α'))) ^ (1 / α') :=
          Real.rpow_le_rpow hbase_nn hstep2 (le_of_lt hα'inv_pos)
      _ = Iβ ^ (1 / β) * Iγ ^ (1 / γ) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hIβ_nn, ← Real.rpow_mul hIγ_nn]
          have he2 : (1 / (β / α')) * (1 / α') = 1 / β := by
            rw [one_div_div]
            field_simp
          have he3 : (1 / (γ / α')) * (1 / α') = 1 / γ := by
            rw [one_div_div]
            field_simp
          rw [he2, he3]
  calc ∫ x, f₁ x * f₂ x * f₃ x ∂μ
      = ∫ x, f₁ x * (f₂ x * f₃ x) ∂μ := by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => ?_))
        ring
    _ ≤ (∫ x, f₁ x ^ α ∂μ) ^ (1 / α) * (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) ^ (1 / α') := hstep1
    _ ≤ (∫ x, f₁ x ^ α ∂μ) ^ (1 / α) * (Iβ ^ (1 / β) * Iγ ^ (1 / γ)) := by
        apply mul_le_mul_of_nonneg_left hmid
        exact Real.rpow_nonneg (MeasureTheory.integral_nonneg
          (fun x => Real.rpow_nonneg (hf₁0 x) _)) _


end KEBall
