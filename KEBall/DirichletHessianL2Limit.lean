import KEBall.DirichletHessianStability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Strong and almost-everywhere compactness of complex Hessians. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- The finite-dimensional Euclidean space of complex Hessian entries. -/
abbrev DirichletHessianCoordinates (n : ℕ) := EuclideanSpace ℂ (Fin n × Fin n)

/-- The entries of a complex Hessian, equipped with the Euclidean norm. -/
def dirichletHessianCoordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : DirichletHessianCoordinates n :=
  WithLp.toLp 2 fun ij => A ij.1 ij.2

private theorem hessianCoordinates_sub_norm_sq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    ‖dirichletHessianCoordinates A - dirichletHessianCoordinates B‖ ^ 2 = ∑ i, ∑ j, ‖(A - B) i j‖ ^ 2 := by
  rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
  rfl

private theorem dirichletL2_norm_sq_complex {n : ℕ} (w : DirichletBallL2 n (DirichletHessianCoordinates n)) :
    ‖w‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂ν[n] := by
  rw [← real_inner_self_eq_norm_sq w, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- A pairwise squared-distance estimate tending to zero gives strong
(L^2) convergence, with a subsequence converging almost everywhere. -/
theorem exists_complexHessian_L2_limit_of_pairwise_integral_bound {n : ℕ} (hn : 0 < n)
    {A : ℕ → E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ j i k, ContinuousOn (fun x => A j x i k) (closedUnitBall n))
    (hPair : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      (∫ x in unitBall n, ∑ i, ∑ l, ‖(A j x - A k x) i l‖ ^ 2 ∂volume0 n) < δ) :
    ∃ H : DirichletBallL2 n (DirichletHessianCoordinates n),
      (∃ Q : ℕ → DirichletBallL2 n (DirichletHessianCoordinates n), Tendsto Q atTop (𝓝 H) ∧
        ∀ j, Q j =ᵐ[ν[n]] fun x => dirichletHessianCoordinates (A j x)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ x ∂ν[n], Tendsto (fun j => dirichletHessianCoordinates (A (φ j) x)) atTop (𝓝 (H x)) := by
  have hC (j : ℕ) : ContinuousOn (fun x => dirichletHessianCoordinates (A j x)) (closedUnitBall n) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin n => ℂ)).comp_continuousOn
    exact continuousOn_pi.mpr fun ij => hA j ij.1 ij.2
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hLp (j : ℕ) : MemLp (fun x => dirichletHessianCoordinates (A j x)) 2 ν[n] := by
    obtain ⟨C, hC'⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn (hC j)
    have hMeas := ((hC j).mono ball_subset_closedBall).aestronglyMeasurable (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)
    exact (memLp_top_of_bound (μ := ν[n]) hMeas C ((ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
        fun x hx => hC' x (ball_subset_closedBall hx))).mono_exponent (by simp)
  let Q (j : ℕ) := (hLp j).toLp _
  have hQ (j : ℕ) : Q j =ᵐ[ν[n]] fun x => dirichletHessianCoordinates (A j x) :=
    MemLp.coeFn_toLp (hLp j)
  have hCauchy : CauchySeq Q := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hPair (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun j hj k hk => ?_⟩
    rw [dist_eq_norm]
    have he : ‖Q j - Q k‖ ^ 2 =
        ∫ x in unitBall n, ∑ i, ∑ l, ‖(A j x - A k x) i l‖ ^ 2 ∂volume0 n := by
      rw [dirichletL2_norm_sq_complex]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Q j) (Q k), hQ j, hQ k] with x hSub hj hk
      rw [hSub, Pi.sub_apply, hj, hk, hessianCoordinates_sub_norm_sq]
    exact lt_of_not_ge fun h => (not_lt_of_ge (pow_le_pow_left₀ hε.le h 2))
      (he ▸ hN j hj k hk)
  obtain ⟨H, hT⟩ := cauchySeq_tendsto_of_complete hCauchy
  obtain ⟨φ, hφ, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  refine ⟨H, ⟨Q, hT, hQ⟩, φ, hφ, ?_⟩
  filter_upwards [hAE, ae_all_iff.mpr hQ] with x hx hEq
  exact hx.congr (fun j => hEq (φ j))

end KEBall
