import KEBall.DirichletAngularL2
import KEBall.DirichletTangentProjection

/-! Weak tangential second derivatives of the Dirichlet solution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- A scalar field continuous on the closed ball preserves square
integrability under multiplication on the ball. -/
theorem memLp_dirichlet_mul_of_continuousOn {n : ℕ} {c f : E n → ℝ}
    (hc : ContinuousOn c (closedUnitBall n)) (hf : MemLp f 2 ν[n]) :
    MemLp (fun x => c x * f x) 2 ν[n] := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable c ν[n] :=
    (hc.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  apply hf.of_le_mul (hm.mul hf.1)
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  change ‖c x * f x‖ ≤ C * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (ball_subset_closedBall hx)) (norm_nonneg _)

/-- Angular weak derivatives in L² give an L² weak derivative along
the scaled tangential projection of any constant direction. -/
theorem exists_memLp_dirichletTangentDerivative {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : MemLp f 2 ν[n]) (w : E n)
    (hAngular : ∀ (S : E n →L[ℝ] E n), star S = -S →
      ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * F x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * f x ∂ν[n])) :
    ∃ h : E n → ℝ, MemLp h 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * h x ∂ν[n]) =
        -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • w - inner ℝ w x • x) +
          ((1 - (2 : ℝ) * n) * inner ℝ w x) * ψ x) * f x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let S (i : Fin (2 * n)) := dirichletPlaneRotation w (b i)
  let c (i : Fin (2 * n)) : E n →L[ℝ] ℝ := innerSL ℝ (b i)
  choose F hF he using fun i => hAngular (S i) (dirichletPlaneRotation_star w (b i))
  let h (x : E n) := ∑ i, c i x * F i x
  have hh : MemLp h 2 ν[n] := memLp_finsetSum Finset.univ fun i _ =>
    memLp_dirichlet_mul_of_continuousOn (c i).continuous.continuousOn (hF i)
  refine ⟨h, hh, fun ψ => ?_⟩
  let χ (i : Fin (2 * n)) := dirichletTestMul ψ (c i).contDiff
  let D (i : Fin (2 * n)) := dirichletTestFieldDerivative (χ i) (S i) (S i).contDiff
  have hInt {f : E n → ℝ} (hf : MemLp f 2 ν[n]) (φ : 𝓓(dirichletBallOpens n, ℝ)) :
      Integrable (fun x => φ x * f x) ν[n] :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hf.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hχ (i : Fin (2 * n)) (x : E n) :
      D i x = ψ x * c i (S i x) + c i x * fderiv ℝ (ψ : E n → ℝ) x (S i x) := by
    change fderiv ℝ (fun y => ψ y * c i y) x (S i x) = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (c i).differentiableAt]
    simp
  have hSumL (x : E n) : (∑ i, χ i x * F i x) = ψ x * h x := by
    change (∑ i, (ψ x * c i x) * F i x) = _
    simp only [mul_assoc, h, Finset.mul_sum]
  have hSumD (x : E n) : (∑ i, D i x) =
      fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • w - inner ℝ w x • x) +
        ((1 - (2 : ℝ) * n) * inner ℝ w x) * ψ x := by
    simp_rw [hχ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_comm]
    have h₁ : (∑ i, c i (S i x)) = (1 - (2 : ℝ) * n) * inner ℝ w x :=
      sum_inner_dirichletPlaneRotation b w x
    rw [h₁, mul_comm (ψ x)]
    congr 1
    calc
      _ = fderiv ℝ (ψ : E n → ℝ) x (∑ i, c i x • S i x) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := congrArg (fderiv ℝ (ψ : E n → ℝ) x)
        (sum_dirichletPlaneRotation_eq_tangentProjection b w x)
  have hEqL : (∫ x, ∑ i, χ i x * F i x ∂ν[n]) = ∫ x, ψ x * h x ∂ν[n] :=
    integral_congr_ae (Eventually.of_forall hSumL)
  have hEqR : (∫ x, ∑ i, D i x * f x ∂ν[n]) =
      ∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • w - inner ℝ w x • x) +
        ((1 - (2 : ℝ) * n) * inner ℝ w x) * ψ x) * f x ∂ν[n] := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (∑ i, D i x * f x) = _
      rw [← Finset.sum_mul, hSumD]
  change (∫ x, ψ x * h x ∂ν[n]) =
    -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • w - inner ℝ w x • x) +
      ((1 - (2 : ℝ) * n) * inner ℝ w x) * ψ x) * f x ∂ν[n])
  rw [← hEqL, ← hEqR, integral_finsetSum _ (fun i _ => hInt (hF i) (χ i)),
    integral_finsetSum _ (fun i _ => hInt hf (D i)),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    he i (χ i)

/-- The derivative of a fixed weak gradient component in the projected
direction `‖x‖² w - ⟪w, x⟫ x` has an L² representative. -/
theorem exists_memLp_dirichletTangentGradient {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) (w e : E n) :
    ∃ h : E n → ℝ, MemLp h 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * h x ∂ν[n]) =
        -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • w - inner ℝ w x • x) +
          ((1 - (2 : ℝ) * n) * inner ℝ w x) * ψ x) *
            inner ℝ e ((u : DirichletBallL2Pair n).snd x) ∂ν[n]) := by
  let U := (u : DirichletBallL2Pair n).snd
  apply exists_memLp_dirichletTangentDerivative hn ((Lp.memLp U).const_inner e) w
  intro S hS
  obtain ⟨v, hv⟩ := exists_dirichletSobolev_angularDerivative_L2 hn hA hl hE hLipA hM₀ hM hu S hS
  exact ⟨fun x => inner ℝ e ((v : DirichletBallL2Pair n).snd x) - inner ℝ (S e) (U x),
    ((Lp.memLp (v : DirichletBallL2Pair n).snd).const_inner e).sub ((Lp.memLp U).const_inner (S e)),
    dirichletSobolev_integral_angularGradientComponent hn S u v hv e⟩

end KEBall
