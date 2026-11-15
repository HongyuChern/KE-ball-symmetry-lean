import KEBall.FiberEnergyVariation

/-!
# Smooth integration over the fixed fiber ball
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

universe u

variable {n : ℕ}
variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private noncomputable def fiberIntegralDerivative (F : P × E n → V) :
    P × E n → P →L[ℝ] V :=
  fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ P (E n))

omit [ProperSpace P] [CompleteSpace V] in
private theorem contDiff_fiberIntegralDerivative {F : P × E n → V} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fiberIntegralDerivative F) := by
  let L := (ContinuousLinearMap.compL ℝ P (P × E n) V).flip
    (ContinuousLinearMap.inl ℝ P (E n))
  exact L.contDiff.comp (hF.fderiv_right (by simp))

set_option maxHeartbeats 750000 in
private theorem hasFDerivAt_fiberIntegral (hn : 0 < n)
    {F : P × E n → V} (hF : ContDiff ℝ ∞ F) (p : P) :
    HasFDerivAt (fun q => ∫ x in unitBall n, F (q, x) ∂volume0 n)
      (∫ x in unitBall n, fiberIntegralDerivative F (p, x) ∂volume0 n) p := by
  let μ := (volume0 n).restrict (unitBall n)
  have hB : MeasurableSet (unitBall n) := measurableSet_ball
  have hfin : volume0 n (unitBall n) ≠ ⊤ := by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top
  have hD := (contDiff_fiberIntegralDerivative hF).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p 1).prod (isCompact_closedBall (0 : E n) 1))
    |>.exists_bound_of_continuousOn hD.continuousOn
  have hi {W : Type u} [NormedAddCommGroup W] {G : P × E n → W}
      (hG : Continuous G) (q : P) : Integrable (fun x => G (q, x)) μ :=
    ((hG.comp (continuous_const.prodMk continuous_id)).continuousOn).integrableOn_of_subset_isCompact
      (isCompact_closedBall _ _) hB ball_subset_closedBall hfin
  have hdiff (q : P) (x : E n) :
      HasFDerivAt (fun y => F (y, x)) (fiberIntegralDerivative F (q, x)) q :=
    (hF.differentiable (by simp) (q, x)).hasFDerivAt.comp q (hasFDerivAt_prodMk_left q x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun q x => F (q, x)) (F' := fun q x => fiberIntegralDerivative F (q, x))
    (ball_mem_nhds p zero_lt_one)
    (Eventually.of_forall fun q => (hi hF.continuous q).aestronglyMeasurable)
    (hi hF.continuous p) (hi (G := fiberIntegralDerivative F) hD p).aestronglyMeasurable
    ((ae_restrict_mem (μ := volume0 n) hB).mono
      fun x hx q hq => hC (q, x) ⟨ball_subset_closedBall hq, ball_subset_closedBall hx⟩)
    (integrableOn_const hfin) (Eventually.of_forall fun x q _ => hdiff q x)

private theorem contDiff_nat_fiberIntegral (hn : 0 < n) (k : ℕ)
    {F : P × E n → V} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ k (fun q => ∫ x in unitBall n, F (q, x) ∂volume0 n) := by
  induction k generalizing V with
  | zero =>
    have hd : Differentiable ℝ (fun q => ∫ x in unitBall n, F (q, x) ∂volume0 n) :=
      fun p => (hasFDerivAt_fiberIntegral hn hF p).differentiableAt
    exact contDiff_zero.mpr hd.continuous
  | succ k ih =>
    have hdiff : Differentiable ℝ (fun q => ∫ x in unitBall n, F (q, x) ∂volume0 n) :=
      fun p => (hasFDerivAt_fiberIntegral hn hF p).differentiableAt
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨hdiff, by simp, ?_⟩
    have he : fderiv ℝ (fun q => ∫ x in unitBall n, F (q, x) ∂volume0 n) =
        fun q => ∫ x in unitBall n, fiberIntegralDerivative F (q, x) ∂volume0 n :=
      funext fun p => (hasFDerivAt_fiberIntegral hn hF p).fderiv
    rw [he]
    exact ih (contDiff_fiberIntegralDerivative hF)

/-- Integrating a smooth family on the fixed ball preserves smoothness
in the parameter. -/
theorem contDiff_fiberIntegral (hn : 0 < n) {F : P × E n → V} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun q => ∫ x in unitBall n, F (q, x) ∂volume0 n) :=
  contDiff_infty.mpr fun k => contDiff_nat_fiberIntegral hn k hF

end KEBall.MoserTrudinger
