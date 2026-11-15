import KEBall.DirichletSecondDiscreteConsequences
import KEBall.DirichletSecondDifferenceLimit
import KEBall.DirichletFatouEnergy

/-!
# The actual second angular derivative of the continuous Hessian is in L2

Only interior differentiability identifies the limit. Integrability up to
boundary is proved by Fatou from the normalized discrete estimates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

theorem contDiffOn_dirichletWithinRealHessian_ball {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) :
    ContDiffOn ℝ ∞ (dirichletWithinRealHessian u) (unitBall n) := by
  have hH : ContDiffOn ℝ ∞ (realHessian u) (unitBall n) :=
    fun x hx => (realHessian_contDiffAt (hu.contDiffAt (isOpen_ball.mem_nhds hx))).contDiffWithinAt
  exact hH.congr (fun x hx => dirichletWithinRealHessian_eq_on_ball u hx)

theorem memLp_dirichlet_angular_second_withinHessian_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ (dirichletWithinRealHessian u) y (S y)) x (S x))
      2 ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨δ, hδ, C, hC, hBound⟩ :=
    exists_dirichlet_unitary_spatial_second_hessian_uniform_L2_bound
      hn hu huS hu0 hPos hf hEq S hS hJ
  let H := dirichletWithinRealHessian u
  let G (x : E n) := fderiv ℝ (fun y => fderiv ℝ H y (S y)) x (S x)
  let t (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let P (m : ℕ) (x : E n) :=
    ‖dirichletFieldDifference (orthogonalFlow S hS (t m)) (t m)
      (dirichletFieldDifference (orthogonalFlow S hS (t m)) (t m) H) x‖ ^ 2
  have htPos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have ht : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htPunct : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun m => (htPos m).ne')⟩
  have hSmall : ∀ᶠ m in atTop, |t m| < δ := by
    have h := ht.abs.eventually_lt_const (show |(0 : ℝ)| < δ by simpa using hδ)
    exact h
  have hH := continuousOn_dirichletWithinRealHessian hu
  have hHS := contDiffOn_dirichletWithinRealHessian_ball huS
  have hG₁S : ContDiffOn ℝ ∞ (fun y => fderiv ℝ H y (S y)) (unitBall n) :=
    (hHS.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply S.contDiff.contDiffOn
  have hGS : ContDiffOn ℝ ∞ G (unitBall n) :=
    (hG₁S.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply S.contDiff.contDiffOn
  have hG : AEStronglyMeasurable G ((volume0 n).restrict (unitBall n)) :=
    hGS.continuousOn.aestronglyMeasurable measurableSet_ball
  have hPC (m : ℕ) : ContinuousOn (P m) (closedUnitBall n) :=
    ((continuousOn_dirichletFieldDifference _ (t m)
      (continuousOn_dirichletFieldDifference _ (t m) hH)).norm).pow 2
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt (m : ℕ) : IntegrableOn (P m) (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn (hPC m) 1).integrable le_rfl
  have hLim : ∀ᵐ x ∂(volume0 n).restrict (unitBall n),
      Tendsto (fun m => P m x) atTop (𝓝 (‖G x‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact ((tendsto_dirichletFieldSecondDifference_flow hHS S hS hx).comp htPunct).norm.pow 2
  have hBoundP : ∀ᶠ m in atTop, (∫ x in unitBall n, P m x ∂volume0 n) ≤ C := by
    filter_upwards [hSmall] with m hm
    exact hBound (t m) (htPos m).ne' hm
  have hEnergy := dirichlet_integrable_and_integral_le_of_ae_tendsto_nonneg hC hInt
    (hG.norm.pow 2) (fun m => Eventually.of_forall (fun x => sq_nonneg _))
    (Eventually.of_forall (fun x => sq_nonneg _)) hLim hBoundP
  exact (memLp_two_iff_integrable_sq_norm hG).mpr hEnergy.1

end KEBall
