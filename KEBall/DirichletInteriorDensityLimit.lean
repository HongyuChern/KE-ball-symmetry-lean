import KEBall.DirichletLocalHessianLimit
import KEBall.DirichletLocalHolder
import KEBall.DirichletInteriorHessianEquation
import KEBall.DirichletBoundaryHessianCluster
import KEBall.DirichletSobolevClassical

/-! Passage to the classical determinant equation from actual smooth
solutions with a common local Hessian modulus and a genuine density limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 750000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall
local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem interior_classical_limit_of_uniform_firstJet_and_local_hessian_holder
    {n : ℕ} {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hU : TendstoUniformlyOn u w atTop (closedUnitBall n))
    (hG : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) G atTop (closedUnitBall n))
    (hLocal : ∀ p ∈ unitBall n, ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ unitBall n ∧
      ∃ K : ℝ≥0, ∀ j,
        (∀ x ∈ closedBall p r, ‖fderiv ℝ (fderiv ℝ (u j)) x‖ ≤ K) ∧
        HolderOnWith K α (fderiv ℝ (fderiv ℝ (u j))) (closedBall p r))
    {f : ℕ → E n → ℝ} {f0 : E n → ℝ}
    (hf : ContinuousOn f0 (unitBall n)) (hfPos : ∀ x ∈ unitBall n, 0 < f0 x)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).det.re = f j x)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun j => f j x) atTop (𝓝 (f0 x))) :
    ContDiffOn ℝ 2 w (unitBall n) ∧
      (∀ p ∈ unitBall n, HasDirichletHolderAt 2 α w p) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = f0 x) := by
  have hData (p : E n) (hp : p ∈ unitBall n) :
      HasDirichletHolderAt 2 α w p ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => fderiv ℝ (fderiv ℝ (u (φ j))) p) atTop
          (𝓝 (fderiv ℝ (fderiv ℝ w) p)) := by
    obtain ⟨r, hr, hSub, K, hK⟩ := hLocal p hp
    have hSubC := hSub.trans ball_subset_closedBall
    obtain ⟨hw2, hwH, _, φ, hφ, hφH⟩ :=
      local_C2_of_uniform_firstJet_and_hessian_holder hu hα
        (hU.mono hSubC) (hG.mono hSubC) (fun j => (hK j).1) (fun j => (hK j).2)
    exact ⟨⟨r, hr, hw2, K, dirichlet_holderOn_iterated_two_iff.mpr hwH⟩,
      φ, hφ, hφH.tendsto_at (mem_ball_self hr)⟩
  have hw2 : ContDiffOn ℝ 2 w (unitBall n) :=
    fun p hp => (hData p hp).1.contDiffAt.contDiffWithinAt
  have hAe : ∀ᵐ x ∂ν[n], (complexHessian w x).PosDef ∧
      (complexHessian w x).det.re = f0 x := by
    filter_upwards [hLim, ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hxL hx
    obtain ⟨φ, hφ, hH⟩ := (hData x hx).2
    have hwx := hw2.contDiffAt (isOpen_ball.mem_nhds hx)
    have hHC := (continuous_dirichlet_complexHessianOfRealBilinear n).tendsto
      (fderiv ℝ (fderiv ℝ w) x) |>.comp hH
    have hComplex : Tendsto (fun j => complexHessian (u (φ j)) x) atTop
        (𝓝 (complexHessian w x)) := by
      rw [← complexHessianOfRealBilinear_eq hwx]
      apply hHC.congr'
      exact Eventually.of_forall fun j =>
        complexHessianOfRealBilinear_eq ((hu (φ j)).contDiffAt.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    have hSemi := dirichlet_posSemidef_of_tendsto_matrix hComplex
      (Eventually.of_forall fun j => (huP (φ j) x hx).posSemidef)
    have hDetL := ((Complex.continuous_re.comp continuous_id.matrix_det).tendsto
      (complexHessian w x)).comp hComplex
    have hFL := (hxL.comp hφ.tendsto_atTop).congr
      (fun j => (hEq (φ j) x hx).symm)
    have hDet : (complexHessian w x).det.re = f0 x := tendsto_nhds_unique hDetL hFL
    refine ⟨hSemi.posDef_iff_det_ne_zero.mpr ?_, hDet⟩
    intro hz
    rw [hz, Complex.zero_re] at hDet
    exact (hfPos x hx).ne hDet
  have hPoint : EqOn (fun x => (complexHessian w x).det.re) f0 (unitBall n) :=
    Measure.eqOn_open_of_ae_eq (hAe.mono fun _ hx => hx.2) isOpen_ball
      (continuousOn_det_complexHessian_C2 hw2) hf
  have hPos := dirichlet_complexHessian_posDef_of_interior_C2_ae hw2
    (hAe.mono fun _ hx => hx.1) (fun x hx => by
      change 0 < (fun y => (complexHessian w y).det.re) x
      rw [hPoint hx]
      exact hfPos x hx)
  exact ⟨hw2, fun p hp => (hData p hp).1, hPos, fun x hx => hPoint hx⟩

end KEBall
