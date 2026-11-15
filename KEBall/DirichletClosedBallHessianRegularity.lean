import KEBall.DirichletRotationBoundaryRegularity
import KEBall.DirichletBoundaryHessianCluster
import KEBall.DirichletTangentGenerator
import KEBall.DirichletClosedBallC2Extension

/-!
# Closed-ball Hessian regularity for the actual first jet

The rotation traces provide every tangent entry at a sphere point.  Bounded
interior Hessians, positivity and the exact determinant then give a unique
full Hessian limit.  Extending this limit yields closed-ball C2 regularity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix NNReal Topology

namespace KEBall

theorem exists_dirichlet_rotation_hessian_trace {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hw2 : ContDiffOn ℝ 2 w (unitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (T : E n →L[ℝ] E n) {p : E n} (hp : p ∈ unitSphere n)
    {Q : E n →L[ℝ] ℝ}
    (hQ : Tendsto (fderiv ℝ (fun y => G y (T y))) (𝓝[unitBall n] p) (𝓝 Q)) :
    Tendsto (fun x => realHessian w x (T x)) (𝓝[unitBall n] p)
      (𝓝 (Q - (G p).comp T)) := by
  have hComp : Tendsto (fun x => (G x).comp T) (𝓝[unitBall n] p) (𝓝 ((G p).comp T)) :=
    ((hLip.continuousOn p (sphere_subset_closedBall hp)).clm_comp
      continuous_const.continuousWithinAt).mono ball_subset_closedBall
  apply (hQ.sub hComp).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  ext v
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply]
  rw [fderiv_dirichlet_firstJet_linearField
    (differentiableAt_dirichlet_firstJet_of_interiorC2 hw2 hD hx),
    fderiv_dirichlet_firstJet_eq_realHessian hD hx, add_sub_cancel_right]
  exact ((hw2.contDiffAt (isOpen_ball.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)).eq v (T x)

theorem exists_dirichlet_actual_boundary_hessian_limits {n : ℕ} (hn : 0 < n)
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hw2 : ContDiffOn ℝ 2 w (unitBall n))
    (hDclosed : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    (hHolder : ∃ β H : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 ≤ H ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤ (H * (4 / R : ℝ) ^ β) * ‖x - y‖ ^ β)
    (hPower : HasDirichletRotationBoundaryPower G)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x)
    (hPos : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
    (hDet : ∀ x ∈ unitBall n, (complexHessian w x).det.re = f x) :
    ∀ p ∈ unitSphere n, ∃ C : E n →L[ℝ] E n →L[ℝ] ℝ,
      Tendsto (realHessian w) (𝓝[unitBall n] p) (𝓝 C) ∧
      (∀ v z, C v z = C z v) ∧ (complexHessianOfRealBilinear C).PosDef ∧
        (complexHessianOfRealBilinear C).det.re = f p := by
  have hBound (x : E n) (hx : x ∈ unitBall n) : ‖realHessian w x‖ ≤ (L : ℝ) := by
    rw [← fderiv_dirichlet_firstJet_eq_realHessian hD hx]
    exact norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hLip
  have hSym (x : E n) (hx : x ∈ unitBall n) (v z : E n) :
      realHessian w x v z = realHessian w x z v :=
    ((hw2.contDiffAt (isOpen_ball.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)).eq v z
  have hMatrix (x : E n) (hx : x ∈ unitBall n) :
      complexHessianOfRealBilinear (realHessian w x) = complexHessian w x :=
    complexHessianOfRealBilinear_eq (hw2.contDiffAt (isOpen_ball.mem_nhds hx))
  intro p hp
  apply exists_dirichlet_boundary_hessian_limit hp hBound
    (hfPos p (sphere_subset_closedBall hp))
    ((hf p (sphere_subset_closedBall hp)).mono ball_subset_closedBall) hSym
    (fun x hx => by rw [hMatrix x hx]; exact hPos x hx)
    (fun x hx => by rw [hMatrix x hx]; exact hDet x hx)
  intro v hv hOrth
  obtain ⟨T, M, hTp, hNorm, hTJ, hTM, hM, hTan⟩ :=
    exists_dirichlet_skewHermitianField_of_tangent hp hOrth
  have hNorm3 : ‖T‖ ≤ 3 := by simpa only [hv, mul_one] using hNorm
  obtain ⟨a, Q, _, _, _, _, _, _, hQLim⟩ :=
    exists_dirichlet_rotation_boundary_firstJet hn hw2 hDclosed hD hLip hw0 hHolder hPower
      T hTJ M hTM hM (fun x _ => hTan x) hNorm3
  refine ⟨T, a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p - (G p).comp T, hTp, ?_⟩
  exact exists_dirichlet_rotation_hessian_trace hw2 hD hLip T hp (hQLim p hp)

theorem contDiffOn_two_dirichlet_of_rotation_boundary_power {n : ℕ} (hn : 0 < n)
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hwC : ContinuousOn w (closedUnitBall n)) (hw2 : ContDiffOn ℝ 2 w (unitBall n))
    (hDclosed : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    (hHolder : ∃ β H : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 ≤ H ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤ (H * (4 / R : ℝ) ^ β) * ‖x - y‖ ^ β)
    (hPower : HasDirichletRotationBoundaryPower G)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x)
    (hPos : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
    (hDet : ∀ x ∈ unitBall n, (complexHessian w x).det.re = f x) :
    ContDiffOn ℝ 2 w (closedUnitBall n) := by
  have hHC : ContinuousOn (realHessian w) (unitBall n) := by
    intro x hx
    exact (((hw2.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hDG (x : E n) (hx : x ∈ unitBall n) : HasFDerivAt G (realHessian w x) x := by
    rw [← fderiv_dirichlet_firstJet_eq_realHessian hD hx]
    exact (differentiableAt_dirichlet_firstJet_of_interiorC2 hw2 hD hx).hasFDerivAt
  apply contDiffOn_two_dirichlet_closedBall_of_hessian_limits hwC hLip.continuousOn hD hHC hDG
  intro p hp
  obtain ⟨C, hC, _⟩ := exists_dirichlet_actual_boundary_hessian_limits hn hw2 hDclosed hD hLip
    hw0 hHolder hPower hf hfPos hPos hDet p hp
  exact ⟨C, hC⟩

end KEBall
