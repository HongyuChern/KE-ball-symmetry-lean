import KEBall.DirichletFirstJetRotationHolder
import KEBall.DirichletBoundaryRemainder

/-!
# Interior derivative modulus for rotation traces near the boundary

The Hessian radius factor is kept explicitly: on the ball of radius r/8,
where r=1-|x|, the derivative of G(y)(T y) has Hölder constant K/r^beta.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem differentiableAt_dirichlet_firstJet_of_interiorC2 {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hw : ContDiffOn ℝ 2 w (unitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    {x : E n} (hx : x ∈ unitBall n) : DifferentiableAt ℝ G x := by
  have he : G =ᶠ[𝓝 x] fderiv ℝ w := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (hD y hy).fderiv.symm
  apply he.differentiableAt_iff.mpr
  exact (((hw.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem exists_dirichlet_rotation_derivative_boundary_scale_holder {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hw : ContDiffOn ℝ 2 w (unitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    {β H : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hH : 0 ≤ H)
    (hHolder : ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
      ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
        ‖realHessian w x - realHessian w y‖ ≤ (H * (4 / R : ℝ) ^ β) * ‖x - y‖ ^ β)
    (T : E n →L[ℝ] E n) :
    (∀ x ∈ unitBall n, DifferentiableAt ℝ (fun y => G y (T y)) x) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ unitBall n, ∀ r : ℝ, r = 1 - ‖x‖ → r ≤ 1 / 2 →
      ∀ y ∈ ball x (r / 8), ∀ z ∈ ball x (r / 8),
        ‖fderiv ℝ (fun v => G v (T v)) y - fderiv ℝ (fun v => G v (T v)) z‖ ≤
          (K / r ^ β) * ‖y - z‖ ^ β := by
  have hGD (x : E n) (hx : x ∈ unitBall n) :=
    differentiableAt_dirichlet_firstJet_of_interiorC2 hw hD hx
  refine ⟨fun x hx => (hGD x hx).clm_apply T.differentiableAt, ?_⟩
  let K : ℝ := ‖T‖ * (H * (16 : ℝ) ^ β + 2 * (L : ℝ))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro x hx r hrEq hrSmall
  have hr : 0 < r := by rw [hrEq]; exact sub_pos.mpr (mem_ball_zero_iff.mp hx)
  have hr1 : r ≤ 1 := by rw [hrEq]; linarith [norm_nonneg x]
  have hInside : closedBall x (r / 2) ⊆ unitBall n :=
    closedBall_subset_dirichlet_unitBall_of_margin (by linarith only [hr, hrEq])
  have hSub : ball x (r / 8) ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hInside)
  have hMargin : closedBall x (2 * (r / 4)) ⊆ unitBall n := by
    convert hInside using 2 <;> ring
  have hScale : 4 / (r / 4) = 16 / r := by ring
  have hGH (y : E n) (hy : y ∈ ball x (r / 8)) (z : E n) (hz : z ∈ ball x (r / 8)) :
      ‖fderiv ℝ G y - fderiv ℝ G z‖ ≤
        (H * (16 : ℝ) ^ β / r ^ β) * ‖y - z‖ ^ β := by
    rw [fderiv_dirichlet_firstJet_eq_realHessian hD (hSub hy),
      fderiv_dirichlet_firstJet_eq_realHessian hD (hSub hz)]
    have hy' : y ∈ ball x ((r / 4) / 2) := by convert hy using 2 <;> ring
    have hz' : z ∈ ball x ((r / 4) / 2) := by convert hz using 2 <;> ring
    have h := hHolder x (r / 4) (by positivity) (by linarith) hMargin y hy' z hz'
    rw [hScale, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 16) hr.le] at h
    simpa only [mul_div_assoc] using h
  have hDiam (y : E n) (hy : y ∈ ball x (r / 8)) (z : E n) (hz : z ∈ ball x (r / 8)) :
      ‖y - z‖ ≤ 1 := by
    rw [← dist_eq_norm]
    have h := dist_triangle y x z
    rw [dist_comm x z] at h
    have hy' := mem_ball.mp hy
    have hz' := mem_ball.mp hz
    linarith
  have hRaw := dirichlet_firstJet_linearField_derivative_holder hLip hSub
    (fun y hy => hGD y (hSub hy)) hβ1 hGH hDiam T
  have hpβ : 0 < r ^ β := Real.rpow_pos_of_pos hr _
  have hpβ1 : r ^ β ≤ 1 := Real.rpow_le_one hr.le hr1 hβ.le
  have hLdiv : 2 * (L : ℝ) ≤ 2 * (L : ℝ) / r ^ β :=
    (le_div_iff₀ hpβ).mpr (mul_le_of_le_one_right (by positivity) hpβ1)
  have hCoeff : ‖T‖ * (H * (16 : ℝ) ^ β / r ^ β + 2 * (L : ℝ)) ≤ K / r ^ β := by
    calc
      _ ≤ ‖T‖ * (H * (16 : ℝ) ^ β / r ^ β + 2 * (L : ℝ) / r ^ β) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hLdiv) (norm_nonneg T)
      _ = _ := by dsimp [K]; ring
  intro y hy z hz
  exact (hRaw y hy z hz).trans
    (mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg (norm_nonneg _) _))

end KEBall
