import KEBall.DirichletCofactorSmoothMap
import KEBall.DirichletHessianHolderNorm

/-!
# Hölder continuity of the actual interior elliptic coefficient

The real cofactor is a smooth polynomial map of the real Hessian.  Its
bounded-set Lipschitz estimate transfers the already proved Hessian modulus
to the very coefficient of the linearized equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ContDiff Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem contDiff_dirichlet_complexHessianOfRealBilinear {n : ℕ} :
    ContDiff ℝ ∞ (@complexHessianOfRealBilinear n) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have h (v w : E n) :
      ContDiff ℝ ∞ (fun D : E n →L[ℝ] E n →L[ℝ] ℝ => (D v w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_id.clm_apply contDiff_const).clm_apply contDiff_const)
  exact (contDiff_const (c := (4 : ℂ)⁻¹)).mul
    (((h (realDirection i) (realDirection j)).add (h (imagDirection i) (imagDirection j))).add
      ((contDiff_const (c := Complex.I)).mul
        ((h (realDirection i) (imagDirection j)).sub (h (imagDirection i) (realDirection j)))))

theorem exists_dirichlet_cofactor_lipschitz_on_realHessian_ball {n : ℕ} (R : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun D : E n →L[ℝ] E n →L[ℝ] ℝ =>
        dirichletCofactorOfMatrix (complexHessianOfRealBilinear D))
      (closedBall 0 R) := by
  have h : ContDiff ℝ ∞ (fun D : E n →L[ℝ] E n →L[ℝ] ℝ =>
      dirichletCofactorOfMatrix (complexHessianOfRealBilinear D)) :=
    contDiff_dirichletCofactorOfMatrix.comp contDiff_dirichlet_complexHessianOfRealBilinear
  exact h.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)

theorem exists_dirichlet_cofactor_local_holder_of_hessian_oscillation {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖dirichletCofactorOperator w x - dirichletCofactorOperator w y‖ ≤
            C * ‖x - y‖ ^ α := by
  have hw := contDiffOn_two_of_dirichlet_hessian_oscillation hD hG hDecay
  have hw1 : ContDiffOn ℝ 1 (fderiv ℝ w) (unitBall n) :=
    hw.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hw0 : ContDiffOn ℝ 0 (realHessian w) (unitBall n) :=
    hw1.fderiv_of_isOpen isOpen_ball (by norm_num)
  obtain ⟨α, hα0, hα1, hHolder⟩ :=
    exists_dirichlet_realHessian_local_holder_of_oscillation hD hG hDecay
  refine ⟨α, hα0, hα1, ?_⟩
  intro x₀ R hR hR1 hMargin
  have hClosed : closedBall x₀ (R / 2) ⊆ unitBall n :=
    (closedBall_subset_closedBall (by linarith)).trans hMargin
  obtain ⟨B, hB⟩ := (isCompact_closedBall x₀ (R / 2)).exists_bound_of_continuousOn
    (hw0.continuousOn.mono hClosed)
  obtain ⟨K, hK⟩ := exists_dirichlet_cofactor_lipschitz_on_realHessian_ball (n := n) B
  obtain ⟨C, hC, hCH⟩ := hHolder x₀ R hR hR1 hMargin
  have he (x : E n) (hx : x ∈ ball x₀ (R / 2)) :
      dirichletCofactorOfMatrix (complexHessianOfRealBilinear (realHessian w x)) =
        dirichletCofactorOperator w x := by
    rw [complexHessianOfRealBilinear_eq
      (hw.contDiffAt (isOpen_ball.mem_nhds (hClosed (ball_subset_closedBall hx))))]
    rfl
  refine ⟨(K : ℝ) * C, mul_nonneg K.coe_nonneg hC, ?_⟩
  intro x hx y hy
  have h := hK.dist_le_mul (realHessian w x)
    (mem_closedBall_zero_iff.mpr (hB x (ball_subset_closedBall hx)))
    (realHessian w y) (mem_closedBall_zero_iff.mpr (hB y (ball_subset_closedBall hy)))
  rw [he x hx, he y hy, dist_eq_norm, dist_eq_norm] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hCH x hx y hy) K.coe_nonneg)

end KEBall
