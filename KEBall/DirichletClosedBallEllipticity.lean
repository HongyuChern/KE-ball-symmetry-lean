import KEBall.DirichletLogDensityClosedBallC2
import KEBall.DirichletAnnularRecovery
import KEBall.DirichletAngularWordEquation
import KEBall.DirichletHessianCofactorHolder

/-!
# The actual continuous cofactor on the closed ball

Closed-ball C2 regularity gives a continuous within Hessian.  Positive
interior determinant and continuous positive density keep this Hessian
positive definite at the sphere.  Compactness then gives genuine uniform
ellipticity of the corresponding real cofactor on the entire closed ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem dirichlet_adjugate_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : A.adjugate.PosDef := by
  rw [adjugate_eq_det_smul_inv hA, posDef_det_eq_ofReal_re hA]
  exact hA.inv.smul (show (0 : ℂ) < (A.det.re : ℂ) from
    Complex.zero_lt_real.mpr (posDef_det_re_pos hA))

theorem dirichletCofactorOfMatrix_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {v : E n} (hv : v ≠ 0) :
    0 < inner ℝ (dirichletCofactorOfMatrix A v) v := by
  have he : inner ℝ (dirichletCofactorOfMatrix A v) v =
      (8 : ℝ)⁻¹ * hermitianRealification A.adjugate v v := by
    unfold dirichletCofactorOfMatrix
    rw [_root_.smul_apply, real_inner_smul_left]
    congr 1
    exact congrArg (fun F : E n →L[ℝ] ℝ => F v)
      ((InnerProductSpace.toDual ℝ (E n)).apply_symm_apply
        (hermitianRealification A.adjugate v))
  rw [he]
  exact mul_pos (by norm_num) (hermitianRealification_pos (dirichlet_adjugate_posDef hA) v hv)

theorem exists_uniform_ellipticity_of_continuous_closedBall_operator {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n}
    (hA : ContinuousOn A (closedUnitBall n))
    (hPos : ∀ x ∈ closedUnitBall n, ∀ v : E n, v ≠ 0 → 0 < inner ℝ (A x v) v) :
    ∃ l M : ℝ, 0 < l ∧ 0 < M ∧
      (∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M) ∧
      ∀ x ∈ closedUnitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v := by
  let S := closedUnitBall n ×ˢ unitSphere n
  let Q (z : E n × E n) := inner ℝ (A z.1 z.2) z.2
  have hQ : ContinuousOn Q S :=
    ((hA.comp continuousOn_fst (fun _ hz => hz.1)).clm_apply continuousOn_snd).inner
      continuousOn_snd
  let e : E n := EuclideanSpace.basisFun (Fin (2 * n)) ℝ ⟨0, by omega⟩
  have he : e ∈ unitSphere n := mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).orthonormal.norm_eq_one _)
  have hS : IsCompact S := (isCompact_closedBall (0 : E n) 1).prod
    (isCompact_sphere (0 : E n) 1)
  obtain ⟨p, hp, hMin⟩ := hS.exists_isMinOn ⟨(0, e), by simp [S, closedUnitBall, he]⟩ hQ
  have hpNe : p.2 ≠ 0 := by
    intro hp0
    have h := mem_sphere_zero_iff_norm.mp hp.2
    rw [hp0, norm_zero] at h
    norm_num at h
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hA
  refine ⟨Q p, max B 1, hPos p.1 hp.1 p.2 hpNe, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hB x hx).trans (le_max_left _ _), ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvNorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let z : E n := ‖v‖⁻¹ • v
  have hz : z ∈ unitSphere n := by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [z, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ hvNorm]
  calc
    Q p * ‖v‖ ^ 2 = ‖v‖ ^ 2 * Q p := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * Q (x, z) :=
      mul_le_mul_of_nonneg_left (hMin ⟨hx, hz⟩) (sq_nonneg _)
    _ = inner ℝ (A x v) v := by
      simp only [Q, z, map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp

theorem continuousOn_dirichletWithinComplexHessian_of_C2 {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ContinuousOn (dirichletWithinComplexHessian u) (closedUnitBall n) := by
  have hS : UniqueDiffOn ℝ (closedUnitBall n) := uniqueDiffOn_convex
    (convex_closedBall (0 : E n) 1) (by
      rw [show interior (closedUnitBall n) = unitBall n from interior_closedBall _ (by norm_num)]
      exact nonempty_ball.mpr (by norm_num))
  have hH : ContDiffOn ℝ 0
      (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n))
      (closedUnitBall n) :=
    (hu.fderivWithin (m := 1) hS (by norm_num)).fderivWithin hS (by norm_num)
  exact contDiff_dirichlet_complexHessianOfRealBilinear.continuous.comp_continuousOn hH.continuousOn

theorem exists_dirichlet_closedBall_cofactor_ellipticity_of_C2 {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hf : ContinuousOn f (closedUnitBall n))
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) f (unitBall n)) :
    let A (x : E n) := dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x)
    ContinuousOn A (closedUnitBall n) ∧
      (∀ x ∈ closedUnitBall n, ∀ v z : E n, inner ℝ (A x v) z = inner ℝ (A x z) v) ∧
      ∃ l M : ℝ, 0 < l ∧ 0 < M ∧
        (∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M) ∧
        ∀ x ∈ closedUnitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v := by
  let A (x : E n) := dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x)
  have hCont : ContinuousOn A (closedUnitBall n) :=
    contDiff_dirichletCofactorOfMatrix.continuous.comp_continuousOn
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu)
  have hPos := closedBall_withinHessian_posDef_and_det_of_C2 hu hf hfPos huP hEq
  refine ⟨hCont, fun x hx v z => dirichletCofactorOfMatrix_symmetric (hPos x hx).1.isHermitian v z,
    exists_uniform_ellipticity_of_continuous_closedBall_operator hn hCont ?_⟩
  intro x hx v hv
  exact dirichletCofactorOfMatrix_pos (hPos x hx).1 hv

end KEBall
