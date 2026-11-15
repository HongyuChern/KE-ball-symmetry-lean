import KEBall.DirichletLinearizedEnergy
import KEBall.DirichletSobolev

/-!
# Weak solvability of the determinant linearization

The real cofactor operator gives the bilinear form of the linearized
Dirichlet problem. Its weak solution comes from Lax–Milgram, and Green's
identity identifies the equation on smooth tests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff ComplexOrder Gradient Matrix

namespace KEBall

/-- The real coefficient operator of the determinant linearization. -/
noncomputable def dirichletCofactorOperator {n : ℕ} (u : E n → ℝ) (x : E n) :
    E n →L[ℝ] E n :=
  (8 : ℝ)⁻¹ •
    ((InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (hermitianRealification (complexHessian u x).adjugate))

theorem dirichletCofactorOperator_inner {n : ℕ} (u : E n → ℝ) (x v w : E n) :
    inner ℝ (dirichletCofactorOperator u x v) w =
      (8 : ℝ)⁻¹ * hermitianRealification (complexHessian u x).adjugate v w := by
  let R := InnerProductSpace.toDual ℝ (E n)
  let L := hermitianRealification (complexHessian u x).adjugate v
  change inner ℝ ((8 : ℝ)⁻¹ • R.symm L) w = (8 : ℝ)⁻¹ * L w
  rw [real_inner_smul_left]
  have hR : inner ℝ (R.symm L) w = L w :=
    congrArg (fun T : E n →L[ℝ] ℝ => T w) (R.apply_symm_apply L)
  rw [hR]

theorem dirichletCofactorOperator_continuousOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContinuousOn (dirichletCofactorOperator u) U := by
  let R := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hComp : Continuous (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => R.comp B) :=
    (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) R).continuous
  have hScale : Continuous (fun L : E n →L[ℝ] E n => (8 : ℝ)⁻¹ • L) := continuous_const_smul _
  have hCont : Continuous (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => (8 : ℝ)⁻¹ • R.comp B) :=
    hScale.comp hComp
  exact hCont.comp_continuousOn (hermitianRealification_contDiffOn
    (matrixField_adjugate_contDiffOn (complexHessian_contDiffOn hU hu))).continuousOn

/-- The real cofactor quadratic form is the prescribed-density multiple
of the log-determinant principal symbol. -/
theorem dirichletCofactorOperator_inner_self {n : ℕ} {u : E n → ℝ} {x : E n}
    (hA : (complexHessian u x).PosDef) (v : E n) :
    inner ℝ (dirichletCofactorOperator u x v) v =
      (complexHessian u x).det.re *
        complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x := by
  let A := complexHessian u x
  have hAdj : A.adjugate = A.det • A⁻¹ := adjugate_eq_det_smul_inv hA
  rw [dirichletCofactorOperator_inner, hermitianRealification_eq_re_dotProduct,
    complexLaplacian_rankOne_quadratic, star_star]
  change (8 : ℝ)⁻¹ * (2 * (complexCoord v ⬝ᵥ (A.adjugate *ᵥ star (complexCoord v))).re) =
    A.det.re * ((complexCoord v ⬝ᵥ (A⁻¹ *ᵥ star (complexCoord v))).re / 4)
  rw [hAdj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, posDef_det_eq_ofReal_re hA]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The cofactor flux paired with a test derivative has the same
bilinear coefficient as the weak Dirichlet operator. -/
theorem cofactorRealField_pairing_eq_dirichletCofactorOperator {n : ℕ}
    {u v h : E n → ℝ} {x : E n}
    (hv : DifferentiableAt ℝ v x) (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ v x (cofactorRealField u h x) =
      2 * inner ℝ (dirichletCofactorOperator u x (∇ h x)) (∇ v x) := by
  let A := (complexHessian u x).adjugate
  let p : Fin n → ℂ := fun j => partialBar j (fun y => (h y : ℂ)) x
  have ht : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    change (starRingEnd ℂ) ((2 : ℂ)⁻¹) = _
    simp [starRingEnd_apply]
  have hp : p = (2 : ℂ)⁻¹ • complexCoord (∇ h x) := by
    funext j
    change partialBar j (fun y => (h y : ℂ)) x = _
    have hj := congrFun (partialZ_eq_half_star_gradient hh) j
    change partialZ j (fun y => (h y : ℂ)) x = _ at hj
    rw [partialBar_ofReal hh, hj]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul, star_star, ht]
    exact mul_comm _ _
  have hField : complexCoord (cofactorRealField u h x) = Aᵀ *ᵥ p := by
    rw [cofactorRealField, complexCoord_complexVectorReal]
    rfl
  rw [fderiv_eq_wirtinger hv]
  change 2 * ((fun j => partialZ j (fun y => (v y : ℂ)) x) ⬝ᵥ
    complexCoord (cofactorRealField u h x)).re = _
  rw [dirichletCofactorOperator_inner, hermitianRealification_eq_re_dotProduct, hField,
    partialZ_eq_half_star_gradient hv, hp, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    Matrix.dotProduct_transpose_mulVec]
  norm_num [smul_eq_mul, Complex.mul_re, Complex.mul_im]
  ring

/-- Integration by parts identifies the weak coefficient form with the
negative determinant linearization on smooth tests. -/
theorem integral_dirichletCofactorOperator_eq_neg_linearization {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u v h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hv : ContDiffOn ℝ ∞ v U) (hh : ContDiffOn ℝ ∞ h U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0) :
    (∫ x in unitBall n, inner ℝ (dirichletCofactorOperator u x (∇ h x)) (∇ v x) ∂volume0 n) =
      -(∫ x in unitBall n, v x * MoserTrudinger.cofactorContraction u h x ∂volume0 n) := by
  rw [MoserTrudinger.integral_mul_cofactorContraction_eq_neg_half_mixed_pairing
    hn hU hSub hu hv hh huP hv0]
  have he : (∫ x in unitBall n, fderiv ℝ v x (cofactorRealField u h x) ∂volume0 n) =
      2 * (∫ x in unitBall n, inner ℝ (dirichletCofactorOperator u x (∇ h x)) (∇ v x) ∂volume0 n) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
    intro x hx
    have hN := hU.mem_nhds (hSub (ball_subset_closedBall hx))
    exact cofactorRealField_pairing_eq_dirichletCofactorOperator
      ((hv.contDiffAt hN).differentiableAt (by simp))
      ((hh.contDiffAt hN).differentiableAt (by simp))
  rw [he]
  ring

/-- The cofactor linearization has a bounded linear weak Dirichlet
solution operator under the positive density and principal symbol bounds. -/
theorem exists_weakCofactorDirichletSolutionCLM {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    : ∃ S : DirichletBallL2 n ℝ →L[ℝ] DirichletSobolev n, ∀ g,
      let P (w : DirichletSobolev n) := ∀ v : DirichletSobolev n,
        (∫ x in unitBall n, inner ℝ (dirichletCofactorOperator u x ((w : DirichletBallL2Pair n).snd x))
          ((v : DirichletBallL2Pair n).snd x) ∂volume0 n) =
        ∫ x in unitBall n, g x * ((v : DirichletBallL2Pair n).fst x) ∂volume0 n
      P (S g) ∧ ∀ w, P w → w = S g := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hC := (dirichletCofactorOperator_continuousOn hU huU).mono hSub
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hC
  have hAe := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hLp : MemLp (dirichletCofactorOperator u) ⊤ ((volume0 n).restrict (unitBall n)) := by
    refine memLp_top_of_bound ((hC.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) M ?_
    filter_upwards [hAe] with x hx
    exact hM x (ball_subset_closedBall hx)
  apply exists_weakDirichletSolutionCLM hn hLp (mul_pos ha hl)
  filter_upwards [hAe] with x hx
  intro v
  rw [dirichletCofactorOperator_inner_self (huP x hx)]
  calc
    (a * l) * ‖v‖ ^ 2 = a * (l * ‖v‖ ^ 2) := by ring
    _ ≤ (complexHessian u x).det.re * (l * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (hDensity x hx) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hElliptic x hx v) (posDef_det_re_pos (huP x hx)).le

/-- The cofactor linearization has a unique weak zero-trace Dirichlet
solution for every L² right-hand side under the positive density and
principal symbol bounds. -/
theorem existsUnique_weakCofactorDirichletSolution {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) :
    ∃! w : DirichletSobolev n, ∀ v : DirichletSobolev n,
      (∫ x in unitBall n, inner ℝ (dirichletCofactorOperator u x ((w : DirichletBallL2Pair n).snd x))
        ((v : DirichletBallL2Pair n).snd x) ∂volume0 n) =
      ∫ x in unitBall n, g x * ((v : DirichletBallL2Pair n).fst x) ∂volume0 n := by
  obtain ⟨S, hS⟩ := exists_weakCofactorDirichletSolutionCLM hn hu huP ha hl hDensity hElliptic
  exact ⟨S g, (hS g).1, (hS g).2⟩

end KEBall
