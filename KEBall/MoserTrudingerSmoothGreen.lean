import KEBall.SecondGreen
import KEBall.LogDetConcavity

/-!
# Green identities for the smooth Monge–Ampère energy

The background Hessian can be any positive definite complex Hessian.
The potentials in the integration by parts have zero boundary values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix

namespace KEBall.MoserTrudinger

/-- The real differential of the determinant in a complex Hessian direction. -/
noncomputable def cofactorContraction {n : ℕ} (u h : E n → ℝ) (x : E n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, (complexHessian u x).adjugate j i *
    complexHessian h x i j).re

theorem cofactorContraction_self {n : ℕ} (u : E n → ℝ) (x : E n) :
    cofactorContraction u u x = (n : ℝ) * (complexHessian u x).det.re := by
  let A := complexHessian u x
  have h (i : Fin n) : (∑ j : Fin n, A.adjugate j i * A i j) = A.det := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) A.mul_adjugate
    simpa [Matrix.mul_apply, mul_comm] using he
  change (∑ i : Fin n, ∑ j : Fin n, A.adjugate j i * A i j).re = (n : ℝ) * A.det.re
  simp [h, nsmul_eq_mul, Complex.mul_re]

private theorem isUnit_det_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.mpr fun h => (posDef_det_re_pos hA).ne' (by rw [h]; rfl)

private theorem divergence_cofactor {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hh : ContDiffAt ℝ ∞ h x)
    (hpos : (complexHessian u x).PosDef) :
    euclideanDivergence (cofactorRealField u h) x = 2 * cofactorContraction u h x := by
  apply cofactorRealField_divergence_of_piola hu hh
  intro j
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact cofactor_divergence_at hc realDirection imagDirection
    (isUnit_det_of_posDef hpos) j

theorem integrable_mul_contraction {n : ℕ} (hn : 0 < n) {U : Set (E n)} (hU : IsOpen U)
    (hsub : closedUnitBall n ⊆ U) {u v h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (hh : ContDiffOn ℝ ∞ h U) :
    IntegrableOn (fun x => v x * cofactorContraction u h x) (unitBall n) (volume0 n) := by
  have hC : ContinuousOn (cofactorContraction u h) U := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (matrixField_adjugate_contDiffOn (complexHessian_contDiffOn hU hu) j i).continuousOn.mul
      (complexHessian_contDiffOn hU hh i j).continuousOn
  exact ((hv.continuousOn.mul hC).mono hsub).integrableOn_of_subset_isCompact
    (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)

/-- Green's identity for the linearized determinant at a smooth positive Hessian. -/
theorem integral_mul_cofactorContraction_swap {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (hh : ContDiffOn ℝ ∞ h U)
    (hpos : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0) (hh0 : ∀ x ∈ unitSphere n, h x = 0) :
    (∫ x in unitBall n, v x * cofactorContraction u h x ∂volume0 n) =
      ∫ x in unitBall n, h x * cofactorContraction u v x ∂volume0 n := by
  have hF := secondGreenField_contDiffOn hU hu hv hh
  have hGreen := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hsub
    (hF.of_le (by simp))
  have hd (x : E n) (hx : x ∈ unitBall n) :
      euclideanDivergence (secondGreenField u v h) x =
        2 * (v x * cofactorContraction u h x - h x * cofactorContraction u v x) := by
    have hN := hU.mem_nhds (hsub (ball_subset_closedBall hx))
    have hu' := hu.contDiffAt hN
    have hv' := hv.contDiffAt hN
    have hh' := hh.contDiffAt hN
    have hvd := hv'.differentiableAt (by simp)
    have hhd := hh'.differentiableAt (by simp)
    have hFh := ((cofactorRealField_contDiffOn hU hu hh).contDiffAt hN).differentiableAt (by simp)
    have hFv := ((cofactorRealField_contDiffOn hU hu hv).contDiffAt hN).differentiableAt (by simp)
    unfold secondGreenField
    rw [euclideanDivergence_sub (V := fun y => v y • cofactorRealField u h y)
      (W := fun y => h y • cofactorRealField u v y) (hvd.smul hFh) (hhd.smul hFv),
      euclideanDivergence_smul hvd hFh, euclideanDivergence_smul hhd hFv,
      divergence_cofactor hu' hh' (hpos x hx), divergence_cofactor hu' hv' (hpos x hx),
      cofactor_gradient_pairing_symm (hpos x hx).isHermitian hvd hhd]
    ring
  have hvol : (∫ x in unitBall n, euclideanDivergence (secondGreenField u v h) x ∂volume0 n) =
      2 * ((∫ x in unitBall n, v x * cofactorContraction u h x ∂volume0 n) -
        ∫ x in unitBall n, h x * cofactorContraction u v x ∂volume0 n) := by
    rw [← integral_sub (integrable_mul_contraction hn hU hsub hu hv hh)
      (integrable_mul_contraction hn hU hsub hu hh hv), ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball hd
  have hsurf : (∫ x : Sphere n, inner ℝ x.1 (secondGreenField u v h x.1) ∂sphere0 n) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by simp [secondGreenField, hv0 _ x.2, hh0 _ x.2]
  rw [hvol, hsurf, mul_zero] at hGreen
  linarith

theorem cofactor_gradient_pairing_nonneg {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hpos : (complexHessian u x).PosDef) (hh : DifferentiableAt ℝ h x) :
    0 ≤ fderiv ℝ h x (cofactorRealField u h x) := by
  let A := complexHessian u x
  let p : Fin n → ℂ := fun i => partialZ i (fun y => (h y : ℂ)) x
  have hu : IsUnit A.det := isUnit_det_of_posDef hpos
  have hA : A.det • A⁻¹ = A.adjugate := by
    rw [A.nonsing_inv_apply hu, smul_smul, hu.mul_val_inv, one_smul]
  have hAdj : A.adjugate.PosSemidef := by
    rw [← hA]
    exact (hpos.inv.smul hpos.det_pos).posSemidef
  have hpos' := (RCLike.nonneg_iff.mp (hAdj.dotProduct_mulVec_nonneg p)).1
  rw [fderiv_eq_wirtinger hh]
  have hEq :
      (∑ i : Fin n, partialZ i (fun y => (h y : ℂ)) x *
        complexCoord (cofactorRealField u h x) i) =
        star p ⬝ᵥ (A.adjugate *ᵥ p) := by
    simp only [cofactorRealField, complexCoord_complexVectorReal, cofactorVectorField,
      partialBar_ofReal hh, Finset.mul_sum, dotProduct, Matrix.mulVec, p, A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hEq]
  positivity

/-- Green's identity for the determinant linearization tested against a zero-boundary variation. -/
theorem integral_mul_cofactorContraction_eq_neg_half_mixed_pairing {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (hh : ContDiffOn ℝ ∞ h U)
    (hpos : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0) :
    (∫ x in unitBall n, v x * cofactorContraction u h x ∂volume0 n) =
      -(∫ x in unitBall n, fderiv ℝ v x (cofactorRealField u h x) ∂volume0 n) / 2 := by
  let V : E n → E n := fun x => v x • cofactorRealField u h x
  let P : E n → ℝ := fun x => fderiv ℝ v x (cofactorRealField u h x)
  have hF := cofactorRealField_contDiffOn hU hu hh
  have hV : ContDiffOn ℝ 1 V U := (hv.smul hF).of_le (by simp)
  have hGreen := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hsub hV
  have hd (x : E n) (hx : x ∈ unitBall n) :
      euclideanDivergence V x = 2 * (v x * cofactorContraction u h x) + P x := by
    have hN := hU.mem_nhds (hsub (ball_subset_closedBall hx))
    have hh' := hh.contDiffAt hN
    have hv' := hv.contDiffAt hN
    change euclideanDivergence (fun x => v x • cofactorRealField u h x) x = _
    rw [euclideanDivergence_smul (hv'.differentiableAt (by simp))
      ((hF.contDiffAt hN).differentiableAt (by simp)),
      divergence_cofactor (hu.contDiffAt hN) hh' (hpos x hx)]
    dsimp [P]
    ring
  have hP : ContinuousOn P U :=
    ((hv.fderiv_of_isOpen hU (by simp) (m := 0)).continuousOn).clm_apply hF.continuousOn
  have hPi : IntegrableOn P (unitBall n) (volume0 n) :=
    (hP.mono hsub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hvol : (∫ x in unitBall n, euclideanDivergence V x ∂volume0 n) =
      2 * (∫ x in unitBall n, v x * cofactorContraction u h x ∂volume0 n) +
        ∫ x in unitBall n, P x ∂volume0 n := by
    rw [← integral_const_mul, ← integral_add
      ((integrable_mul_contraction hn hU hsub hu hv hh).const_mul 2) hPi]
    exact setIntegral_congr_fun measurableSet_ball hd
  have hsurf : (∫ x : Sphere n, inner ℝ x.1 (V x.1) ∂sphere0 n) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by simp [V, hv0 _ x.2]
  rw [hvol, hsurf, mul_zero] at hGreen
  change (∫ x in unitBall n, v x * cofactorContraction u h x ∂volume0 n) =
    -(∫ x in unitBall n, P x ∂volume0 n) / 2
  linarith only [hGreen]

/-- Green's identity for the energy of a zero-boundary variation. -/
theorem integral_mul_cofactorContraction_eq_neg_half_pairing {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (hpos : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hh0 : ∀ x ∈ unitSphere n, h x = 0) :
    (∫ x in unitBall n, h x * cofactorContraction u h x ∂volume0 n) =
      -(∫ x in unitBall n, fderiv ℝ h x (cofactorRealField u h x) ∂volume0 n) / 2 := by
  exact integral_mul_cofactorContraction_eq_neg_half_mixed_pairing hn hU hsub hu hh hh hpos hh0

/-- The quadratic form of the linearized determinant is nonpositive
on smooth zero-boundary variations. -/
theorem integral_mul_cofactorContraction_nonpos {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (hpos : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hh0 : ∀ x ∈ unitSphere n, h x = 0) :
    (∫ x in unitBall n, h x * cofactorContraction u h x ∂volume0 n) ≤ 0 := by
  rw [integral_mul_cofactorContraction_eq_neg_half_pairing hn hU hsub hu hh hpos hh0]
  have hnonneg : 0 ≤ ∫ x in unitBall n, fderiv ℝ h x (cofactorRealField u h x) ∂volume0 n := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact cofactor_gradient_pairing_nonneg (hpos x hx)
      ((hh.contDiffAt (hU.mem_nhds (hsub (ball_subset_closedBall hx)))).differentiableAt (by simp))
  linarith only [hnonneg]

end KEBall.MoserTrudinger
