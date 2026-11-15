import KEBall.DirichletTangentProjection
import KEBall.DirichletNormalRecovery

/-! Complex-linear skew-adjoint fields span the tangent space to each
centered sphere. These are the infinitesimal symmetries of the Dirichlet
equation used for tangential differentiation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Set
open scoped ComplexOrder ContDiff

namespace KEBall

/-- The sum of a real plane rotation and its image under the complex structure. -/
noncomputable def dirichletUnitaryRotation {n : ℕ} (v w : E n) : E n →L[ℝ] E n :=
  dirichletPlaneRotation v w + dirichletPlaneRotation (J v) (J w)

theorem dirichletUnitaryRotation_star {n : ℕ} (v w : E n) :
    star (dirichletUnitaryRotation v w) = -dirichletUnitaryRotation v w := by
  unfold dirichletUnitaryRotation
  rw [ContinuousLinearMap.star_eq_adjoint, map_add, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, dirichletPlaneRotation_star,
    dirichletPlaneRotation_star, neg_add]

theorem dirichletUnitaryRotation_apply {n : ℕ} (v w x : E n) :
    dirichletUnitaryRotation v w x =
      (inner ℝ w x • v - inner ℝ v x • w) +
        (inner ℝ (J w) x • J v - inner ℝ (J v) x • J w) := by
  simp only [dirichletUnitaryRotation, add_apply, dirichletPlaneRotation_apply]

theorem dirichletUnitaryRotation_J {n : ℕ} (v w x : E n) :
    dirichletUnitaryRotation v w (J x) = J (dirichletUnitaryRotation v w x) := by
  rw [dirichletUnitaryRotation_apply, dirichletUnitaryRotation_apply, inner_J_J, inner_J_J]
  have hJ (z : E n) : J z = JCLM n z := (JCLM_apply z).symm
  conv_rhs => rw [hJ]
  simp only [map_add, map_sub, map_smul]
  simp only [JCLM_apply, J_sq, inner_J_skew, neg_smul, smul_neg]
  abel

theorem JCLM_star (n : ℕ) : star (JCLM n) = -JCLM n := by
  ext1 x
  apply ext_inner_left ℝ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    neg_apply, inner_neg_right, JCLM_apply, inner_J_skew]

/-- The weighted unitary generators recover the tangent projection, with
the (Jx) component accounted for by the central generator. -/
theorem sum_dirichletUnitaryRotation_eq_tangentProjection {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (v x : E n) :
    (∑ i, inner ℝ (b i) x • dirichletUnitaryRotation v (b i) x) +
      inner ℝ (J v) x • J x = ‖x‖ ^ 2 • v - inner ℝ v x • x := by
  have hJ : (∑ i, inner ℝ (b i) x • J (b i)) = J x := by
    simp only [← JCLM_apply, ← map_smul, ← map_sum, b.sum_repr']
  have hZero : (∑ i, inner ℝ (b i) x * inner ℝ (J (b i)) x) = 0 := by
    simp only [inner_J_skew, mul_neg]
    rw [Finset.sum_neg_distrib]
    have he : (∑ i, inner ℝ (b i) x * inner ℝ (b i) (J x)) = inner ℝ x (J x) := by
      calc
        _ = ∑ i, inner ℝ x (b i) * inner ℝ (b i) (J x) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [real_inner_comm (b i) x]
        _ = _ := b.sum_inner_mul_inner x (J x)
    rw [he]
    have h := inner_J_skew x x
    rw [real_inner_comm (J x) x] at h ⊢
    linarith
  have hAux : (∑ i, inner ℝ (b i) x • dirichletPlaneRotation (J v) (J (b i)) x) =
      -(inner ℝ (J v) x • J x) := by
    simp only [dirichletPlaneRotation_apply, smul_sub, smul_smul, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hZero, zero_smul, zero_sub, ← hJ, Finset.smul_sum]
    simp only [smul_smul, mul_comm]
  simp only [dirichletUnitaryRotation, add_apply, smul_add, Finset.sum_add_distrib]
  rw [sum_dirichletPlaneRotation_eq_tangentProjection, hAux, add_assoc, neg_add_cancel, add_zero]

/-- Regularity along the finitely many fixed unitary fields controls
the tangential input of a bilinear form away from the origin. -/
theorem contDiffOn_tangentHessian_of_unitaryRotations {n : ℕ} {r : ℕ∞ω} {S : Set (E n)}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hS : ∀ x ∈ S, x ≠ 0)
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hRot : ∀ i j, ContDiffOn ℝ r (fun x => B x (dirichletUnitaryRotation (b i) (b j) x)) S)
    (hJ : ContDiffOn ℝ r (fun x => B x (J x)) S) :
    ContDiffOn ℝ r
      (fun x => (B x).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight x)) S := by
  let H (i : Fin (2 * n)) (x : E n) :=
    (∑ j, inner ℝ (b j) x • B x (dirichletUnitaryRotation (b i) (b j) x)) +
      inner ℝ (J (b i)) x • B x (J x)
  let P (x : E n) :=
    ContinuousLinearMap.id ℝ (E n) - (‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight x
  have hH (i : Fin (2 * n)) : ContDiffOn ℝ r (H i) S := by
    refine (ContDiffOn.sum (fun j _ => ?_)).add ?_
    · exact (innerSL ℝ (b j)).contDiff.contDiffOn.smul (hRot i j)
    · exact (innerSL ℝ (J (b i))).contDiff.contDiffOn.smul hJ
  have hInv : ContDiffOn ℝ r (fun x : E n => (‖x‖ ^ 2)⁻¹) S :=
    (contDiff_norm_sq ℝ).contDiffOn.inv fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr (hS x hx))
  have hForm : ContDiffOn ℝ r
      (fun x => ∑ i, (innerSL ℝ (b i)).smulRight ((‖x‖ ^ 2)⁻¹ • H i x)) S :=
    ContDiffOn.sum fun i _ => contDiffOn_const.smulRight (hInv.smul (hH i))
  refine hForm.congr fun x hx => ?_
  have hNorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hS x hx))
  have hP (i : Fin (2 * n)) : P x (b i) =
      (‖x‖ ^ 2)⁻¹ • (‖x‖ ^ 2 • b i - inner ℝ (b i) x • x) := by
    simp only [P, sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_sub, smul_smul,
      inv_mul_cancel₀ hNorm, one_smul, real_inner_comm x (b i)]
  have hEval (i : Fin (2 * n)) : B x (P x (b i)) = (‖x‖ ^ 2)⁻¹ • H i x := by
    rw [hP, ← sum_dirichletUnitaryRotation_eq_tangentProjection b (b i) x]
    simp only [H, map_smul, map_add, map_sum]
  change (B x).comp (P x) = _
  ext a : 1
  calc
    ((B x).comp (P x)) a =
        ((B x).comp (P x)) (∑ i, inner ℝ (b i) a • b i) := by rw [b.sum_repr']
    _ = _ := by
      simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply, hEval,
        sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- On an annulus the determinant and derivatives along the unitary fields
determine the regularity of the whole real Hessian. -/
theorem contDiffOn_realHessian_of_unitaryRotations_det {n : ℕ} {r : ℕ∞ω} {S : Set (E n)}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hS : ∀ x ∈ S, x ≠ 0)
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {f : E n → ℝ}
    (hSym : ∀ x ∈ S, ∀ a c, B x a c = B x c a)
    (hRot : ∀ i j, ContDiffOn ℝ r (fun x => B x (dirichletUnitaryRotation (b i) (b j) x)) S)
    (hJ : ContDiffOn ℝ r (fun x => B x (J x)) S)
    (hf : ContDiffOn ℝ r f S)
    (hPos : ∀ x ∈ S, (complexHessianOfRealBilinear (B x)).PosDef)
    (hDet : ∀ x ∈ S, (complexHessianOfRealBilinear (B x)).det.re = f x) :
    ContDiffOn ℝ r B S := fun x hx =>
  contDiffWithinAt_realHessian_of_tangent_det hx (hS x hx) hSym
    (contDiffOn_tangentHessian_of_unitaryRotations b hS hRot hJ) hf (hPos x hx) hDet

/-- A derivative along a fixed linear field supplies the Hessian evaluated
in that direction, via the product rule for derivatives within the domain. -/
theorem contDiffOn_fderivWithin_fderivWithin_apply_of_rotation {n r : ℕ}
    {S T : Set (E n)} (hS : UniqueDiffOn ℝ S) (hT : T ⊆ S)
    (hClosure : T ⊆ closure (interior S)) {u : E n → ℝ}
    (hu2 : ContDiffOn ℝ 2 u S) (hu : ContDiffOn ℝ (r + 1 : ℕ) u S)
    (R : E n →L[ℝ] E n)
    (hR : ContDiffOn ℝ (r + 1 : ℕ) (fun x => fderivWithin ℝ u S x (R x)) S) :
    ContDiffOn ℝ r (fun x => fderivWithin ℝ (fderivWithin ℝ u S) S x (R x)) T := by
  let D := fderivWithin ℝ u S
  let w (x : E n) := D x (R x)
  have hOrder : (r : ℕ∞ω) + 1 ≤ (r + 1 : ℕ) := by
    exact_mod_cast (le_refl (r + 1))
  have hW : ContDiffOn ℝ r (fderivWithin ℝ w S) S := hR.fderivWithin hS hOrder
  have hD : ContDiffOn ℝ r D S := hu.fderivWithin hS hOrder
  have hE : ContDiffOn ℝ r (fun x => (D x).comp R) S := hD.clm_comp contDiffOn_const
  refine ((hW.sub hE).mono hT).congr fun x hx => ?_
  have hxS := hT hx
  have hD1 : ContDiffOn ℝ 1 D S := hu2.fderivWithin hS (by norm_num)
  have hd := (hD1.differentiableOn one_ne_zero x hxS).hasFDerivWithinAt
  have hEq := (hd.clm_apply R.hasFDerivWithinAt).fderivWithin (hS x hxS)
  have hSym := (hu2 x hxS).isSymmSndFDerivWithinAt (by simp) hS (hClosure hx) hxS
  change _ = fderivWithin ℝ w S x - (D x).comp R
  rw [hEq]
  ext a
  simp only [ContinuousLinearMap.flip_apply, add_sub_cancel_left]
  exact hSym.eq (R x) a

/-- Near the boundary, one higher derivative of the angular derivatives and
regularity of the prescribed density propagate to the within Hessian. -/
theorem contDiffOn_fderivWithin_fderivWithin_of_unitaryRotations_det {n r : ℕ}
    {S T : Set (E n)} (hS : UniqueDiffOn ℝ S) (hT : T ⊆ S)
    (hClosure : T ⊆ closure (interior S)) (hAway : ∀ x ∈ T, x ≠ 0)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {u f : E n → ℝ}
    (hu2 : ContDiffOn ℝ 2 u S) (hu : ContDiffOn ℝ (r + 1 : ℕ) u S)
    (hRot : ∀ i j, ContDiffOn ℝ (r + 1 : ℕ) (fun x =>
      fderivWithin ℝ u S x (dirichletUnitaryRotation (b i) (b j) x)) S)
    (hJ : ContDiffOn ℝ (r + 1 : ℕ) (fun x => fderivWithin ℝ u S x (J x)) S)
    (hf : ContDiffOn ℝ r f T)
    (hPos : ∀ x ∈ T,
      (complexHessianOfRealBilinear (fderivWithin ℝ (fderivWithin ℝ u S) S x)).PosDef)
    (hDet : ∀ x ∈ T,
      (complexHessianOfRealBilinear (fderivWithin ℝ (fderivWithin ℝ u S) S x)).det.re = f x) :
    ContDiffOn ℝ r (fderivWithin ℝ (fderivWithin ℝ u S) S) T := by
  refine contDiffOn_realHessian_of_unitaryRotations_det b hAway ?_ ?_ ?_ hf hPos hDet
  · intro x hx a c
    exact ((hu2 x (hT hx)).isSymmSndFDerivWithinAt (by simp) hS (hClosure hx) (hT hx)).eq a c
  · intro i j
    exact contDiffOn_fderivWithin_fderivWithin_apply_of_rotation hS hT hClosure hu2 hu _ (hRot i j)
  · simpa only [JCLM_apply] using
      (contDiffOn_fderivWithin_fderivWithin_apply_of_rotation hS hT hClosure hu2 hu (JCLM n)
        (by simpa only [JCLM_apply] using hJ))

end KEBall
