import KEBall.DirichletRankOneRecovery
import KEBall.DirichletSobolevClassical
import KEBall.DirichletPositiveMatrix

/-! Recovery of the radial Hessian entry on the closed ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

private theorem complexHessianOfRealBilinear_rankOne {n : ℕ} (v : E n) :
    let D (a b : E n) := inner ℝ v a * inner ℝ v b
    (fun i j => (4 : ℂ)⁻¹ *
      ((D (realDirection i) (realDirection j) : ℂ) +
        (D (imagDirection i) (imagDirection j) : ℂ) +
        Complex.I * ((D (realDirection i) (imagDirection j) : ℂ) -
          (D (imagDirection i) (realDirection j) : ℂ)))) =
      (4 : ℂ)⁻¹ • Matrix.vecMulVec (star (complexCoord v)) (complexCoord v) := by
  dsimp only
  ext i j
  simp [complexCoord, realDirection, imagDirection, EuclideanSpace.inner_single_right,
    Matrix.vecMulVec_apply, Pi.star_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex Hessian convention applied to a real bilinear Hessian. -/
noncomputable def complexHessianOfRealBilinear {n : ℕ} (D : E n →L[ℝ] E n →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  (4 : ℂ)⁻¹ *
    ((D (realDirection i) (realDirection j) : ℂ) +
      (D (imagDirection i) (imagDirection j) : ℂ) +
      Complex.I * ((D (realDirection i) (imagDirection j) : ℂ) -
        (D (imagDirection i) (realDirection j) : ℂ)))

theorem complexHessianOfRealBilinear_eq {n : ℕ} {v : E n → ℝ} {x : E n}
    (hv : ContDiffAt ℝ 2 v x) :
    complexHessianOfRealBilinear (realHessian v x) = complexHessian v x := by
  ext i j
  exact (complexHessian_real_entry_C2 hv i j).symm

theorem complexHessianOfRealBilinear_add_rankOne {n : ℕ}
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) (v : E n) (t : ℝ) :
    complexHessianOfRealBilinear (D + t • (innerSL ℝ v).smulRight (innerSL ℝ v)) =
      complexHessianOfRealBilinear D + ((t / 4 : ℝ) : ℂ) •
        Matrix.vecMulVec (star (complexCoord v)) (complexCoord v) := by
  ext i j
  have h := congrFun (congrFun (complexHessianOfRealBilinear_rankOne v) i) j
  change _ = ((4 : ℂ)⁻¹ • Matrix.vecMulVec (star (complexCoord v)) (complexCoord v)) i j at h
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.add_apply, show ((t / 4 : ℝ) : ℂ) =
    (t : ℂ) * (4 : ℂ)⁻¹ by push_cast; ring]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← h, complexHessianOfRealBilinear,
    add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem contDiffOn_complexHessianOfRealBilinear {n : ℕ} {S : Set (E n)} {r : ℕ∞ω}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} (hB : ContDiffOn ℝ r B S)
    (i j : Fin n) :
    ContDiffOn ℝ r (fun x => complexHessianOfRealBilinear (B x) i j) S := by
  have h (v w : E n) : ContDiffOn ℝ r (fun x => (B x v w : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  exact (contDiffOn_const (c := (4 : ℂ)⁻¹)).mul
    (((h (realDirection i) (realDirection j)).add (h (imagDirection i) (imagDirection j))).add
      ((contDiffOn_const (c := Complex.I)).mul
        ((h (realDirection i) (imagDirection j)).sub (h (imagDirection i) (realDirection j)))))

private theorem contDiffOn_realBilinear_rankOne {n : ℕ} {S : Set (E n)} {r : ℕ∞ω}
    {v : E n → E n} (hv : ContDiffOn ℝ r v S) :
    ContDiffOn ℝ r (fun x => (innerSL ℝ (v x)).smulRight (innerSL ℝ (v x))) S := by
  have hL : ContDiffOn ℝ r (fun x => innerSL ℝ (v x)) S :=
    (innerSL ℝ (E := E n)).contDiff.comp_contDiffOn hv
  exact hL.smulRight hL

/-- A real Hessian whose only unknown coefficient is a rank-one term has
the same regularity as the known part and the prescribed density. The
reference matrix may be shifted by a constant rank-one term. -/
theorem contDiffOn_realHessian_of_rankOne_det {n : ℕ} {S : Set (E n)} {r : ℕ∞ω}
    {B D : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {v : E n → E n} {t f : E n → ℝ}
    (hD : ContDiffOn ℝ r D S) (hv : ContDiffOn ℝ r v S) (hv0 : ∀ x ∈ S, v x ≠ 0)
    (hf : ContDiffOn ℝ r f S) (c : ℝ)
    (hPos : ∀ x ∈ S, (complexHessianOfRealBilinear
      (D x + c • (innerSL ℝ (v x)).smulRight (innerSL ℝ (v x)))).PosDef)
    (hEq : ∀ x ∈ S, B x = D x + t x • (innerSL ℝ (v x)).smulRight (innerSL ℝ (v x)))
    (hDet : ∀ x ∈ S, (complexHessianOfRealBilinear (B x)).det.re = f x) :
    ContDiffOn ℝ r B S := by
  let P (x : E n) := (innerSL ℝ (v x)).smulRight (innerSL ℝ (v x))
  let A (x : E n) := complexHessianOfRealBilinear (D x + c • P x)
  let z (x : E n) := star (complexCoord (v x))
  let s (x : E n) := (t x - c) / 4
  have hP : ContDiffOn ℝ r P S := contDiffOn_realBilinear_rankOne hv
  have hA (i j : Fin n) : ContDiffOn ℝ r (fun x => A x i j) S :=
    contDiffOn_complexHessianOfRealBilinear (hD.add (hP.const_smul c)) i j
  have hz (i : Fin n) : ContDiffOn ℝ r (fun x => z x i) S :=
    Complex.conjCLE.contDiff.comp_contDiffOn ((complexCoordCLM i).contDiff.comp_contDiffOn hv)
  have hz0 (x : E n) (hx : x ∈ S) : z x ≠ 0 := by
    intro h
    apply hv0 x hx
    apply complexCoord_eq_zero_iff.mp
    have he := congrArg star h
    simpa only [z, star_star, star_zero] using he
  have hD' (x : E n) (hx : x ∈ S) :
      (A x + (s x : ℂ) • Matrix.vecMulVec (z x) (star (z x))).det.re = f x := by
    rw [← hDet x hx, hEq x hx]
    congr 2
    have he : D x + c • P x + (t x - c) • P x = D x + t x • P x := by
      have h : c + (t x - c) = t x := by ring
      calc
        _ = D x + ((c + (t x - c)) • P x) := by
          exact (add_assoc _ _ _).trans (congrArg (D x + ·) (add_smul c (t x - c) (P x)).symm)
        _ = _ := congrArg (fun a : ℝ => D x + a • P x) h
    rw [← he]
    simpa only [A, P, s, z, star_star] using
      (complexHessianOfRealBilinear_add_rankOne (D x + c • P x) (v x) (t x - c)).symm
  have hs : ContDiffOn ℝ r s S := contDiffOn_of_hermitianRankOne_det hA hz hPos hz0 hf hD'
  have ht : ContDiffOn ℝ r t S :=
    ((hs.const_smul (4 : ℝ)).add contDiffOn_const).congr fun x _ => by
      change t x = 4 * ((t x - c) / 4) + c
      ring
  have hScaled : ContDiffOn ℝ r (fun x => t x • innerSL ℝ (v x)) S := by
    have hL : ContDiffOn ℝ r (fun x => innerSL ℝ (v x)) S :=
      (innerSL ℝ (E := E n)).contDiff.comp_contDiffOn hv
    exact ht.smul hL
  have hTP : ContDiffOn ℝ r (fun x => t x • P x) S := by
    have hL : ContDiffOn ℝ r (fun x => innerSL ℝ (v x)) S :=
      (innerSL ℝ (E := E n)).contDiff.comp_contDiffOn hv
    exact (hL.smulRight hScaled).congr fun x _ => by
      ext y w
      simp [P, smul_smul, mul_comm]
  exact (hD.add hTP).congr hEq

/-- Removing the radial-radial entry leaves a bilinear field whose
regularity follows from the tangential input of the original field. -/
theorem exists_contDiffOn_realHessian_tangent_split {n : ℕ} {S : Set (E n)} {r : ℕ∞ω}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hAway : ∀ y ∈ S, y ≠ 0)
    (hSym : ∀ y ∈ S, ∀ a b, B y a b = B y b a)
    (hTan : ContDiffOn ℝ r
      (fun y => (B y).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y)) S) :
    ∃ (D : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (t : E n → ℝ),
      ContDiffOn ℝ r D S ∧
      ∀ y ∈ S, B y = D y + t y • (innerSL ℝ y).smulRight (innerSL ℝ y) := by
  let N (y : E n) : E n →L[ℝ] E n :=
    (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y
  let T (y : E n) := (B y).comp (ContinuousLinearMap.id ℝ (E n) - N y)
  let D (y : E n) := T y + (T y).flip.comp (N y)
  let t (y : E n) := B y y y / (‖y‖ ^ 2) ^ 2
  let P (y : E n) := (innerSL ℝ y).smulRight (innerSL ℝ y)
  have hN : ContDiffOn ℝ r N S := by
    have hR : ContDiffOn ℝ r (fun y : E n => (‖y‖ ^ 2)⁻¹) S :=
      ((contDiff_norm_sq ℝ).contDiffOn).inv fun y hy => pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway y hy))
    have hL : ContDiffOn ℝ r (fun y : E n => innerSL ℝ y) S :=
      (innerSL ℝ (E := E n)).contDiff.contDiffOn
    refine ((hR.smul hL).smulRight contDiffOn_id).congr fun y _ => ?_
    ext a : 1
    simp [N, smul_smul]
  have hT : ContDiffOn ℝ r T S := hTan
  let F : (E n →L[ℝ] E n →L[ℝ] ℝ) ≃L[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearEquiv
  have hFC : ContDiff ℝ r (F : (E n →L[ℝ] E n →L[ℝ] ℝ) → (E n →L[ℝ] E n →L[ℝ] ℝ)) :=
    @ContinuousLinearEquiv.contDiff ℝ (E n →L[ℝ] E n →L[ℝ] ℝ) (E n →L[ℝ] E n →L[ℝ] ℝ)
      _ _ _ _ _ r F
  have hFlip : ContDiffOn ℝ r (fun y => (T y).flip) S := hFC.comp_contDiffOn hT
  have hD : ContDiffOn ℝ r D S := hT.add (hFlip.clm_comp hN)
  have hSplit (y : E n) (hy : y ∈ S) : B y = D y + t y • P y := by
    have hNorm : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway y hy))
    ext a b
    simp only [D, T, N, t, P, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, smul_smul]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [hSym y hy b y]
    field_simp
    ring
  exact ⟨D, t, hD, hSplit⟩

/-- On any set away from the origin, regularity of the tangential input
of a symmetric real Hessian and of its determinant recovers the radial entry.
A positive Hessian at a point provides the reference on a relative neighborhood. -/
theorem contDiffWithinAt_realHessian_of_tangent_det {n : ℕ} {S : Set (E n)} {r : ℕ∞ω}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {f : E n → ℝ} {x : E n}
    (hx : x ∈ S) (hx0 : x ≠ 0)
    (hSym : ∀ y ∈ S, ∀ a b, B y a b = B y b a)
    (hTan : ContDiffOn ℝ r
      (fun y => (B y).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y)) S)
    (hf : ContDiffOn ℝ r f S)
    (hPos : (complexHessianOfRealBilinear (B x)).PosDef)
    (hDet : ∀ y ∈ S, (complexHessianOfRealBilinear (B y)).det.re = f y) :
    ContDiffWithinAt ℝ r B S x := by
  let V := {y : E n | y ≠ 0}
  have hV : IsOpen V := isClosed_singleton.isOpen_compl
  obtain ⟨D, t, hD, hSplit⟩ := exists_contDiffOn_realHessian_tangent_split
    (fun _ hy => hy.2) (fun y hy => hSym y hy.1) (hTan.mono inter_subset_left)
  let P (y : E n) := (innerSL ℝ y).smulRight (innerSL ℝ y)
  let c := t x
  let A (y : E n) := complexHessianOfRealBilinear (D y + c • P y)
  have hxSV : x ∈ S ∩ V := ⟨hx, hx0⟩
  have hA0 : (A x).PosDef := by
    change (complexHessianOfRealBilinear (D x + c • P x)).PosDef
    rw [← hSplit x hxSV]
    exact hPos
  have hPC : ContDiffOn ℝ r P (S ∩ V) := contDiffOn_realBilinear_rankOne contDiffOn_id
  have hAC : ContinuousOn A (S ∩ V) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear (hD.add (hPC.const_smul c)) i j).continuousOn
  obtain ⟨U, hU, hxU, hUH⟩ := exists_isOpen_hermitian_posDef_nhds hA0
  have hEv : ∀ᶠ y in 𝓝[S ∩ V] x, A y ∈ U := (hAC x hxSV).eventually (hU.mem_nhds hxU)
  obtain ⟨W, hW, hWS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hEv
  have hxW : x ∈ W := mem_of_mem_nhds hW
  let S' := (S ∩ V) ∩ W
  have hPSD (y : E n) (hy : y ∈ S') : (A y).PosDef := by
    apply hUH (A y) (hWS ⟨hy.2, hy.1⟩)
    have hSymD (a b : E n) : (D y + c • P y) a b = (D y + c • P y) b a := by
      have he : D y + c • P y = B y + (c - t y) • P y := by
        rw [hSplit y hy.1]
        have h : t y + (c - t y) = c := by ring
        exact ((add_assoc (D y) (t y • P y) ((c - t y) • P y)).trans
          (congrArg (D y + ·) ((add_smul (t y) (c - t y) (P y)).symm.trans
            (congrArg (fun a : ℝ => a • P y) h)))).symm
      rw [he]
      simp only [add_apply, smul_apply, smul_eq_mul, P, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply]
      rw [hSym y hy.1.1 a b, mul_comm (inner ℝ y a) (inner ℝ y b)]
    ext i j
    change star (complexHessianOfRealBilinear (D y + c • P y) j i) =
      complexHessianOfRealBilinear (D y + c • P y) i j
    simp only [complexHessianOfRealBilinear, Complex.star_def, map_mul, map_add, map_sub,
      Complex.conj_ofReal, Complex.conj_I, map_inv₀, map_ofNat]
    rw [hSymD (realDirection j) (realDirection i), hSymD (imagDirection j) (imagDirection i),
      hSymD (realDirection j) (imagDirection i), hSymD (imagDirection j) (realDirection i)]
    ring
  have hB' : ContDiffOn ℝ r B S' := contDiffOn_realHessian_of_rankOne_det
    (hD.mono inter_subset_left) contDiffOn_id (fun _ hy => hy.1.2)
    (hf.mono (inter_subset_left.trans inter_subset_left)) c hPSD
    (fun y hy => hSplit y hy.1) (fun y hy => hDet y hy.1.1)
  have hN' : V ∩ W ∈ 𝓝 x := inter_mem (hV.mem_nhds hx0) hW
  have h₁ : ContDiffWithinAt ℝ r B (S ∩ (V ∩ W)) x := by
    rw [← inter_assoc]
    exact hB' x ⟨hxSV, hxW⟩
  exact (contDiffWithinAt_inter hN').mp h₁

end KEBall
