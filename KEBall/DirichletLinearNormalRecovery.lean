import KEBall.DirichletAnnularRecovery

/-! Normal recovery for the linearized determinant. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

/-- The cofactor equation determines the missing real rank-one coefficient
by division by the strictly positive normal coefficient. -/
theorem contDiffOn_of_hermitianRankOne_linearized_det {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {r : ℕ∞ω} {S : Set X}
    {A D : X → Matrix (Fin n) (Fin n) ℂ} {z : X → Fin n → ℂ} {t f : X → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) S)
    (hD : ∀ i j, ContDiffOn ℝ r (fun x => D x i j) S)
    (hz : ∀ i, ContDiffOn ℝ r (fun x => z x i) S)
    (hP : ∀ x ∈ S, (A x).PosDef) (hZ : ∀ x ∈ S, z x ≠ 0)
    (hf : ContDiffOn ℝ r f S)
    (hEq : ∀ x ∈ S,
      ((A x).adjugate * (D x + (t x : ℂ) • Matrix.vecMulVec (z x) (star (z x)))).trace.re = f x) :
    ContDiffOn ℝ r t S := by
  let g (x : X) := ((A x).adjugate * D x).trace.re
  have hG : ContDiffOn ℝ r g S := by
    apply Complex.reCLM.contDiff.comp_contDiffOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact ContDiffOn.sum fun i _ =>
      ContDiffOn.sum fun j _ => (contDiffOn_adjugate_of_contDiffOn_entries hA i j).mul (hD j i)
  have he (x : X) (hx : x ∈ S) :
      t x = (f x - g x) / hermitianRankOneDetSlope (A x) (z x) := by
    rw [eq_div_iff (hermitianRankOneDetSlope_pos (hP x hx) (hZ x hx)).ne', ← hEq x hx]
    have hTrace (M : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
        (M * Matrix.vecMulVec u w).trace = w ⬝ᵥ (M *ᵥ u) := by
      rw [Matrix.mul_vecMulVec]
      simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct, mul_comm]
    simp only [g, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hTrace, hermitianRankOneDetSlope]
    ring
  exact ((hf.sub hG).div (contDiffOn_hermitianRankOneDetSlope hA hz)
    (fun x hx => (hermitianRankOneDetSlope_pos (hP x hx) (hZ x hx)).ne')).congr he

/-- A cofactor equation determines the regularity of the full symmetric
Hessian from its tangential input on a set away from the center. -/
theorem contDiffOn_realHessian_of_tangent_linearized_det {n : ℕ}
    {S : Set (E n)} {r : ℕ∞ω}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    {A : E n → Matrix (Fin n) (Fin n) ℂ} {f : E n → ℝ}
    (hAway : ∀ y ∈ S, y ≠ 0) (hSym : ∀ y ∈ S, ∀ a b, B y a b = B y b a)
    (hTan : ContDiffOn ℝ r
      (fun y => (B y).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y)) S)
    (hf : ContDiffOn ℝ r f S)
    (hA : ∀ i j, ContDiffOn ℝ r (fun y => A y i j) S)
    (hPos : ∀ y ∈ S, (A y).PosDef)
    (hEq : ∀ y ∈ S, ((A y).adjugate * complexHessianOfRealBilinear (B y)).trace.re = f y) :
    ContDiffOn ℝ r B S := by
  obtain ⟨D, t, hD, hSplit⟩ := exists_contDiffOn_realHessian_tangent_split hAway hSym hTan
  let z (y : E n) := star (complexCoord y)
  let s (y : E n) := t y / 4
  have hz (i : Fin n) : ContDiffOn ℝ r (fun y => z y i) S :=
    Complex.conjCLE.contDiff.comp_contDiffOn (complexCoordCLM i).contDiff.contDiffOn
  have hz0 (y : E n) (hy : y ∈ S) : z y ≠ 0 := by
    intro h
    apply hAway y hy
    apply complexCoord_eq_zero_iff.mp
    simpa only [z, star_star, star_zero] using congrArg star h
  have hs : ContDiffOn ℝ r s S := by
    refine contDiffOn_of_hermitianRankOne_linearized_det hA
      (contDiffOn_complexHessianOfRealBilinear hD) hz hPos hz0 hf ?_
    intro y hy
    have he := complexHessianOfRealBilinear_add_rankOne (D y) y (t y)
    rw [← hSplit y hy] at he
    simpa only [s, z, star_star, ← he] using hEq y hy
  have ht : ContDiffOn ℝ r t S :=
    (hs.const_smul (4 : ℝ)).congr fun y _ => by
      change t y = 4 * (t y / 4)
      ring
  have hL : ContDiffOn ℝ r (fun y : E n => innerSL ℝ y) S :=
    (innerSL ℝ (E := E n)).contDiff.contDiffOn
  have hTP : ContDiffOn ℝ r
      (fun y : E n => t y • (innerSL ℝ y).smulRight (innerSL ℝ y)) S := by
    refine (hL.smulRight (ht.smul hL)).congr fun y _ => ?_
    ext a b
    simp [smul_smul, mul_comm]
  exact (hD.add hTP).congr hSplit

/-- The cofactor equation supplies all second derivatives from the
first derivatives along a finite family of unitary fields. -/
theorem contDiffOn_fderivWithin_fderivWithin_of_unitaryRotations_linearized_det {n r : ℕ}
    {S : Set (E n)} (hS : UniqueDiffOn ℝ S)
    (hClosure : S ⊆ closure (interior S)) (hAway : ∀ x ∈ S, x ≠ 0)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {u f : E n → ℝ}
    {A : E n → Matrix (Fin n) (Fin n) ℂ}
    (hu2 : ContDiffOn ℝ 2 u S) (hu : ContDiffOn ℝ (r + 1 : ℕ) u S)
    (hRot : ∀ i j, ContDiffOn ℝ (r + 1 : ℕ) (fun x =>
      fderivWithin ℝ u S x (dirichletUnitaryRotation (b i) (b j) x)) S)
    (hJ : ContDiffOn ℝ (r + 1 : ℕ) (fun x => fderivWithin ℝ u S x (J x)) S)
    (hf : ContDiffOn ℝ r f S)
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) S)
    (hPos : ∀ x ∈ S, (A x).PosDef)
    (hEq : ∀ x ∈ S, ((A x).adjugate * complexHessianOfRealBilinear
      (fderivWithin ℝ (fderivWithin ℝ u S) S x)).trace.re = f x) :
    ContDiffOn ℝ r (fderivWithin ℝ (fderivWithin ℝ u S) S) S := by
  refine contDiffOn_realHessian_of_tangent_linearized_det hAway ?_ ?_ hf hA hPos hEq
  · intro x hx a c
    exact ((hu2 x hx).isSymmSndFDerivWithinAt (by simp) hS (hClosure hx) hx).eq a c
  · refine contDiffOn_tangentHessian_of_unitaryRotations b hAway ?_ ?_
    · intro i j
      exact contDiffOn_fderivWithin_fderivWithin_apply_of_rotation hS (Subset.rfl)
        hClosure hu2 hu _ (hRot i j)
    · simpa only [JCLM_apply] using
        (contDiffOn_fderivWithin_fderivWithin_apply_of_rotation hS (Subset.rfl)
          hClosure hu2 hu (JCLM n) (by simpa only [JCLM_apply] using hJ))

/-- Near the sphere a cofactor equation and one extra angular derivative
increase the regularity of the potential by one order. -/
theorem contDiffOn_closedBall_inter_succ_of_angularDerivatives_linearized_det {n r : ℕ}
    {U : Set (E n)} (hU : IsOpen U) (hAway : (0 : E n) ∉ U)
    {u f : E n → ℝ} (hu2 : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hu : ContDiffOn ℝ (r + 1 : ℕ) u (closedUnitBall n ∩ U))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (hRot : ∀ i j, ContDiffOn ℝ (r + 1 : ℕ)
      (dirichletAngularDerivative (dirichletUnitaryRotation (b i) (b j)) u) (closedUnitBall n ∩ U))
    (hJ : ContDiffOn ℝ (r + 1 : ℕ)
      (dirichletAngularDerivative (JCLM n) u) (closedUnitBall n ∩ U))
    (hf : ContDiffOn ℝ r f (closedUnitBall n ∩ U))
    {A : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) (closedUnitBall n ∩ U))
    (hPos : ∀ x ∈ closedUnitBall n ∩ U, (A x).PosDef)
    (hEq : ∀ x ∈ closedUnitBall n ∩ U, ((A x).adjugate * complexHessianOfRealBilinear
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n) x)).trace.re = f x) :
    ContDiffOn ℝ (r + 2 : ℕ) u (closedUnitBall n ∩ U) := by
  apply contDiffOn_closedBall_inter_succ_of_withinHessian hU hu2 b hRot hJ
  dsimp only
  intro hT hClosure hRot' hJ' hD₂
  exact contDiffOn_fderivWithin_fderivWithin_of_unitaryRotations_linearized_det hT hClosure
    (fun x hx h => hAway (h ▸ hx.2)) b (hu2.mono inter_subset_left) hu
    hRot' hJ' hf hA hPos (fun x hx => hD₂ x hx ▸ hEq x hx)

end KEBall
