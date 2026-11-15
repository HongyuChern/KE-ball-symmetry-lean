import KEBall.ComplexProductBall
import KEBall.FiberEnergyDeterminantBound

/-!
# The fiber block of the Bedford–Taylor Hessian
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder ContDiff

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

/-- Reindex the ambient Hessian into its fiber and base coordinates. -/
noncomputable def complexProductHessian {n m : ℕ}
    (u : ComplexModel (n + m) → ℝ) (x : ComplexModel (n + m)) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
  (modelHessian u x).submatrix finSumFinEquiv finSumFinEquiv

theorem complexProductHessian_det {n m : ℕ}
    (u : ComplexModel (n + m) → ℝ) (x : ComplexModel (n + m)) :
    (complexProductHessian (n := n) (m := m) u x).det = (modelHessian u x).det :=
  Matrix.det_submatrix_equiv_self _ _

theorem complexProductHessian_fiber {n m : ℕ} {u : ComplexModel (n + m) → ℝ}
    (hu : ContDiff ℝ 2 u) (x : ComplexModel (n + m)) :
    (complexProductHessian (n := n) (m := m) u x).toBlocks₁₁ =
      modelHessian (fun z => u ((complexProductCoordinates n m).symm
        (z, (complexProductCoordinates n m x).2))) (complexProductCoordinates n m x).1 := by
  let e := complexProductCoordinates n m
  let w := (e x).2
  let z := (e x).1
  let Lc : ComplexModel n →L[ℂ] ComplexModel (n + m) :=
    e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ (ComplexModel n) (ComplexModel m))
  let L := Lc.restrictScalars ℝ
  have hL (a : ComplexModel n) : L a = e.symm (a, 0) := rfl
  have hAffine (a : ComplexModel n) : e.symm (0, w) + L a = e.symm (a, w) := by
    rw [hL, ← map_add]
    simp
  have hx : e.symm (z, w) = x := e.symm_apply_apply x
  have hess (a b : ComplexModel n) :
      PshLines.realHessian (fun z' => u (e.symm (z', w))) z a b =
        PshLines.realHessian u x (L a) (L b) := by
    simpa only [hAffine, hx] using PshLines.realHessian_comp_affine hu L (e.symm (0, w)) z a b
  have hvec (i : Fin n) :
      L (coordinateVector i) = coordinateVector (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin m)) := by
    rw [hL, ← complexProductCoordinates_coordinateVector_inl (n := n) (m := m) i]
    exact e.symm_apply_apply _
  have hI (i : Fin n) :
      L (Complex.I • coordinateVector i) =
        Complex.I • coordinateVector (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin m)) := by
    change Lc (Complex.I • coordinateVector i) = _
    rw [map_smul]
    exact congrArg (Complex.I • ·) (hvec i)
  ext i j : 1
  change modelHessian u x (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin m))
    (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin m)) =
    modelHessian (fun z' => u (e.symm (z', w))) z i j
  simp only [PshLines.FirstPass.MongeAmpere.complexHessian, hess, hvec, hI]

/-- A base-direction Hessian bound gives a pointwise determinant bound
with the genuine vertical Hessian determinant as its weight. -/
theorem complexHessian_det_re_le_fiber_mul_of_base_bound {n : ℕ}
    {u : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ 2 u) {x : ComplexModel (n + 1)}
    (hP : (modelHessian u x).PosSemidef) {C : ℝ}
    (hBase : ∀ y : ComplexModel (n + 1), (complexProductCoordinates n 1 y).1 = 0 →
      PshLines.realHessian u x y y ≤ C * ‖y‖ ^ 2) :
    (modelHessian u x).det.re ≤
      (modelHessian (fun z => u ((complexProductCoordinates n 1).symm
        (z, (complexProductCoordinates n 1 x).2))) (complexProductCoordinates n 1 x).1).det.re *
        (C / 2) := by
  let e := complexProductCoordinates n 1
  let H := complexProductHessian (n := n) (m := 1) u x
  let v := coordinateVector (finSumFinEquiv (Sum.inr 0 : Fin n ⊕ Fin 1))
  have hH : H.PosSemidef := hP.submatrix _
  have hposA : H.toBlocks₁₁.PosSemidef := hH.submatrix Sum.inl
  have hdetNonneg : 0 ≤ H.toBlocks₁₁.det.re :=
    (RCLike.nonneg_iff.mp hposA.det_nonneg).1
  have hv : (e v).1 = 0 :=
    congrArg Prod.fst (complexProductCoordinates_coordinateVector_inr (n := n) (m := 1) 0)
  have hvI : (e (Complex.I • v)).1 = 0 := by rw [map_smul, Prod.smul_fst, hv, smul_zero]
  have hvn : ‖v‖ = 1 := by
    change ‖PiLp.single (β := fun _ : Fin (n + 1) => ℂ) 2 _ 1‖ = 1
    simp only [PiLp.norm_single, norm_one]
  have h₁ := hBase v hv
  have h₂ := hBase (Complex.I • v) hvI
  rw [hvn, one_pow, mul_one] at h₁
  rw [norm_smul, Complex.norm_I, one_mul, hvn, one_pow, mul_one] at h₂
  have hD : (H.toBlocks₂₂ 0 0).re ≤ C / 2 := by
    change (modelHessian u x (finSumFinEquiv (Sum.inr 0 : Fin n ⊕ Fin 1))
      (finSumFinEquiv (Sum.inr 0 : Fin n ⊕ Fin 1))).re ≤ _
    simp only [PshLines.FirstPass.MongeAmpere.complexHessian, Complex.add_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im,
      zero_mul, mul_zero, one_mul, sub_zero, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat]
    dsimp only [v] at h₁ h₂
    linarith only [h₁, h₂]
  have h := (MoserTrudinger.det_re_le_fiber_mul_base hH).trans
    (mul_le_mul_of_nonneg_left hD hdetNonneg)
  change (complexProductHessian (n := n) (m := 1) u x).det.re ≤
    (complexProductHessian (n := n) (m := 1) u x).toBlocks₁₁.det.re * (C / 2) at h
  rwa [complexProductHessian_det, complexProductHessian_fiber hu] at h

end KEBall.BedfordTaylor
