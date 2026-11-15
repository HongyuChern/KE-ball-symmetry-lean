import KEBall.DirichletAngularPotentialL2

/-!
# Mixed angular Hessians via polarization and the exact bracket

For X_S u = du(Sx), [X_S,X_T] = X_(TS-ST).  This lower-order
bracket is retained when passing from pure second derivatives to mixed ones.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

theorem dirichlet_fderiv_linearFieldDerivative {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (T : E n →L[ℝ] E n) (v : E n) :
    fderiv ℝ (fun y => fderiv ℝ u y (T y)) x v =
      realHessian u x v (T x) + fderiv ℝ u x (T v) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have h := hd.clm_apply (T.hasFDerivAt (x := x))
  rw [h.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, realHessian, add_comm]

theorem dirichlet_mixedAngularDerivative_polarization {n : ℕ}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (S T : E n →L[ℝ] E n) :
    fderiv ℝ (fun y => fderiv ℝ u y (T y)) x (S x) =
      (1 / 2 : ℝ) *
        (fderiv ℝ (fun y => fderiv ℝ u y ((S + T) y)) x ((S + T) x) -
          fderiv ℝ (fun y => fderiv ℝ u y (S y)) x (S x) -
          fderiv ℝ (fun y => fderiv ℝ u y (T y)) x (T x) +
          fderiv ℝ u x ((T * S - S * T) x)) := by
  rw [dirichlet_fderiv_linearFieldDerivative hu T (S x),
    dirichlet_fderiv_linearFieldDerivative hu (S + T) ((S + T) x),
    dirichlet_fderiv_linearFieldDerivative hu S (S x),
    dirichlet_fderiv_linearFieldDerivative hu T (T x)]
  simp only [_root_.add_apply,
    _root_.sub_apply, ContinuousLinearMap.mul_apply, map_add, map_sub]
  rw [realHessian_symm hu (T x) (S x)]
  ring

theorem memLp_realHessian_mixedAngularDerivative_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S T : E n →L[ℝ] E n) (hS : star S = -S) (hT : star T = -T)
    (hSJ : ∀ x, S (J x) = J (S x)) (hTJ : ∀ x, T (J x) = J (T x)) :
    MemLp (realHessian (fun y => fderiv ℝ (fun z => fderiv ℝ u z (T z)) y (S y)))
      2 ((volume0 n).restrict (unitBall n)) := by
  let B := T * S - S * T
  let Q (L : E n →L[ℝ] E n) (y : E n) :=
    fderiv ℝ (fun z => fderiv ℝ u z (L z)) y (L y)
  let b (y : E n) := fderiv ℝ u y (B y)
  have hSum : star (S + T) = -(S + T) := by simp only [star_add, hS, hT, neg_add]
  have hB : star B = -B := by
    dsimp only [B]
    simp only [star_sub, star_mul, hS, hT, neg_mul_neg]
    abel
  have hSumJ (x : E n) : (S + T) (J x) = J ((S + T) x) := by
    simp only [_root_.add_apply, hSJ, hTJ]
    simpa only [JCLM_apply] using ((JCLM n).map_add (S x) (T x)).symm
  have hBJ (x : E n) : B (J x) = J (B x) := by
    simp only [B, _root_.sub_apply, ContinuousLinearMap.mul_apply, hSJ, hTJ]
    simpa only [JCLM_apply] using ((JCLM n).map_sub (T (S x)) (S (T x))).symm
  have hS₂ := memLp_realHessian_secondAngularDerivative_of_C2_solution hn hu huS hu0 hPos hf hEq S hS hSJ
  have hT₂ := memLp_realHessian_secondAngularDerivative_of_C2_solution hn hu huS hu0 hPos hf hEq T hT hTJ
  have hSum₂ := memLp_realHessian_secondAngularDerivative_of_C2_solution hn hu huS hu0 hPos hf hEq
    (S + T) hSum hSumJ
  have hB₁ := memLp_realHessian_firstAngularDerivative_of_C2_solution hn hu huS hu0 hPos hf hEq B hB hBJ
  have hMem : MemLp (fun x => (1 / 2 : ℝ) •
      (realHessian (Q (S + T)) x - realHessian (Q S) x - realHessian (Q T) x + realHessian b x))
      2 ((volume0 n).restrict (unitBall n)) :=
    (((hSum₂.sub hS₂).sub hT₂).add hB₁).const_smul (1 / 2 : ℝ)
  have hQC (L : E n →L[ℝ] E n) : ContDiffOn ℝ 2 (Q L) (unitBall n) :=
    ((((huS.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
      L.contDiff.contDiffOn).fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
        L.contDiff.contDiffOn).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hbC : ContDiffOn ℝ 2 b (unitBall n) :=
    ((huS.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
      B.contDiff.contDiffOn).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine MemLp.ae_eq ?_ hMem
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  have he : (fun y => fderiv ℝ (fun z => fderiv ℝ u z (T z)) y (S y)) =ᶠ[𝓝 x]
      (1 / 2 : ℝ) • (Q (S + T) - Q S - Q T + b) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichlet_mixedAngularDerivative_polarization
      (huS.contDiffAt (isOpen_ball.mem_nhds hy)) S T
  have hAt (L : E n →L[ℝ] E n) := (hQC L).contDiffAt (isOpen_ball.mem_nhds hx)
  have hbAt := hbC.contDiffAt (isOpen_ball.mem_nhds hx)
  have hH : realHessian (fun y => fderiv ℝ (fun z => fderiv ℝ u z (T z)) y (S y)) x =
      realHessian ((1 / 2 : ℝ) • (Q (S + T) - Q S - Q T + b)) x := he.fderiv.fderiv_eq
  rw [hH, dirichlet_realHessian_smul_C2
    (u := Q (S + T) - Q S - Q T + b)
    ((((hAt (S + T)).sub (hAt S)).sub (hAt T)).add hbAt),
    dirichlet_realHessian_add_C2 (u := Q (S + T) - Q S - Q T) (v := b)
      (((hAt (S + T)).sub (hAt S)).sub (hAt T)) hbAt,
    dirichlet_realHessian_sub_C2 (u := Q (S + T) - Q S) (v := Q T)
      ((hAt (S + T)).sub (hAt S)) (hAt T),
    dirichlet_realHessian_sub_C2 (u := Q (S + T)) (v := Q S) (hAt (S + T)) (hAt S)]

end KEBall
