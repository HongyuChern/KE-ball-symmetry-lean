import KEBall.DirichletGradient
import KEBall.SphereDifferential
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! The Miranda–Talenti identity for zero boundary data on the unit ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Laplacian Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private noncomputable def hessianTrace {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, realHessian u x (e[n] i) (e[n] i)

private theorem hessianTrace_eq_laplacian {n : ℕ} (u : E n → ℝ) (x : E n) :
    hessianTrace u x = Δ u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u e[n]]
  simp only [hessianTrace, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

private noncomputable def mirandaTalentiField {n : ℕ} (u : E n → ℝ) (x : E n) : E n :=
  hessianTrace u x • euclideanGradient u x -
    ∑ j, fderiv ℝ u x (e[n] j) • euclideanGradient (fun y => fderiv ℝ u y (e[n] j)) x

private theorem mirandaTalentiField_contDiffOn {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (mirandaTalentiField u) U := by
  have hT : ContDiffOn ℝ ∞ (hessianTrace u) U := by
    apply ContDiffOn.sum
    intro i _
    have hD := (hu.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)
    exact (hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hG {w : E n → ℝ} (hw : ContDiffOn ℝ ∞ w U) :
      ContDiffOn ℝ ∞ (euclideanGradient w) U :=
    fun x hx => (euclideanGradient_contDiffAt (hw.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  refine (hT.smul (hG hu)).sub ?_
  exact ContDiffOn.sum fun j _ => (contDiffOn_directionalDerivative hU hu (e[n] j)).smul
    (hG (contDiffOn_directionalDerivative hU hu (e[n] j)))

private theorem mirandaTalentiField_coord {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U) (i : Fin (2 * n)) :
    mirandaTalentiField u x i = hessianTrace u x * fderiv ℝ u x (e[n] i) -
      ∑ j, fderiv ℝ u x (e[n] j) * realHessian u x (e[n] i) (e[n] j) := by
  change (EuclideanSpace.proj i : E n →L[ℝ] ℝ) (mirandaTalentiField u x) = _
  simp only [mirandaTalentiField, map_sub, map_smul, map_sum, smul_eq_mul,
    EuclideanSpace.coe_proj, euclideanGradient_coord,
    fderiv_firstDerivative_apply (hu.contDiffAt (hU.mem_nhds hx))]

private theorem mirandaTalentiField_divergence {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U) :
    euclideanDivergence (mirandaTalentiField u) x =
      (Δ u x) ^ 2 - ∑ i, ∑ j, (realHessian u x (e[n] i) (e[n] j)) ^ 2 := by
  let d (i : Fin (2 * n)) (y : E n) := fderiv ℝ u y (e[n] i)
  let h (i j : Fin (2 * n)) (y : E n) := realHessian u y (e[n] i) (e[n] j)
  let k (i j l : Fin (2 * n)) := realThirdDerivative u x (e[n] i) (e[n] j) (e[n] l)
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hd (i : Fin (2 * n)) : DifferentiableAt ℝ (d i) x :=
    ((contDiffOn_directionalDerivative hU hu (e[n] i)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hh (i j : Fin (2 * n)) : DifferentiableAt ℝ (h i j) x :=
    (((realHessian_contDiffAt huAt).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hD (i j : Fin (2 * n)) : fderiv ℝ (d j) x (e[n] i) = h i j x :=
    fderiv_firstDerivative_apply huAt _ _
  have hH (i j l : Fin (2 * n)) : fderiv ℝ (h j l) x (e[n] i) = k i j l :=
    fderiv_realHessian_apply huAt _ _ _
  have hSymm (i j : Fin (2 * n)) : k i j j = k j j i := by
    dsimp [k]
    rw [realThirdDerivative_symm12 huAt (e[n] i) (e[n] j),
      realThirdDerivative_symm23 hU hu hx (e[n] j) (e[n] i) (e[n] j)]
  have hT : DifferentiableAt ℝ (hessianTrace u) x :=
    DifferentiableAt.fun_sum fun j _ => hh j j
  have hT' (i : Fin (2 * n)) : fderiv ℝ (hessianTrace u) x (e[n] i) = ∑ j, k i j j := by
    unfold hessianTrace
    rw [fderiv_fun_sum (fun j _ => hh j j)]
    simp only [sum_apply, hH]
  have hf (i : Fin (2 * n)) : fderiv ℝ (fun y => mirandaTalentiField u y i) x (e[n] i) =
      ((∑ j, k i j j) * d i x + hessianTrace u x * h i i x) -
        ∑ j, (h i j x ^ 2 + d j x * k i i j) := by
    have he : (fun y => mirandaTalentiField u y i) =ᶠ[𝓝 x]
        (fun y => hessianTrace u y * d i y - ∑ j, d j y * h i j y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact mirandaTalentiField_coord hU hu hy i
    let P (y : E n) := hessianTrace u y * d i y
    let Q (j : Fin (2 * n)) (y : E n) := d j y * h i j y
    have hP : DifferentiableAt ℝ P x := hT.mul (hd i)
    have hQ (j : Fin (2 * n)) : DifferentiableAt ℝ (Q j) x := (hd j).mul (hh i j)
    rw [he.fderiv_eq]
    change fderiv ℝ (fun y => P y - ∑ j, Q j y) x (e[n] i) = _
    rw [fderiv_fun_sub hP (DifferentiableAt.fun_sum fun j _ => hQ j),
      fderiv_fun_sum (fun j _ => hQ j)]
    unfold P Q
    rw [fderiv_fun_mul hT (hd i)]
    simp only [_root_.sub_apply, _root_.add_apply,
      sum_apply, _root_.smul_apply, smul_eq_mul, hD, hT']
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      rw [fderiv_fun_mul (hd j) (hh i j)]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hD, hH]
      ring
  have hc : (∑ i, (∑ j, k i j j) * d i x) = ∑ i, ∑ j, d j x * k i i j := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSymm j i, mul_comm]
  simp only [euclideanDivergence, hf, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∑ i, (∑ j, k i j j) * d i x) + hessianTrace u x * hessianTrace u x -
    ((∑ i, ∑ j, h i j x ^ 2) + ∑ i, ∑ j, d j x * k i i j) = _
  rw [hc, hessianTrace_eq_laplacian]
  ring


private theorem mirandaTalentiField_flux {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) :
    inner ℝ x (mirandaTalentiField u x) =
      (2 * n - 1 : ℝ) * (fderiv ℝ u x x) ^ 2 := by
  let b := e[n]
  let a := 2 * boundarySlope u x
  let L := fderiv ℝ (boundarySlope u) x
  let c (j : Fin (2 * n)) := inner ℝ x (b j)
  have huAt := hu.contDiffAt (sphere_subset_closedBall hx)
  have hRep : (∑ j, c j • b j) = x := by
    have h (j : Fin (2 * n)) : c j = b.repr x j := by
      rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
    simp only [h]
    exact b.sum_repr x
  have hMap (D : E n →L[ℝ] ℝ) : (∑ j, c j * D (b j)) = D x := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg (fun y => D y) hRep
  have hC2 : (∑ j, c j ^ 2) = 1 := by
    simpa only [c, real_inner_comm x, sphere_inner_self hx, pow_two] using b.sum_inner_mul_inner x x
  have hDer (v : E n) : fderiv ℝ u x v = a * inner ℝ x v := sphere_fderiv_normal hu hu0 hx v
  have hDerX : fderiv ℝ u x x = a := by rw [hDer, sphere_inner_self hx, mul_one]
  have hInner (w : E n → ℝ) : inner ℝ x (euclideanGradient w x) = fderiv ℝ w x x := by
    rw [real_inner_comm, inner_euclideanGradient]
  have hFlux : inner ℝ x (mirandaTalentiField u x) = a * (hessianTrace u x - realHessian u x x x) := by
    simp only [mirandaTalentiField, inner_sub_right, real_inner_smul_right, inner_sum, hInner, hDerX,
      fderiv_firstDerivative_apply huAt]
    change hessianTrace u x * a - (∑ j, fderiv ℝ u x (b j) * realHessian u x x (b j)) = _
    have hSum : (∑ j, fderiv ℝ u x (b j) * realHessian u x x (b j)) =
        a * realHessian u x x x := by
      simp_rw [hDer, mul_assoc, ← Finset.mul_sum]
      exact congrArg (a * ·) (hMap (realHessian u x x))
    rw [hSum]
    ring
  have hTrace : hessianTrace u x = (2 * n : ℝ) * a + 4 * L x -
      (2 * L x + 2 * a) := by
    have hEntry (j : Fin (2 * n)) :
        realHessian u x (b j) (b j) =
          a + 4 * (c j * L (b j)) - (2 * L x + 2 * a) * c j ^ 2 := by
      rw [sphere_realHessian_decomposition hu hu0 hx, real_inner_self_eq_norm_sq,
        b.orthonormal.norm_eq_one j]
      dsimp only [a, c, L]
      ring
    change (∑ j, realHessian u x (b j) (b j)) = _
    simp only [hEntry, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    rw [hMap, hC2, mul_one]
  have hNormal : realHessian u x x x = 2 * L x - a := by
    have h := fderiv_boundarySlope huAt x
    dsimp only [L, a] at *
    rw [h, hDerX]
    ring
  rw [hFlux, hTrace, hNormal, hDerX]
  ring

/-- For smooth zero-boundary data the difference between the squared Laplacian
and the squared Hilbert–Schmidt norm of the Hessian is a nonnegative boundary term. -/
theorem mirandaTalenti_identity_on_unitBall {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    (∫ x in unitBall n, (Δ u x) ^ 2 ∂volume0 n) -
      (∫ x in unitBall n, ∑ i, ∑ j, (realHessian u x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) =
      (2 * n : ℝ) * (2 * n - 1 : ℝ) *
        ∫ θ : Sphere n, (fderiv ℝ u θ.val θ.val) ^ 2 ∂sphere0 n := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hGreen := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hSub
    ((mirandaTalentiField_contDiffOn hU huU).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  let p (x : E n) := (Δ u x) ^ 2
  let q (x : E n) := ∑ i, ∑ j, (realHessian u x (e[n] i) (e[n] j)) ^ 2
  have hH := (huU.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hEntry (i j : Fin (2 * n)) :
      ContinuousOn (fun x => realHessian u x (e[n] i) (e[n] j)) U :=
    ((hH.clm_apply contDiffOn_const).clm_apply contDiffOn_const).continuousOn
  have hP : ContinuousOn p U := by
    simp only [p, ← hessianTrace_eq_laplacian]
    exact (continuousOn_finsetSum Finset.univ fun i _ => hEntry i i).pow 2
  have hQ : ContinuousOn q U := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ => (hEntry i j).pow 2
  have hI {w : E n → ℝ} (hw : ContinuousOn w U) : IntegrableOn w (unitBall n) (volume0 n) :=
    (hw.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hDiv :
      (∫ x in unitBall n, euclideanDivergence (mirandaTalentiField u) x ∂volume0 n) =
        ∫ x in unitBall n, (p - q) x ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    exact mirandaTalentiField_divergence hU huU (hSub (ball_subset_closedBall hx))
  rw [hDiv] at hGreen
  change (∫ x in unitBall n, p x - q x ∂volume0 n) = _ at hGreen
  rw [integral_sub (hI hP) (hI hQ)] at hGreen
  have hFlux (θ : Sphere n) : inner ℝ θ.val (mirandaTalentiField u θ.val) =
      (2 * n - 1 : ℝ) * (fderiv ℝ u θ.val θ.val) ^ 2 :=
    mirandaTalentiField_flux ⟨U, hU, hSub, huU⟩ hu0 θ.property
  simp only [hFlux] at hGreen
  rw [integral_const_mul, ← mul_assoc] at hGreen
  exact hGreen

end KEBall
