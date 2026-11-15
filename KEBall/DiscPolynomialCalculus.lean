import KEBall.BrezisMerleDiscMass
import KEBall.ComplexMaximum
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial Laplacians on the disc
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric MvPolynomial Set
open scoped BigOperators ContDiff Laplacian Topology

namespace KEBall.DiscPolynomial

local notation "Poly" => MvPolynomial (Fin 2) ℝ

/-- Evaluate a polynomial at the two real Euclidean coordinates of the disc. -/
noncomputable def evaluate (p : Poly) (x : E 1) : ℝ := MvPolynomial.eval (fun i => x i) p

private theorem evaluate_C (a : ℝ) : evaluate (C a) = fun _ => a := by
  funext x
  exact eval_C (f := fun i : Fin 2 => x i) a

private theorem evaluate_add (p q : Poly) : evaluate (p + q) = fun x => evaluate p x + evaluate q x := by
  funext x
  exact map_add (MvPolynomial.eval fun i => x i) p q

private theorem evaluate_mul (p q : Poly) : evaluate (p * q) = fun x => evaluate p x * evaluate q x := by
  funext x
  exact eval_mul

private theorem evaluate_X (i : Fin 2) : evaluate (X i) = (EuclideanSpace.proj i : E 1 →L[ℝ] ℝ) := by
  funext x
  exact eval_X (f := fun j : Fin 2 => x j) i

theorem contDiff_evaluate (p : Poly) : ContDiff ℝ ∞ (evaluate p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [evaluate_C]
    exact contDiff_const
  | add p q hp hq =>
    rw [evaluate_add]
    exact hp.add hq
  | mul_X p i hp =>
    rw [evaluate_mul, evaluate_X]
    exact hp.mul (EuclideanSpace.proj i : E 1 →L[ℝ] ℝ).contDiff

private theorem fderiv_evaluate_basis (p : Poly) (x : E 1) (i : Fin 2) :
    fderiv ℝ (evaluate p) x ((EuclideanSpace.basisFun (Fin 2) ℝ) i) = evaluate (pderiv i p) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [evaluate_C, pderiv_C]
    simp [evaluate]
  | add p q hp hq =>
    rw [evaluate_add, fderiv_fun_add ((contDiff_evaluate p).differentiable (by simp) x)
      ((contDiff_evaluate q).differentiable (by simp) x)]
    simp only [add_apply, hp, hq, Derivation.map_add]
    simp [evaluate]
  | mul_X p j hp =>
    let e := (EuclideanSpace.basisFun (Fin 2) ℝ) i
    rw [evaluate_mul, evaluate_X, fderiv_fun_mul ((contDiff_evaluate p).differentiable (by simp) x)
      (EuclideanSpace.proj j : E 1 →L[ℝ] ℝ).differentiableAt,
      (EuclideanSpace.proj j : E 1 →L[ℝ] ℝ).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, hp,
      Derivation.leibniz, evaluate, map_add, smul_eq_mul, map_mul, pderiv_X, eval_X]
    change evaluate p x * e j + x j * evaluate (pderiv i p) x =
      evaluate p x * evaluate (Pi.single (M := fun _ : Fin 2 => Poly) i 1 j) x +
        x j * evaluate (pderiv i p) x
    congr 2
    simp [e, EuclideanSpace.basisFun_apply, evaluate, Pi.single_apply]

/-- The formal polynomial Laplacian in the two real coordinates. -/
noncomputable def polynomialLaplacian : Poly →ₗ[ℝ] Poly :=
  ∑ i : Fin 2, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

theorem evaluate_polynomialLaplacian (p : Poly) (x : E 1) :
    evaluate (polynomialLaplacian p) x = Δ (evaluate p) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  unfold polynomialLaplacian
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  unfold evaluate
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  let e := (EuclideanSpace.basisFun (Fin 2) ℝ) i
  have he : (fun y : E 1 => fderiv ℝ (evaluate p) y e) = evaluate (pderiv i p) :=
    funext fun y => fderiv_evaluate_basis p y i
  have hh := fderiv_evaluate_basis (pderiv i p) x i
  rw [← he] at hh
  rw [iteratedFDeriv_two_apply]
  change evaluate (pderiv i (pderiv i p)) x = fderiv ℝ (fderiv ℝ (evaluate p)) x e e
  have h₂ : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) + 1 = 2 by norm_num]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  rw [← hh, fderiv_clm_apply
    (((contDiff_evaluate p).fderiv_right (m := 1) h₂).differentiable one_ne_zero x)
    (differentiableAt_const e)]
  simp [ContinuousLinearMap.flip_apply, e]

theorem totalDegree_pderiv_le (p : Poly) (i : Fin 2) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  unfold totalDegree
  apply Finset.sup_le
  intro m hm
  have hmp : m + Finsupp.single i 1 ∈ p.support := by
    rw [mem_support_iff, coeff_pderiv] at hm
    exact mem_support_iff.mpr fun he => hm (by rw [he, zero_mul])
  have h := le_totalDegree hmp
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (h := fun (_ : Fin 2) (d : ℕ) => d) rfl] at h
  exact Nat.le_sub_of_add_le h

theorem totalDegree_laplacian_le (p : Poly) :
    (polynomialLaplacian p).totalDegree ≤ p.totalDegree - 2 := by
  unfold polynomialLaplacian
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  apply totalDegree_finsetSum_le
  intro i _
  change (pderiv i (pderiv i p)).totalDegree ≤ _
  have h := totalDegree_pderiv_le (pderiv i p) i
  have h' := totalDegree_pderiv_le p i
  omega

/-- The weak maximum principle used for polynomial Dirichlet solutions. -/
theorem disc_nonpositive_of_laplacian_nonneg {u : E 1 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ u x)
    (hB : ∀ x ∈ unitSphere 1, u x ≤ 0) :
    ∀ x ∈ closedUnitBall 1, u x ≤ 0 := by
  intro z hz
  by_contra! hpos
  let ε : ℝ := u z / 2
  let q : E 1 → ℝ := fun x => ‖x‖ ^ 2 - 1
  let w : E 1 → ℝ := fun x => u x + ε • q x
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hq : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).sub contDiff_const
  have hw : ContDiff ℝ ∞ w := hu.add (hq.const_smul _)
  have hwpos : 0 < w z := by
    change 0 < u z + ε * (‖z‖ ^ 2 - 1)
    have h := mul_nonneg hε.le (sq_nonneg ‖z‖)
    dsimp [ε] at h ⊢
    linarith
  obtain ⟨x, hx, hMax⟩ := (isCompact_closedBall (0 : E 1) 1).exists_isMaxOn
    ⟨z, hz⟩ hw.continuous.continuousOn
  have hwx : 0 < w x := hwpos.trans_le (hMax hz)
  have hxS : x ∉ unitSphere 1 := by
    intro hxs
    have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hxs
    have hwle : w x ≤ 0 := by simpa [w, q, hnorm] using hB x hxs
    exact hwle.not_gt hwx
  have hxB : x ∈ unitBall 1 := by
    rw [unitBall, ← closedBall_sdiff_sphere]
    exact ⟨hx, hxS⟩
  have hloc := hMax.localize.isLocalMax
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hxB) ball_subset_closedBall)
  have hL : Δ w x ≤ 0 := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w
      (EuclideanSpace.basisFun (Fin 2) ℝ)]
    apply Finset.sum_nonpos
    intro i _
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, realHessian] using
      realHessian_nonpos_of_isLocalMax hw.contDiffAt hloc ((EuclideanSpace.basisFun (Fin 2) ℝ) i)
  have h₂ : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hΔw : Δ w x = Δ u x + ε * 4 := by
    have hqu : ContDiffAt ℝ 2 (ε • q) x := ((hq.of_le h₂).const_smul ε).contDiffAt
    change Δ (u + ε • q) x = _
    rw [(hu.of_le h₂).contDiffAt.laplacian_add hqu,
      InnerProductSpace.laplacian_smul ε (hq.of_le h₂).contDiffAt, smul_eq_mul,
      show Δ q x = 4 from BrezisMerle.laplacian_disc_quadratic x]
  rw [hΔw] at hL
  linarith [hΔ x hxB]

end KEBall.DiscPolynomial
