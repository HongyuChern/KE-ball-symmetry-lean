import KEBall.DirichletTangentProjection
import KEBall.DirichletWeakHessian
import Mathlib.Tactic.Module

/-! Smooth coefficient identities for recovering radial weak derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- The radial rank-one tensor, scaled by the squared radius. -/
noncomputable def dirichletRadialTensor {n : ℕ} (x : E n) : E n →L[ℝ] E n :=
  rankOne ℝ x x

/-- The tangential projection scaled by the squared radius. -/
noncomputable def dirichletTangentTensor {n : ℕ} (x : E n) : E n →L[ℝ] E n :=
  ‖x‖ ^ 2 • ContinuousLinearMap.id ℝ (E n) - dirichletRadialTensor x

theorem dirichletRadialTensor_apply {n : ℕ} (x v : E n) :
    dirichletRadialTensor x v = inner ℝ x v • x := rankOne_apply _ _ _

theorem dirichletTangentTensor_apply {n : ℕ} (x v : E n) :
    dirichletTangentTensor x v = ‖x‖ ^ 2 • v - inner ℝ v x • x := by
  simp only [dirichletTangentTensor, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    dirichletRadialTensor_apply, real_inner_comm v x]

theorem contDiff_rankOne_real {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {X Y : D → F}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun x => rankOne ℝ (X x) (Y x)) := by
  have hR : IsBoundedBilinearMap ℝ (fun p : F × F => rankOne ℝ p.1 p.2) := by
    refine ⟨?_, ?_, ?_, ?_, ⟨1, zero_lt_one, fun x y => by simp⟩⟩
    · intro x₁ x₂ y
      ext z
      simp [rankOne_apply]
    · intro c x y
      ext z
      simp only [rankOne_apply, smul_apply]
      exact smul_comm (inner ℝ y z) c x
    · intro x y₁ y₂
      ext z
      simp [rankOne_apply]
    · intro c x y
      ext z
      simp [rankOne_apply]
  exact hR.contDiff.comp (hX.prodMk hY)

theorem contDiff_dirichletRadialTensor {n : ℕ} :
    ContDiff ℝ ∞ (dirichletRadialTensor (n := n)) :=
  contDiff_rankOne_real contDiff_id contDiff_id

theorem contDiff_dirichletTangentTensor {n : ℕ} :
    ContDiff ℝ ∞ (dirichletTangentTensor (n := n)) :=
  ((contDiff_norm_sq ℝ).smul contDiff_const).sub contDiff_dirichletRadialTensor

theorem dirichletRadialTensor_adjoint {n : ℕ} (x : E n) :
    (dirichletRadialTensor x).adjoint = dirichletRadialTensor x :=
  adjoint_rankOne x x

theorem dirichletTangentTensor_adjoint {n : ℕ} (x : E n) :
    (dirichletTangentTensor x).adjoint = dirichletTangentTensor x := by
  simp [dirichletTangentTensor, dirichletRadialTensor_adjoint]

/-- After removing the tangential coefficients, the remaining coefficient is
the radial tensor times the scalar ellipticity in the radial direction. -/
theorem dirichlet_tangent_radial_coefficient_decomposition {n : ℕ} (x : E n)
    (A : E n →L[ℝ] E n) :
    (‖x‖ ^ 4) • A =
      (‖x‖ ^ 2) • ((dirichletTangentTensor x).comp A) +
      (dirichletRadialTensor x).comp (A.comp (dirichletTangentTensor x)) +
      inner ℝ (A x) x • dirichletRadialTensor x := by
  ext v : 1
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    dirichletRadialTensor_apply, dirichletTangentTensor_apply, map_sub, map_smul]
  rw [real_inner_comm v x, real_inner_comm (A x) x, real_inner_comm (A v) x]
  module

/-- The divergence of a smooth vector field in a constant orthonormal frame. -/
noncomputable def dirichletVectorDivergence {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (X : E n → E n) (x : E n) : ℝ :=
  ∑ j, fderiv ℝ (fun y => inner ℝ (b j) (X y)) x (b j)

theorem contDiff_dirichletVectorDivergence {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {X : E n → E n}
    (hX : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (dirichletVectorDivergence b X) :=
  ContDiff.sum fun j _ =>
    (((innerSL ℝ (b j)).contDiff.comp hX).fderiv_right (by simp)).clm_apply contDiff_const

/-- A rank-one coefficient tests the weak derivative of one gradient component
in the direction of a smooth vector field. -/
theorem dirichletHessianTrace_rankOne_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {X : E n → E n} (hX : ContDiff ℝ ∞ X)
    (i : Fin (2 * n)) :
    dirichletHessianTrace b u ψ (contDiff_rankOne_real hX
      (contDiff_const (c := b i) : ContDiff ℝ ∞ (fun _ : E n => b i))) =
      -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) *
        inner ℝ (b i) ((u : DirichletBallL2Pair n).snd x) ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let R (x : E n) := rankOne ℝ (X x) (b i)
  let U := (u : DirichletBallL2Pair n).snd
  let a (x : E n) := inner ℝ (b i) (U x)
  have hDiag (j : Fin (2 * n)) :
      inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal i j
  have hColumn (j : Fin (2 * n)) (x : E n) :
      dirichletColumnDivergence b R (b j) x =
        if i = j then dirichletVectorDivergence b X x else 0 := by
    by_cases h : i = j
    · subst j
      unfold dirichletColumnDivergence dirichletVectorDivergence
      simp [R, rankOne_apply]
    · unfold dirichletColumnDivergence
      simp [R, rankOne_apply, hDiag, h]
  have hDiv (x : E n) :
      (∑ j, dirichletColumnDivergence b R (b j) x * inner ℝ (b j) (U x)) =
        dirichletVectorDivergence b X x * a x := by
    rw [Fintype.sum_eq_single i (fun j hj => by rw [hColumn, if_neg (Ne.symm hj), zero_mul])]
    simp [hColumn, a]
  have ha : Integrable a ν[n] := ((Lp.memLp U).const_inner (b i)).integrable (by norm_num)
  have hInt (φ : 𝓓(dirichletBallOpens n, ℝ)) : Integrable (fun x => φ x * a x) ν[n] :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (ha.locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hPrincI : Integrable (fun x => fderiv ℝ (ψ : E n → ℝ) x (X x) * a x) ν[n] :=
    hInt (dirichletTestFieldDerivative ψ X hX)
  have hDivI : Integrable (fun x => (ψ x * dirichletVectorDivergence b X x) * a x) ν[n] :=
    hInt (dirichletTestMul ψ (contDiff_dirichletVectorDivergence b hX))
  rw [dirichletHessianTrace_eq_neg_integral hn]
  change -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (R x (U x)) ∂ν[n]) -
      (∫ x, ψ x * (∑ j, dirichletColumnDivergence b R (b j) x * inner ℝ (b j) (U x)) ∂ν[n]) = _
  simp_rw [hDiv, ← mul_assoc]
  have hP (x : E n) : fderiv ℝ (ψ : E n → ℝ) x (R x (U x)) =
      fderiv ℝ (ψ : E n → ℝ) x (X x) * a x := by
    simp [R, rankOne_apply, a, mul_comm]
  simp_rw [hP]
  rw [sub_eq_add_neg, ← neg_add, ← integral_add hPrincI hDivI]
  simp only [add_mul, a, U]

/-- Divergence of the tangential projection applied to a fixed direction. -/
theorem dirichletVectorDivergence_tangentTensor {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (v x : E n) :
    dirichletVectorDivergence b (fun y => dirichletTangentTensor y v) x =
      (1 - (2 : ℝ) * n) * inner ℝ v x := by
  let c (j : Fin (2 * n)) := innerSL ℝ (b j)
  let d := innerSL ℝ v
  have hN : ContDiff ℝ ∞ (fun y : E n => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have h (j : Fin (2 * n)) :
      fderiv ℝ (fun y => inner ℝ (b j) (dirichletTangentTensor y v)) x (b j) =
        2 * (inner ℝ x (b j) * inner ℝ (b j) v) -
          inner ℝ v (b j) * inner ℝ (b j) x - inner ℝ v x := by
    have hEq : (fun y => inner ℝ (b j) (dirichletTangentTensor y v)) =
        fun y => ‖y‖ ^ 2 * c j v - d y * c j y := by
      funext y
      simp only [dirichletTangentTensor_apply, inner_sub_right, real_inner_smul_right]
      rfl
    have hNc : ContDiff ℝ ∞ (fun y : E n => ‖y‖ ^ 2 * c j v) := hN.mul contDiff_const
    have hProd : ContDiff ℝ ∞ (fun y => d y * c j y) := d.contDiff.mul (c j).contDiff
    rw [hEq, fderiv_fun_sub (hNc.differentiable (by simp) x) (hProd.differentiable (by simp) x),
      fderiv_fun_mul (hN.differentiable (by simp) x) (differentiableAt_const (c j v)),
      fderiv_fun_mul d.differentiableAt (c j).differentiableAt, fderiv_norm_sq_apply]
    have hB : c j (b j) = 1 := by simp [c]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, fderiv_fun_const, Pi.zero_apply, zero_apply, ContinuousLinearMap.fderiv, hB, mul_zero, zero_add, mul_one,
      c, d, innerSL_apply_apply]
    ring
  unfold dirichletVectorDivergence
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, b.sum_inner_mul_inner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [real_inner_comm v x]
  ring

end KEBall
