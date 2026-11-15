import KEBall.DirichletDeGiorgiCoefficients

/-!
# A normalized coefficient with a prescribed ellipticity ratio

The upper constant is exactly `(K / c)^2 + 1`; it does not come from a
new existential essential-supremum bound for each coefficient field.
The measurable representative and inverse coercivity proof are the same
as in the already verified coefficient bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "μ[" n "]" => Measure.restrict (volume : Measure (E n)) (unitBall n)

theorem exists_dirichletDeGiorgi_coefficient_of_bound {n : ℕ} [NeZero n]
    {B : E n → E n →L[ℝ] E n} (hB : MemLp B ⊤ ν[n])
    {c K : ℝ} (hc : 0 < c) (hK0 : 0 ≤ K)
    (hBound : ∀ᵐ x ∂ν[n], ‖B x‖ ≤ K)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) :
    ∃ A : DeGiorgi.NormalizedEllipticCoeff (2 * n) (unitBall n),
      A.1.Λ = (K / c) ^ 2 + 1 ∧
      ∀ᵐ x ∂μ[n], ∀ v : E n,
        DeGiorgi.matMulE (A.1.a x) v = c⁻¹ • B x v := by
  classical
  let Bm := hB.aestronglyMeasurable.mk B
  have hm : Measurable Bm := hB.aestronglyMeasurable.measurable_mk
  have he : B =ᵐ[μ[n]] Bm :=
    ae_volume0_restrict_iff.mp hB.aestronglyMeasurable.ae_eq_mk
  have hKV : ∀ᵐ x ∂μ[n], ‖B x‖ ≤ K := ae_volume0_restrict_iff.mp hBound
  let T : ℝ := K / c
  have hT : 0 ≤ T := div_nonneg hK0 hc.le
  let M (x : E n) := dirichletRealCoefficientMatrix (c⁻¹ • Bm x)
  have hAction (x v : E n) : DeGiorgi.matMulE (M x) v = c⁻¹ • Bm x v := by
    dsimp only [M]
    rw [dirichletRealCoefficientMatrix_action, ContinuousLinearMap.smul_apply]
  have hMeas (i j : Fin (2 * n)) : Measurable (fun x => M x i j) := by
    have hApply : Measurable (fun x => Bm x (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.measurable_apply (EuclideanSpace.single j 1)).comp hm
    have hCoord := hApply.const_inner (𝕜 := ℝ) (c := EuclideanSpace.single i (1 : ℝ))
    simpa only [M, dirichletRealCoefficientMatrix, ContinuousLinearMap.smul_apply,
      PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_single_left, map_one, one_mul]
      using hCoord.const_mul c⁻¹
  have hCoer : ∀ᵐ x ∂μ[n], ∀ v : E n,
      ‖v‖ ^ 2 ≤ inner ℝ v (DeGiorgi.matMulE (M x) v) := by
    filter_upwards [he, ae_volume0_restrict_iff.mp hEll] with x hx hEx
    intro v
    rw [hAction, ← hx, real_inner_smul_right]
    have h := mul_le_mul_of_nonneg_left (hEx v) (inv_nonneg.mpr hc.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, real_inner_comm] using h
  have hNorm : ∀ᵐ x ∂μ[n], ∀ v : E n,
      ‖DeGiorgi.matMulE (M x) v‖ ≤ T * ‖v‖ := by
    filter_upwards [he, hKV] with x hx hKx
    intro v
    calc
      _ = c⁻¹ * ‖B x v‖ := by
        rw [hAction, ← hx, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      _ ≤ c⁻¹ * (K * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((B x).le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right hKx (norm_nonneg v))) (inv_nonneg.mpr hc.le)
      _ = T * ‖v‖ := by dsimp only [T]; ring
  let A : DeGiorgi.EllipticCoeff (2 * n) (unitBall n) := {
    a := M
    lam := 1
    Λ := T ^ 2 + 1
    measurable_comp := hMeas
    hlam := by norm_num
    hΛ := by nlinarith only [sq_nonneg T]
    coercive := by simpa only [one_mul] using hCoer
    coercive_inv := by
      filter_upwards [hCoer, hNorm] with x hCx hNx
      exact dirichletMatrix_inverse_coercive (M x) hT hCx hNx }
  refine ⟨⟨A, rfl⟩, rfl, ?_⟩
  filter_upwards [he] with x hx
  intro v
  change DeGiorgi.matMulE (M x) v = c⁻¹ • B x v
  rw [hAction, ← hx]


end KEBall
