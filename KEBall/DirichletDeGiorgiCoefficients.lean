import KEBall.SphereMeasure
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

/-!
# Normalizing the actual bounded cofactor field for weak Harnack

The external coefficient class asks for coercivity of the inverse matrix.
Here that property is derived from the existing lower ellipticity and the
essential operator-norm bound.  The globally measurable representative is
chosen only after recording almost-everywhere agreement with the original
field.  No pointwise regularity of the coefficient is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ENNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "μ[" n "]" => Measure.restrict (volume : Measure (E n)) (unitBall n)

/-- The normalized and ordinary volume have the same null sets, including
after restriction to any measurable or nonmeasurable set. -/
theorem ae_volume0_restrict_iff {n : ℕ} {s : Set (E n)} {P : E n → Prop} :
    (∀ᵐ x ∂(volume0 n).restrict s, P x) ↔
      ∀ᵐ x ∂(volume : Measure (E n)).restrict s, P x := by
  have hc : ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  rw [volume0, Measure.restrict_smul]
  exact Measure.ae_ennreal_smul_measure_iff hc

/-- Multiplication of volume by the fixed positive finite normalization
does not change membership in any `L^p` space. -/
theorem memLp_volume0_restrict_iff {n : ℕ} {s : Set (E n)}
    {V : Type*} [NormedAddCommGroup V] {f : E n → V} {p : ℝ≥0∞} :
    MemLp f p ((volume0 n).restrict s) ↔
      MemLp f p ((volume : Measure (E n)).restrict s) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n)
  have hc : c ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [volume0, Measure.restrict_smul]
  change MemLp f p (c • (volume : Measure (E n)).restrict s) ↔ _
  constructor
  · intro hf
    have h := hf.smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.mpr hc)
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul] using h
  · intro hf
    exact hf.smul_measure hct

/-- Coordinates of a real operator in the fixed Euclidean orthonormal basis. -/
def dirichletRealCoefficientMatrix {n : ℕ} (B : E n →L[ℝ] E n) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j => B (EuclideanSpace.single j 1) i

theorem dirichletRealCoefficientMatrix_action {n : ℕ}
    (B : E n →L[ℝ] E n) (v : E n) :
    DeGiorgi.matMulE (dirichletRealCoefficientMatrix B) v = B v := by
  have hExpand : (∑ j : Fin (2 * n), v j • EuclideanSpace.single j 1) = v := by
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr v
  apply PiLp.ext
  intro i
  change (∑ j : Fin (2 * n), B (EuclideanSpace.single j 1) i * v j) = B v i
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, mul_comm] using congrArg (fun z : E n => B z i) hExpand

/-- A coercive finite matrix is invertible.  This lemma precedes the
construction of `EllipticCoeff`, so it does not assume inverse coercivity. -/
theorem dirichletMatrix_det_ne_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hCoer : ∀ v : DeGiorgi.AmbientSpace d,
      ‖v‖ ^ 2 ≤ inner ℝ v (DeGiorgi.matMulE M v)) : M.det ≠ 0 := by
  classical
  rw [ne_eq, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, hMv⟩
  let ξ : DeGiorgi.AmbientSpace d := WithLp.toLp 2 v
  have hMξ : DeGiorgi.matMulE M ξ = 0 := by
    apply PiLp.ext
    intro i
    simp [DeGiorgi.matMulE, ξ, hMv]
  have hNorm : ‖ξ‖ = 0 := by
    have h := hCoer ξ
    rw [hMξ, inner_zero_right] at h
    nlinarith only [h, sq_nonneg ‖ξ‖]
  have hξ := norm_eq_zero.mp hNorm
  apply hv
  have he := congrArg (fun η : DeGiorgi.AmbientSpace d => η.ofLp) hξ
  simpa [ξ] using he

/-- An operator-norm bound and lower coercivity imply the inverse bound
needed by the pinned De Giorgi interface, with upper scale `T² + 1`. -/
theorem dirichletMatrix_inverse_coercive {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hCoer : ∀ v : DeGiorgi.AmbientSpace d,
      ‖v‖ ^ 2 ≤ inner ℝ v (DeGiorgi.matMulE M v))
    (hNorm : ∀ v : DeGiorgi.AmbientSpace d,
      ‖DeGiorgi.matMulE M v‖ ≤ T * ‖v‖)
    (ξ : DeGiorgi.AmbientSpace d) :
    (T ^ 2 + 1)⁻¹ * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (DeGiorgi.matMulE M⁻¹ ξ) := by
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (dirichletMatrix_det_ne_zero M hCoer)
  let η := DeGiorgi.matMulE M⁻¹ ξ
  have hMη : DeGiorgi.matMulE M η = ξ := by
    apply PiLp.ext
    intro i
    simp [η, DeGiorgi.matMulE, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet]
  have hc : ‖η‖ ^ 2 ≤ inner ℝ ξ η := by
    simpa only [hMη, real_inner_comm] using hCoer η
  have hn : ‖ξ‖ ^ 2 ≤ T ^ 2 * ‖η‖ ^ 2 := by
    have h := hNorm η
    rw [hMη] at h
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg ξ) h 2
  have hq : 0 ≤ inner ℝ ξ η := (sq_nonneg ‖η‖).trans hc
  have hTotal : ‖ξ‖ ^ 2 ≤ (T ^ 2 + 1) * inner ℝ ξ η := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg T)
    nlinarith only [hn, h, hq]
  have hΛ : 0 < T ^ 2 + 1 := by positivity
  have hDiv := (div_le_iff₀ hΛ).mpr (show ‖ξ‖ ^ 2 ≤ inner ℝ ξ η * (T ^ 2 + 1) by
    simpa only [mul_comm] using hTotal)
  simpa only [div_eq_mul_inv, mul_comm, η] using hDiv

/-- The actual essentially bounded coefficient field has a measurable
normalized De Giorgi representative with exactly the same action almost
everywhere, multiplied by the positive scalar `c⁻¹`. -/
theorem exists_dirichletDeGiorgi_coefficient {n : ℕ} [NeZero n]
    {B : E n → E n →L[ℝ] E n} (hB : MemLp B ⊤ ν[n])
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) :
    ∃ A : DeGiorgi.NormalizedEllipticCoeff (2 * n) (unitBall n),
      ∀ᵐ x ∂μ[n], ∀ v : E n,
        DeGiorgi.matMulE (A.1.a x) v = c⁻¹ • B x v := by
  classical
  let Bm := hB.aestronglyMeasurable.mk B
  have hm : Measurable Bm := hB.aestronglyMeasurable.measurable_mk
  have he : B =ᵐ[μ[n]] Bm :=
    ae_volume0_restrict_iff.mp hB.aestronglyMeasurable.ae_eq_mk
  have hTop : eLpNormEssSup B ν[n] < ⊤ := by
    simpa only [eLpNorm_exponent_top] using hB.2
  obtain ⟨K, hK⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hTop
  have hKV : ∀ᵐ x ∂μ[n], ‖B x‖ ≤ (K : ℝ) := by
    apply ae_volume0_restrict_iff.mp
    filter_upwards [hK] with x hx
    exact_mod_cast hx
  let T : ℝ := (K : ℝ) / c
  have hT : 0 ≤ T := div_nonneg K.coe_nonneg hc.le
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
      _ ≤ c⁻¹ * ((K : ℝ) * ‖v‖) :=
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
  refine ⟨⟨A, rfl⟩, ?_⟩
  filter_upwards [he] with x hx
  intro v
  change DeGiorgi.matMulE (M x) v = c⁻¹ • B x v
  rw [hAction, ← hx]

end KEBall
