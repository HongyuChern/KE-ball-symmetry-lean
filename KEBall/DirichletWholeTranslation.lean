import KEBall.DirichletWholeSobolev
import KEBall.DirichletTranslationEstimate

/-! Translation of the whole-space Sobolev graph and its L² difference quotients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

theorem euclideanTranslate_measurePreserving {n : ℕ} (a : E n) :
    MeasurePreserving (fun x => x + a) (volume0 n) (volume0 n) :=
  (measurePreserving_add_right (volume : Measure (E n)) a).smul_measure _

/-- Translation of the argument acts isometrically on ambient L². -/
noncomputable def euclideanL2Translate {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : E n) : EuclideanL2 n F →ₗᵢ[ℝ] EuclideanL2 n F :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + a) (euclideanTranslate_measurePreserving a)

theorem euclideanL2Translate_ae {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : E n) (f : EuclideanL2 n F) : euclideanL2Translate a f =ᵐ[volume0 n] fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (euclideanTranslate_measurePreserving a)

private noncomputable def euclideanTestTranslate {n : ℕ} (a : E n)
    (φ : 𝓓((⊤ : Opens (E n)), ℝ)) : 𝓓((⊤ : Opens (E n)), ℝ) :=
  ⟨fun x => φ (x + a), φ.contDiff.comp (contDiff_id.add contDiff_const),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight a), subset_univ _⟩

private theorem euclideanTestTranslate_gradient {n : ℕ} (a : E n)
    (φ : 𝓓((⊤ : Opens (E n)), ℝ)) (x : E n) :
    ∇ (euclideanTestTranslate a φ : E n → ℝ) x = ∇ (φ : E n → ℝ) (x + a) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_gradient_left]
  have hD : HasFDerivAt (fun y : E n => y + a) (ContinuousLinearMap.id ℝ (E n)) x :=
    (hasFDerivAt_id x).add_const a
  have h := ((φ.contDiff.differentiable (by simp) (x + a)).hasFDerivAt).comp x hD
  change fderiv ℝ ((φ : E n → ℝ) ∘ fun y => y + a) x v = _
  rw [h.fderiv]
  rfl

private noncomputable def euclideanGraphTranslate {n : ℕ} (a : E n) :
    EuclideanL2Pair n →L[ℝ] EuclideanL2Pair n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((euclideanL2Translate a |>.toContinuousLinearMap.comp (WithLp.fstL 2 ℝ _ _)).prod
      (euclideanL2Translate a |>.toContinuousLinearMap.comp (WithLp.sndL 2 ℝ _ _)))

private theorem euclideanGraphTranslate_test {n : ℕ} (a : E n)
    (φ : 𝓓((⊤ : Opens (E n)), ℝ)) :
    euclideanGraphTranslate a (compactTestL2Graph (volume0 n) φ) =
      compactTestL2Graph (volume0 n) (euclideanTestTranslate a φ) := by
  let ψ := euclideanTestTranslate a φ
  let μ := volume0 n
  let hμ := euclideanTranslate_measurePreserving a
  apply (WithLp.equiv 2 (EuclideanL2 n ℝ × EuclideanL2 n (E n))).injective
  apply Prod.ext
  · change euclideanL2Translate a (compactTestToL2 μ φ) = compactTestToL2 μ ψ
    apply Lp.ext
    filter_upwards [euclideanL2Translate_ae a (compactTestToL2 μ φ),
      hμ.quasiMeasurePreserving.tendsto_ae.eventually (compactTestToL2_ae μ φ),
      compactTestToL2_ae μ ψ] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    rfl
  · change euclideanL2Translate a (compactTestGradientToL2 μ φ) = compactTestGradientToL2 μ ψ
    apply Lp.ext
    filter_upwards [euclideanL2Translate_ae a (compactTestGradientToL2 μ φ),
      hμ.quasiMeasurePreserving.tendsto_ae.eventually (compactTestGradientToL2_ae μ φ),
      compactTestGradientToL2_ae μ ψ] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    exact (euclideanTestTranslate_gradient a φ x).symm

/-- Translation transports a function and its weak gradient together. -/
noncomputable def euclideanSobolevTranslate {n : ℕ} (a : E n) :
    EuclideanSobolev n →L[ℝ] EuclideanSobolev n := by
  let T := euclideanGraphTranslate a
  let P := euclideanSobolevSubmodule n
  apply (T.comp P.subtypeL).codRestrict P
  intro u
  change T u.val ∈ P
  have hClosed : IsClosed (T ⁻¹' (P : Set (EuclideanL2Pair n))) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hRange : ((compactTestL2Graph (volume0 n) (Ω := ⊤)).range : Set (EuclideanL2Pair n)) ⊆
      T ⁻¹' P := by
    rintro _ ⟨φ, rfl⟩
    change T (compactTestL2Graph (volume0 n) φ) ∈ P
    rw [show T (compactTestL2Graph (volume0 n) φ) = _ from euclideanGraphTranslate_test a φ]
    exact subset_closure ⟨_, rfl⟩
  exact closure_minimal hRange hClosed u.property

theorem euclideanSobolevTranslate_value_ae {n : ℕ} (a : E n) (u : EuclideanSobolev n) :
    (euclideanSobolevTranslate a u : EuclideanL2Pair n).fst =ᵐ[volume0 n]
      fun x => (u : EuclideanL2Pair n).fst (x + a) :=
  euclideanL2Translate_ae a (u : EuclideanL2Pair n).fst

theorem euclideanSobolevTranslate_gradient_ae {n : ℕ} (a : E n) (u : EuclideanSobolev n) :
    (euclideanSobolevTranslate a u : EuclideanL2Pair n).snd =ᵐ[volume0 n]
      fun x => (u : EuclideanL2Pair n).snd (x + a) :=
  euclideanL2Translate_ae a (u : EuclideanL2Pair n).snd

/-- The translation difference quotient in a fixed direction on the Sobolev graph. -/
noncomputable def euclideanSobolevDifferenceQuotient {n : ℕ} (v : E n) (h : ℝ) :
    EuclideanSobolev n →L[ℝ] EuclideanSobolev n :=
  h⁻¹ • (euclideanSobolevTranslate (h • v) - ContinuousLinearMap.id ℝ (EuclideanSobolev n))

private theorem euclideanL2_norm_sq {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : EuclideanL2 n F) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂volume0 n := by
  rw [← real_inner_self_eq_norm_sq f, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem euclideanGraphTranslate_norm_differenceQuotient_test {n : ℕ}
    (φ : 𝓓((⊤ : Opens (E n)), ℝ)) (v : E n) {h : ℝ} (hh : h ≠ 0) :
    let z := compactTestL2Graph (volume0 n) φ
    ‖(h⁻¹ • (euclideanGraphTranslate (h • v) z - z) : EuclideanL2Pair n).fst‖ ≤ ‖v‖ * ‖z.snd‖ := by
  let μ := volume0 n
  let z := compactTestL2Graph μ φ
  let f := compactTestToL2 μ φ
  let G := compactTestGradientToL2 μ φ
  let fT := euclideanL2Translate (h • v) f
  change ‖h⁻¹ • (fT - f)‖ ≤ ‖v‖ * ‖G‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, euclideanL2_norm_sq, euclideanL2_norm_sq G, ← integral_const_mul]
  have hEq :
      (∫ x, ‖(h⁻¹ • (fT - f)) x‖ ^ 2 ∂μ) = ∫ x, (h⁻¹ * (φ (x + h • v) - φ x)) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul h⁻¹ (fT - f), Lp.coeFn_sub fT f,
      euclideanL2Translate_ae (h • v) f,
      (euclideanTranslate_measurePreserving (h • v)).quasiMeasurePreserving.tendsto_ae.eventually
        (compactTestToL2_ae μ φ), compactTestToL2_ae μ φ] with x hs hsub ht htp hp
    change fT x = f (x + h • v) at ht
    change f (x + h • v) = φ (x + h • v) at htp
    change f x = φ x at hp
    simp only [hs, hsub, ht, htp, hp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  rw [hEq]
  have hBound : (∫ x, (h⁻¹ * (φ (x + h • v) - φ x)) ^ 2 ∂μ) ≤
      ∫ x, (fderiv ℝ (φ : E n → ℝ) x v) ^ 2 ∂μ := by
    dsimp only [μ, volume0]
    rw [integral_smul_measure, integral_smul_measure]
    exact mul_le_mul_of_nonneg_left
      (integral_sq_translationDifferenceQuotient_le φ.contDiff φ.hasCompactSupport v hh)
      ENNReal.toReal_nonneg
  apply hBound.trans
  have hP : MemLp (fun x => inner ℝ (G x) v) 2 μ := (Lp.memLp G).inner_const v
  have hEqGrad : (fun x => (fderiv ℝ (φ : E n → ℝ) x v) ^ 2) =ᵐ[μ]
      (fun x => (inner ℝ (G x) v) ^ 2) := by
    filter_upwards [compactTestGradientToL2_ae μ φ] with x hx
    change G x = ∇ (φ : E n → ℝ) x at hx
    rw [hx, inner_gradient_left]
  have hI : Integrable (fun x => (fderiv ℝ (φ : E n → ℝ) x v) ^ 2) μ :=
    ((memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mp hP).congr hEqGrad.symm
  have hG : Integrable (fun x => ‖G x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) G G
  refine integral_mono_ae hI (hG.const_mul _) ?_
  filter_upwards [hEqGrad] with x hx
  rw [hx, ← sq_abs (inner ℝ (G x) v), ← Real.norm_eq_abs, ← mul_pow, mul_comm ‖v‖ ‖G x‖]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- The L² norm of a function's difference quotient is controlled by its gradient. -/
theorem norm_euclideanSobolevDifferenceQuotient_value_le {n : ℕ} (u : EuclideanSobolev n)
    (v : E n) {h : ℝ} (hh : h ≠ 0) :
    ‖(euclideanSobolevDifferenceQuotient v h u : EuclideanL2Pair n).fst‖ ≤
      ‖v‖ * ‖(u : EuclideanL2Pair n).snd‖ := by
  let T := euclideanGraphTranslate (h • v)
  let S : Set (EuclideanL2Pair n) := {z | ‖(h⁻¹ • (T z - z) : EuclideanL2Pair n).fst‖ ≤ ‖v‖ * ‖z.snd‖}
  have hClosed : IsClosed S := isClosed_le (by fun_prop) (by fun_prop)
  have hRange : ((compactTestL2Graph (volume0 n) (Ω := ⊤)).range : Set (EuclideanL2Pair n)) ⊆ S := by
    rintro _ ⟨φ, rfl⟩
    exact euclideanGraphTranslate_norm_differenceQuotient_test φ v hh
  exact closure_minimal hRange hClosed u.property

end KEBall
