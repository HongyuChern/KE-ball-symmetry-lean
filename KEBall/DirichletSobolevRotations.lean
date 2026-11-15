import KEBall.DirichletSobolev
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthogonal pullback of zero-boundary Sobolev functions

Orthogonal maps preserve the real unit ball and its normalized measure.
Pullback acts on the closed function–gradient graph by the chain rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

theorem orthogonal_preimage_unitBall {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    R ⁻¹' unitBall n = unitBall n := by
  ext x
  change R x ∈ ball (0 : E n) 1 ↔ x ∈ ball (0 : E n) 1
  rw [mem_ball_zero_iff, mem_ball_zero_iff, R.norm_map]

theorem orthogonal_measurePreserving_dirichletBall {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving R ((volume0 n).restrict (unitBall n))
      ((volume0 n).restrict (unitBall n)) := by
  have h : MeasurePreserving R (volume0 n) (volume0 n) :=
    R.measurePreserving.smul_measure _
  simpa only [orthogonal_preimage_unitBall R] using
    h.restrict_preimage (s := unitBall n) measurableSet_ball

private noncomputable def dirichletTestPullback {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (φ : 𝓓(dirichletBallOpens n, ℝ)) : 𝓓(dirichletBallOpens n, ℝ) := by
  refine ⟨(φ : E n → ℝ) ∘ R, φ.contDiff.comp R.toContinuousLinearEquiv.contDiff,
    φ.hasCompactSupport.comp_homeomorph R.toHomeomorph, ?_⟩
  change tsupport ((φ : E n → ℝ) ∘ R) ⊆ unitBall n
  have hPre : Function.support ((φ : E n → ℝ) ∘ R) ⊆ R ⁻¹' tsupport (φ : E n → ℝ) :=
    fun _ hx => subset_tsupport (φ : E n → ℝ) hx
  refine (closure_minimal hPre ((isClosed_tsupport _).preimage R.continuous)).trans ?_
  rw [← orthogonal_preimage_unitBall R]
  exact preimage_mono φ.tsupport_subset

private theorem dirichletTestPullback_gradient {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (φ : 𝓓(dirichletBallOpens n, ℝ)) (x : E n) :
    ∇ (dirichletTestPullback R φ : E n → ℝ) x = R.symm (∇ (φ : E n → ℝ) (R x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hD := ((φ.contDiff.differentiable (by simp) (R x)).hasFDerivAt).comp x
    R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ ((φ : E n → ℝ) ∘ R) x v = _
  have hDF : HasFDerivAt ((φ : E n → ℝ) ∘ R) _ x := hD
  rw [hDF.fderiv]
  change fderiv ℝ (φ : E n → ℝ) (R x) (R v) = _
  rw [← inner_gradient_left]
  calc
    _ = inner ℝ (R (R.symm (∇ (φ : E n → ℝ) (R x)))) (R v) := by rw [R.apply_symm_apply]
    _ = _ := R.inner_map_map _ _

/-- Composition with an orthogonal map on the ball preserves the L² norm. -/
noncomputable def dirichletL2Pullback {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (R : E n ≃ₗᵢ[ℝ] E n) :
    DirichletBallL2 n F →ₗᵢ[ℝ] DirichletBallL2 n F :=
  Lp.compMeasurePreservingₗᵢ ℝ R (orthogonal_measurePreserving_dirichletBall R)

theorem dirichletL2Pullback_ae {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (R : E n ≃ₗᵢ[ℝ] E n) (f : DirichletBallL2 n F) :
    dirichletL2Pullback R f =ᵐ[(volume0 n).restrict (unitBall n)] fun x => f (R x) :=
  Lp.coeFn_compMeasurePreserving f (orthogonal_measurePreserving_dirichletBall R)

private noncomputable def dirichletGradientPullback {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    DirichletBallL2 n (E n) →L[ℝ] DirichletBallL2 n (E n) :=
  (ContinuousLinearMap.compLpL 2 ((volume0 n).restrict (unitBall n))
    R.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (dirichletL2Pullback R).toContinuousLinearMap

private theorem dirichletGradientPullback_ae {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (g : DirichletBallL2 n (E n)) :
    dirichletGradientPullback R g =ᵐ[(volume0 n).restrict (unitBall n)]
      fun x => R.symm (g (R x)) := by
  refine EventuallyEq.trans (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (dirichletL2Pullback R g)) ?_
  filter_upwards [dirichletL2Pullback_ae R g] with x hx
  change R.symm (dirichletL2Pullback R g x) = _
  rw [hx]

private noncomputable def dirichletGraphPullback {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    DirichletBallL2Pair n →L[ℝ] DirichletBallL2Pair n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((dirichletL2Pullback R).toContinuousLinearMap.comp (WithLp.fstL 2 ℝ _ _)).prod
      ((dirichletGradientPullback R).comp (WithLp.sndL 2 ℝ _ _)))

private theorem dirichletGraphPullback_test {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (φ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletGraphPullback R (dirichletTestL2Graph n φ) =
      dirichletTestL2Graph n (dirichletTestPullback R φ) := by
  let ψ := dirichletTestPullback R φ
  let hμ := orthogonal_measurePreserving_dirichletBall R
  apply (WithLp.equiv 2 (DirichletBallL2 n ℝ × DirichletBallL2 n (E n))).injective
  apply Prod.ext
  · change dirichletL2Pullback R (dirichletTestToL2 φ) = dirichletTestToL2 ψ
    apply Lp.ext
    filter_upwards [dirichletL2Pullback_ae R (dirichletTestToL2 φ),
      hμ.quasiMeasurePreserving.tendsto_ae.eventually (dirichletTestToL2_ae φ),
      dirichletTestToL2_ae ψ] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    rfl
  · change dirichletGradientPullback R (dirichletTestGradientToL2 n φ) =
      dirichletTestGradientToL2 n ψ
    apply Lp.ext
    filter_upwards [dirichletGradientPullback_ae R (dirichletTestGradientToL2 n φ),
      hμ.quasiMeasurePreserving.tendsto_ae.eventually (dirichletTestGradientToL2_ae φ),
      dirichletTestGradientToL2_ae ψ] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    exact (dirichletTestPullback_gradient R φ x).symm

/-- The pullback of zero-trace Sobolev functions by an orthogonal map. -/
noncomputable def dirichletSobolevPullback {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    DirichletSobolev n →L[ℝ] DirichletSobolev n := by
  let T := dirichletGraphPullback R
  let P := dirichletSobolevSubmodule n
  apply (T.comp P.subtypeL).codRestrict P
  intro w
  change T w.val ∈ P
  have hClosed : IsClosed (T ⁻¹' (P : Set (DirichletBallL2Pair n))) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hRange : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ T ⁻¹' P := by
    rintro _ ⟨φ, rfl⟩
    change T (dirichletTestL2Graph n φ) ∈ P
    rw [show T (dirichletTestL2Graph n φ) = _ from dirichletGraphPullback_test R φ]
    exact subset_closure ⟨_, rfl⟩
  exact closure_minimal hRange hClosed w.property

theorem dirichletSobolevPullback_value_ae {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (w : DirichletSobolev n) :
    (dirichletSobolevPullback R w : DirichletBallL2Pair n).fst =ᵐ[(volume0 n).restrict (unitBall n)]
      fun x => (w : DirichletBallL2Pair n).fst (R x) :=
  dirichletL2Pullback_ae R (w : DirichletBallL2Pair n).fst

theorem dirichletSobolevPullback_gradient_ae {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (w : DirichletSobolev n) :
    (dirichletSobolevPullback R w : DirichletBallL2Pair n).snd =ᵐ[(volume0 n).restrict (unitBall n)]
      fun x => R.symm ((w : DirichletBallL2Pair n).snd (R x)) :=
  dirichletGradientPullback_ae R (w : DirichletBallL2Pair n).snd

end KEBall
