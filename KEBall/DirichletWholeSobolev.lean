import KEBall.DirichletSobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The whole-space function–gradient graph and zero extension from the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

noncomputable abbrev EuclideanL2 (n : ℕ) (F : Type*) [NormedAddCommGroup F] := Lp F 2 (volume0 n)

noncomputable abbrev EuclideanL2Pair (n : ℕ) :=
  WithLp 2 (EuclideanL2 n ℝ × EuclideanL2 n (E n))

/-- The whole-space graph is the closure of smooth compactly supported tests. -/
noncomputable def euclideanSobolevSubmodule (n : ℕ) : Submodule ℝ (EuclideanL2Pair n) :=
  (compactTestL2Graph (volume0 n) (Ω := ⊤)).range.topologicalClosure

abbrev EuclideanSobolev (n : ℕ) := ↥(euclideanSobolevSubmodule n)

noncomputable instance {n : ℕ} : CompleteSpace (EuclideanSobolev n) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

private theorem memLp_dirichletZeroExtension {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : DirichletBallL2 n F) : MemLp ((unitBall n).indicator (f : E n → F)) 2 (volume0 n) :=
  (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp f)

/-- Zero extension is an isometry from the restricted L² space to the ambient L² space. -/
noncomputable def dirichletL2ZeroExtension {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] : DirichletBallL2 n F →ₗᵢ[ℝ] EuclideanL2 n F where
  toFun f := (memLp_dirichletZeroExtension f).toLp ((unitBall n).indicator (f : E n → F))
  map_add' f g := by
    rw [← MemLp.toLp_add (memLp_dirichletZeroExtension f) (memLp_dirichletZeroExtension g)]
    apply MemLp.toLp_congr
    filter_upwards [(ae_restrict_iff' (μ := volume0 n) measurableSet_ball).mp (Lp.coeFn_add f g)]
      with x hx
    by_cases hb : x ∈ unitBall n
    · simpa only [indicator_of_mem hb, Pi.add_apply] using hx hb
    · simp [indicator_of_notMem hb]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_dirichletZeroExtension f)]
    apply MemLp.toLp_congr
    filter_upwards [(ae_restrict_iff' (μ := volume0 n) measurableSet_ball).mp (Lp.coeFn_smul c f)]
      with x hx
    by_cases hb : x ∈ unitBall n
    · simpa only [indicator_of_mem hb, Pi.smul_apply] using hx hb
    · simp [indicator_of_notMem hb]
  norm_map' f := by
    change ‖(memLp_dirichletZeroExtension f).toLp ((unitBall n).indicator (f : E n → F))‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict (s := unitBall n) measurableSet_ball, Lp.norm_def]

theorem dirichletL2ZeroExtension_ae {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : DirichletBallL2 n F) :
    dirichletL2ZeroExtension f =ᵐ[volume0 n] (unitBall n).indicator (f : E n → F) :=
  MemLp.coeFn_toLp (memLp_dirichletZeroExtension f)

private noncomputable def dirichletGraphZeroExtension (n : ℕ) :
    DirichletBallL2Pair n →L[ℝ] EuclideanL2Pair n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((dirichletL2ZeroExtension.toContinuousLinearMap.comp (WithLp.fstL 2 ℝ _ _)).prod
      (dirichletL2ZeroExtension.toContinuousLinearMap.comp (WithLp.sndL 2 ℝ _ _)))

private noncomputable def dirichletTestAmbient {n : ℕ} (φ : 𝓓(dirichletBallOpens n, ℝ)) :
    𝓓((⊤ : Opens (E n)), ℝ) :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩

private theorem dirichletGraphZeroExtension_test {n : ℕ} (φ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletGraphZeroExtension n (dirichletTestL2Graph n φ) =
      compactTestL2Graph (volume0 n) (dirichletTestAmbient φ) := by
  let ψ := dirichletTestAmbient φ
  apply (WithLp.equiv 2 (EuclideanL2 n ℝ × EuclideanL2 n (E n))).injective
  apply Prod.ext
  · change dirichletL2ZeroExtension (dirichletTestToL2 φ) = compactTestToL2 (volume0 n) ψ
    apply Lp.ext
    filter_upwards [dirichletL2ZeroExtension_ae (dirichletTestToL2 φ),
      (ae_restrict_iff' (μ := volume0 n) measurableSet_ball).mp (dirichletTestToL2_ae φ),
      compactTestToL2_ae (volume0 n) ψ] with x h₁ h₂ h₃
    rw [h₁, h₃]
    change (unitBall n).indicator (dirichletTestToL2 φ : E n → ℝ) x = φ x
    by_cases hb : x ∈ unitBall n
    · rw [indicator_of_mem hb]
      exact h₂ hb
    · rw [indicator_of_notMem hb]
      exact (image_eq_zero_of_notMem_tsupport (fun hx => hb (φ.tsupport_subset hx))).symm
  · change dirichletL2ZeroExtension (dirichletTestGradientToL2 n φ) =
      compactTestGradientToL2 (volume0 n) ψ
    apply Lp.ext
    filter_upwards [dirichletL2ZeroExtension_ae (dirichletTestGradientToL2 n φ),
      (ae_restrict_iff' (μ := volume0 n) measurableSet_ball).mp (dirichletTestGradientToL2_ae φ),
      compactTestGradientToL2_ae (volume0 n) ψ] with x h₁ h₂ h₃
    rw [h₁, h₃]
    change (unitBall n).indicator (dirichletTestGradientToL2 n φ : E n → E n) x =
      ∇ (φ : E n → ℝ) x
    by_cases hb : x ∈ unitBall n
    · rw [indicator_of_mem hb]
      exact h₂ hb
    · rw [indicator_of_notMem hb]
      apply ext_inner_right ℝ
      intro v
      rw [inner_zero_left, inner_gradient_left, fderiv_of_notMem_tsupport ℝ (fun hx => hb (φ.tsupport_subset hx)),
        zero_apply]

/-- The zero extension transports the actual Dirichlet function–gradient graph. -/
noncomputable def dirichletSobolevZeroExtension (n : ℕ) :
    DirichletSobolev n →L[ℝ] EuclideanSobolev n := by
  let T := dirichletGraphZeroExtension n
  let P := euclideanSobolevSubmodule n
  apply (T.comp (dirichletSobolevSubmodule n).subtypeL).codRestrict P
  intro u
  change T u.val ∈ P
  have hClosed : IsClosed (T ⁻¹' (P : Set (EuclideanL2Pair n))) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hRange : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ T ⁻¹' P := by
    rintro _ ⟨φ, rfl⟩
    change T (dirichletTestL2Graph n φ) ∈ P
    rw [show T (dirichletTestL2Graph n φ) = _ from dirichletGraphZeroExtension_test φ]
    exact subset_closure ⟨_, rfl⟩
  exact closure_minimal hRange hClosed u.property

theorem dirichletSobolevZeroExtension_value_ae {n : ℕ} (u : DirichletSobolev n) :
    (dirichletSobolevZeroExtension n u : EuclideanL2Pair n).fst =ᵐ[volume0 n]
      (unitBall n).indicator (fun x => (u : DirichletBallL2Pair n).fst x) :=
  dirichletL2ZeroExtension_ae (u : DirichletBallL2Pair n).fst

theorem dirichletSobolevZeroExtension_gradient_ae {n : ℕ} (u : DirichletSobolev n) :
    (dirichletSobolevZeroExtension n u : EuclideanL2Pair n).snd =ᵐ[volume0 n]
      (unitBall n).indicator (fun x => (u : DirichletBallL2Pair n).snd x) :=
  dirichletL2ZeroExtension_ae (u : DirichletBallL2Pair n).snd

end KEBall
