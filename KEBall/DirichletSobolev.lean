import KEBall.DirichletPoincare
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Weak Dirichlet solutions on the real model ball

The Hilbert space is the closed graph of a test function and its gradient
in the product of the two L² spaces. Poincaré's inequality and Lax–Milgram
give the weak solution for a bounded uniformly elliptic coefficient field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

abbrev dirichletBallOpens (n : ℕ) : Opens (E n) :=
  ⟨unitBall n, isOpen_ball⟩

noncomputable abbrev DirichletBallL2 (n : ℕ) (F : Type*) [NormedAddCommGroup F] :=
  Lp F 2 ((volume0 n).restrict (unitBall n))

private theorem compactTest_memLp {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure (E n)} [IsFiniteMeasureOnCompacts μ] {Ω : Opens (E n)}
    (φ : 𝓓(Ω, F)) : MemLp (φ : E n → F) 2 μ :=
  φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-- Inclusion of compactly supported test functions in the L² space of the measure. -/
noncomputable def compactTestToL2 {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure (E n)) [IsFiniteMeasureOnCompacts μ] {Ω : Opens (E n)} :
    𝓓(Ω, F) →ₗ[ℝ] Lp F 2 μ where
  toFun φ := (compactTest_memLp φ).toLp φ
  map_add' φ ψ := MemLp.toLp_add (compactTest_memLp φ) (compactTest_memLp ψ)
  map_smul' c φ := MemLp.toLp_const_smul c (compactTest_memLp φ)

theorem compactTestToL2_ae {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure (E n)) [IsFiniteMeasureOnCompacts μ] {Ω : Opens (E n)} (φ : 𝓓(Ω, F)) :
    compactTestToL2 μ φ =ᵐ[μ] (φ : E n → F) :=
  MemLp.coeFn_toLp (compactTest_memLp φ)

/-- The gradient of a compactly supported test function as an L² field. -/
noncomputable def compactTestGradientToL2 {n : ℕ}
    (μ : Measure (E n)) [IsFiniteMeasureOnCompacts μ] {Ω : Opens (E n)} :
    𝓓(Ω, ℝ) →ₗ[ℝ] Lp (E n) 2 μ :=
  (ContinuousLinearMap.compLpL 2 μ
    (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap).toLinearMap.comp
      ((compactTestToL2 μ).comp (TestFunction.fderivCLM ℝ ⊤ ⊤).toLinearMap)

theorem compactTestGradientToL2_ae {n : ℕ}
    (μ : Measure (E n)) [IsFiniteMeasureOnCompacts μ] {Ω : Opens (E n)} (φ : 𝓓(Ω, ℝ)) :
    compactTestGradientToL2 μ φ =ᵐ[μ] (∇ (φ : E n → ℝ)) := by
  let F := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let ψ := TestFunction.fderivCLM ℝ ⊤ ⊤ φ
  have hψ := compactTestToL2_ae μ ψ
  change (F.compLp (compactTestToL2 μ ψ)) =ᵐ[μ] _
  refine EventuallyEq.trans (F.coeFn_compLp (compactTestToL2 μ ψ)) ?_
  filter_upwards [hψ] with x hx
  change F (compactTestToL2 μ ψ x) = ∇ (φ : E n → ℝ) x
  rw [hx]
  have hφ := TestFunction.fderivCLM_apply_of_le (𝕜 := ℝ) (k := (⊤ : ℕ∞)) φ (by simp)
  change F (ψ x) = _
  rw [show ψ x = fderiv ℝ (φ : E n → ℝ) x from congrFun hφ x]
  rfl

/-- The function and gradient of a smooth compactly supported test as an L² pair. -/
noncomputable def compactTestL2Graph {n : ℕ}
    (μ : Measure (E n)) [IsFiniteMeasureOnCompacts μ] {Ω : Opens (E n)} :
    𝓓(Ω, ℝ) →ₗ[ℝ] WithLp 2 (Lp ℝ 2 μ × Lp (E n) 2 μ) :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    ((compactTestToL2 μ).prod (compactTestGradientToL2 μ))

instance volume0_isFiniteMeasureOnCompacts (n : ℕ) : IsFiniteMeasureOnCompacts (volume0 n) :=
  IsFiniteMeasureOnCompacts.smul (volume : Measure (E n)) ENNReal.ofReal_ne_top

/-- The ordinary inclusion of a compactly supported Dirichlet test in L². -/
noncomputable def dirichletTestToL2 {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    𝓓(dirichletBallOpens n, F) →ₗ[ℝ] DirichletBallL2 n F :=
  compactTestToL2 ((volume0 n).restrict (unitBall n))

theorem dirichletTestToL2_ae {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : 𝓓(dirichletBallOpens n, F)) :
    dirichletTestToL2 φ =ᵐ[(volume0 n).restrict (unitBall n)] (φ : E n → F) :=
  compactTestToL2_ae _ φ

/-- The L² gradient of a smooth Dirichlet test function in the real model. -/
noncomputable def dirichletTestGradientToL2 (n : ℕ) :
    𝓓(dirichletBallOpens n, ℝ) →ₗ[ℝ] DirichletBallL2 n (E n) :=
  compactTestGradientToL2 ((volume0 n).restrict (unitBall n))

theorem dirichletTestGradientToL2_ae {n : ℕ} (φ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletTestGradientToL2 n φ =ᵐ[(volume0 n).restrict (unitBall n)] (∇ (φ : E n → ℝ)) :=
  compactTestGradientToL2_ae _ φ

noncomputable abbrev DirichletBallL2Pair (n : ℕ) :=
  WithLp 2 (DirichletBallL2 n ℝ × DirichletBallL2 n (E n))

/-- The function and its gradient as a single vector in a product Hilbert space. -/
noncomputable def dirichletTestL2Graph (n : ℕ) :
    𝓓(dirichletBallOpens n, ℝ) →ₗ[ℝ] DirichletBallL2Pair n :=
  compactTestL2Graph ((volume0 n).restrict (unitBall n))

/-- The closed graph space of zero-trace Dirichlet functions and gradients. -/
noncomputable def dirichletSobolevSubmodule (n : ℕ) : Submodule ℝ (DirichletBallL2Pair n) :=
  (dirichletTestL2Graph n).range.topologicalClosure

abbrev DirichletSobolev (n : ℕ) := ↥(dirichletSobolevSubmodule n)

noncomputable instance {n : ℕ} : CompleteSpace (DirichletSobolev n) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

private theorem norm_L2_sq_eq_integral {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (w : DirichletBallL2 n F) :
    ‖w‖ ^ 2 = ∫ x in unitBall n, ‖w x‖ ^ 2 ∂volume0 n := by
  rw [← real_inner_self_eq_norm_sq w, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem dirichletTestL2_poincare {n : ℕ} (hn : 0 < n) (φ : 𝓓(dirichletBallOpens n, ℝ)) :
    (n : ℝ) ^ 2 * ‖dirichletTestToL2 φ‖ ^ 2 ≤ ‖dirichletTestGradientToL2 n φ‖ ^ 2 := by
  have hφ : SmoothNear (closedUnitBall n) (φ : E n → ℝ) :=
    ⟨Set.univ, isOpen_univ, subset_univ _, φ.contDiff.contDiffOn⟩
  have hφ0 (x : E n) (hx : x ∈ unitSphere n) : φ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hm : x ∈ unitBall n := φ.tsupport_subset h
    exact (lt_irrefl _ ((mem_sphere_zero_iff_norm.mp hx) ▸ mem_ball_zero_iff.mp hm)).elim
  have h := dirichlet_poincare_sq hn hφ hφ0
  have hValue : (∫ x in unitBall n, ‖dirichletTestToL2 φ x‖ ^ 2 ∂volume0 n) =
      ∫ x in unitBall n, ‖φ x‖ ^ 2 ∂volume0 n := by
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae φ] with x hx
    rw [hx]
  have hGrad : (∫ x in unitBall n, ‖dirichletTestGradientToL2 n φ x‖ ^ 2 ∂volume0 n) =
      ∫ x in unitBall n, ‖∇ (φ : E n → ℝ) x‖ ^ 2 ∂volume0 n := by
    apply integral_congr_ae
    filter_upwards [dirichletTestGradientToL2_ae φ] with x hx
    rw [hx]
  rw [norm_L2_sq_eq_integral, norm_L2_sq_eq_integral, hValue, hGrad]
  simp only [Real.norm_eq_abs, sq_abs]
  have he (x : E n) : ‖∇ (φ : E n → ℝ) x‖ = ‖fderiv ℝ (φ : E n → ℝ) x‖ := by
    rw [← toDual_gradient, LinearIsometryEquiv.norm_map]
  simp_rw [he]
  exact h

/-- The Dirichlet Poincaré estimate extends to the closed graph space. -/
theorem dirichletSobolev_poincare {n : ℕ} (hn : 0 < n) (w : DirichletSobolev n) :
    (n : ℝ) ^ 2 * ‖(w : DirichletBallL2Pair n).fst‖ ^ 2 ≤ ‖(w : DirichletBallL2Pair n).snd‖ ^ 2 := by
  let S : Set (DirichletBallL2Pair n) := {z | (n : ℝ) ^ 2 * ‖z.fst‖ ^ 2 ≤ ‖z.snd‖ ^ 2}
  have hS : IsClosed S := isClosed_le (by fun_prop) (by fun_prop)
  have hSub : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ S := by
    rintro _ ⟨φ, rfl⟩
    exact dirichletTestL2_poincare hn φ
  have hClosure : closure ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ S :=
    closure_minimal hSub hS
  exact hClosure w.property

/-- Lax–Milgram gives a bounded linear solution operator into the closed
Dirichlet function–gradient graph, with uniqueness for each forcing. -/
theorem exists_weakDirichletSolutionCLM {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ((volume0 n).restrict (unitBall n))) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂(volume0 n).restrict (unitBall n), ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    : ∃ S : DirichletBallL2 n ℝ →L[ℝ] DirichletSobolev n, ∀ g,
      let P (u : DirichletSobolev n) := ∀ w : DirichletSobolev n,
        (∫ x in unitBall n, inner ℝ (A x ((u : DirichletBallL2Pair n).snd x))
          ((w : DirichletBallL2Pair n).snd x) ∂volume0 n) =
        ∫ x in unitBall n, g x * ((w : DirichletBallL2Pair n).fst x) ∂volume0 n
      P (S g) ∧ ∀ v, P v → v = S g := by
  let μ := (volume0 n).restrict (unitBall n)
  let V : Type := DirichletBallL2 n (E n)
  let W := DirichletSobolev n
  let G : W →L[ℝ] V := (WithLp.sndL 2 ℝ _ _).comp (dirichletSobolevSubmodule n).subtypeL
  let F : W →L[ℝ] DirichletBallL2 n ℝ :=
    (WithLp.fstL 2 ℝ _ _).comp (dirichletSobolevSubmodule n).subtypeL
  let eval := (ContinuousLinearMap.apply (E := E n) ℝ (E n)).flip
  let T : V →L[ℝ] V := eval.holderL μ ⊤ 2 2 (hA.toLp A)
  let B : W →L[ℝ] W →L[ℝ] ℝ := (innerSL ℝ (E := V)).bilinearComp (T.comp G) G
  have hT (v : V) : T v =ᵐ[μ] fun x => A x (v x) := by
    change eval.holder 2 (hA.toLp A) v =ᵐ[μ] _
    refine EventuallyEq.trans (eval.coeFn_holder (hA.toLp A) v) ?_
    filter_upwards [MemLp.coeFn_toLp hA] with x hx
    change (hA.toLp A) x (v x) = A x (v x)
    rw [hx]
  have hB (u w : W) : B u w =
      ∫ x in unitBall n, inner ℝ (A x ((u : DirichletBallL2Pair n).snd x))
        ((w : DirichletBallL2Pair n).snd x) ∂volume0 n := by
    change inner ℝ (T (G u)) (G w) = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT (G u)] with x hx
    change inner ℝ (T (G u) x) (G w x) = inner ℝ (A x (G u x)) (G w x)
    rw [hx]
  have hLow (w : W) : l * ‖G w‖ ^ 2 ≤ B w w := by
    change l * ‖G w‖ ^ 2 ≤ inner ℝ (T (G w)) (G w)
    rw [norm_L2_sq_eq_integral, MeasureTheory.L2.inner_def, ← integral_const_mul]
    have hi : Integrable (fun x => ‖G w x‖ ^ 2) μ := by
      simpa only [real_inner_self_eq_norm_sq] using
        (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (G w) (G w))
    apply integral_mono_ae (hi.const_mul l) (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) _ _)
    filter_upwards [hE, hT (G w)] with x hx hTx
    rw [hTx]
    exact hx (G w x)
  have hNorm (w : W) : ‖w‖ ^ 2 ≤ 2 * ‖G w‖ ^ 2 := by
    have hp := dirichletSobolev_poincare hn w
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith only [hnR]
    have hp' := (mul_le_mul_of_nonneg_right hnSq (sq_nonneg ‖(w : DirichletBallL2Pair n).fst‖)).trans hp
    change ‖(w : DirichletBallL2Pair n)‖ ^ 2 ≤ 2 * ‖(w : DirichletBallL2Pair n).snd‖ ^ 2
    rw [WithLp.prod_norm_sq_eq_of_L2]
    linarith only [hp']
  have hCoer : IsCoercive B := by
    refine ⟨l / 2, by positivity, fun w => ?_⟩
    have h := mul_le_mul_of_nonneg_left (hNorm w) (show 0 ≤ l / 2 by positivity)
    nlinarith only [h, hLow w]
  let e := hCoer.continuousLinearEquivOfBilin
  let D := (innerSL ℝ (E := DirichletBallL2 n ℝ)).bilinearComp
    (ContinuousLinearMap.id ℝ (DirichletBallL2 n ℝ)) F
  let J := (InnerProductSpace.toDual ℝ W).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let S := e.symm.toContinuousLinearMap.comp (J.comp D)
  refine ⟨S, fun g => ?_⟩
  let R := D g
  let r := J R
  let u := S g
  have hR (w : W) : R w = ∫ x in unitBall n, g x * ((w : DirichletBallL2Pair n).fst x) ∂volume0 n := by
    change inner ℝ g (F w) = _
    rw [MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
    rfl
  have hr (w : W) : inner ℝ r w = R w :=
    congrArg (fun q : W →L[ℝ] ℝ => q w) ((InnerProductSpace.toDual ℝ W).apply_symm_apply R)
  have hu : e u = r := e.apply_symm_apply r
  have hForm (v w : W) : inner ℝ (e v) w = B v w :=
    hCoer.continuousLinearEquivOfBilin_apply v w
  refine ⟨?_, ?_⟩
  · intro w
    have hBw : B u w = R w := calc
      B u w = inner ℝ (e u) w := (hForm u w).symm
      _ = inner ℝ r w := congrArg (fun z => inner ℝ z w) hu
      _ = R w := hr w
    exact (hB u w).symm.trans (hBw.trans (hR w))
  · intro v hv
    have hv' (w : W) : inner ℝ r w = B v w :=
      (hr w).trans ((hR w).trans ((hv w).symm.trans (hB v w).symm))
    have heq : r = e v := hCoer.unique_continuousLinearEquivOfBilin hv'
    exact e.injective (heq.symm.trans hu.symm)

/-- A bounded uniformly elliptic coefficient field has a unique weak
Dirichlet solution in the closed function–gradient graph. -/
theorem existsUnique_weakDirichletSolution {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ((volume0 n).restrict (unitBall n))) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂(volume0 n).restrict (unitBall n), ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (g : DirichletBallL2 n ℝ) :
    ∃! u : DirichletSobolev n, ∀ w : DirichletSobolev n,
      (∫ x in unitBall n, inner ℝ (A x ((u : DirichletBallL2Pair n).snd x))
        ((w : DirichletBallL2Pair n).snd x) ∂volume0 n) =
      ∫ x in unitBall n, g x * ((w : DirichletBallL2Pair n).fst x) ∂volume0 n := by
  obtain ⟨S, hS⟩ := exists_weakDirichletSolutionCLM hn hA hl hE
  exact ⟨S g, (hS g).1, (hS g).2⟩

end KEBall
