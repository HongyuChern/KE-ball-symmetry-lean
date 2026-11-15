import KEBall.DirichletRegularity
import Mathlib.Analysis.Normed.Operator.Banach

/-! A Banach realization of finite-order weak Sobolev spaces on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Integration against a smooth compactly supported test is bounded on L². -/
private noncomputable def dirichletL2Pairing {n : ℕ} (ψ : 𝓓B[n]) :
    DirichletBallL2 n ℝ →L[ℝ] ℝ :=
  innerSL ℝ (dirichletTestToL2 ψ)

private theorem dirichletL2Pairing_apply {n : ℕ} (ψ : 𝓓B[n]) (f : DirichletBallL2 n ℝ) :
    dirichletL2Pairing ψ f = ∫ x, ψ x * f x ∂ν[n] := by
  change inner ℝ (dirichletTestToL2 ψ) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactTestToL2_ae (μ := ν[n]) ψ] with x hx
  change inner ℝ (compactTestToL2 ν[n] ψ x) (f x) = _
  rw [hx, Real.inner_apply, mul_comm]

/-- Distributional pairing with any fixed derivative test is bounded on L². -/
noncomputable def dirichletWeakTestCLM {n : ℕ} :
    List (E n) → 𝓓B[n] → DirichletBallL2 n ℝ →L[ℝ] ℝ
  | [], ψ => dirichletL2Pairing ψ
  | d :: ds, ψ => -dirichletWeakTestCLM ds (dirichletTestLineDerivative d ψ)

theorem dirichletWeakTestCLM_apply {n : ℕ} (ds : List (E n)) (ψ : 𝓓B[n])
    (f : DirichletBallL2 n ℝ) :
    dirichletWeakTestCLM ds ψ f = dirichletWeakDerivativeTest f ds ψ := by
  induction ds generalizing ψ with
  | nil => exact dirichletL2Pairing_apply ψ f
  | cons d ds ih => simp only [dirichletWeakTestCLM, dirichletWeakDerivativeTest,
      neg_apply, ih]

/-- The finite set of lists of coordinate directions of length at most k. -/
abbrev DirichletJetIndex (n k : ℕ) := Σ j : Fin (k + 1), Fin j.val → Fin (2 * n)

noncomputable def dirichletJetDirections {n k : ℕ} (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (i : DirichletJetIndex n k) : List (E n) :=
  List.ofFn (fun j => b (i.2 j))

noncomputable abbrev DirichletJetGraphAmbient (n k : ℕ) :=
  DirichletBallL2 n ℝ × (DirichletJetIndex n k → DirichletBallL2 n ℝ)

private noncomputable def dirichletJetConstraint {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (i : DirichletJetIndex n k)
    (ψ : 𝓓B[n]) : DirichletJetGraphAmbient n k →L[ℝ] ℝ :=
  (dirichletWeakTestCLM (dirichletJetDirections b i) ψ).comp
      (ContinuousLinearMap.fst ℝ _ _) -
    (dirichletL2Pairing ψ).comp ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ _ _))

/-- The graph of all coordinate derivatives up to order k. -/
noncomputable def dirichletSobolevJetGraph {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) :
    Submodule ℝ (DirichletJetGraphAmbient n k) :=
  ⨅ i, ⨅ ψ : 𝓓B[n], (dirichletJetConstraint b i ψ).ker

theorem isClosed_dirichletSobolevJetGraph {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) :
    IsClosed (dirichletSobolevJetGraph (k := k) b : Set (DirichletJetGraphAmbient n k)) := by
  simp only [dirichletSobolevJetGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun ψ => (dirichletJetConstraint b i ψ).isClosed_ker

noncomputable instance {n k : ℕ} (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) :
    CompleteSpace (dirichletSobolevJetGraph (k := k) b) :=
  (isClosed_dirichletSobolevJetGraph (k := k) b).completeSpace_coe

theorem mem_dirichletSobolevJetGraph_iff {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (z : DirichletJetGraphAmbient n k) :
    z ∈ dirichletSobolevJetGraph b ↔
      ∀ (i : DirichletJetIndex n k) (ψ : 𝓓B[n]),
        dirichletWeakDerivativeTest z.1 (dirichletJetDirections b i) ψ =
          ∫ x, ψ x * z.2 i x ∂ν[n] := by
  simp only [dirichletSobolevJetGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro ψ
  change dirichletWeakTestCLM (dirichletJetDirections b i) ψ z.1 -
    dirichletL2Pairing ψ (z.2 i) = 0 ↔ _
  rw [sub_eq_zero, dirichletWeakTestCLM_apply, dirichletL2Pairing_apply]

/-- A graph element has precisely the finite weak order recorded by its
coordinate derivatives. -/
theorem hasDirichletWeakDerivativesL2_of_jetGraph {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (z : dirichletSobolevJetGraph (k := k) b) :
    HasDirichletWeakDerivativesL2 (z.val.1 : E n → ℝ) k := by
  apply HasDirichletWeakDerivativesL2.of_coordinate_tests hn b (Lp.memLp z.val.1)
  intro is hLen
  let i : DirichletJetIndex n k := ⟨⟨is.length, Nat.lt_succ_of_le hLen⟩, is.get⟩
  have he : dirichletJetDirections b i = is.map b := by
    change List.ofFn (fun j : Fin is.length => b (is.get j)) = is.map b
    change List.ofFn ((b : Fin (2 * n) → E n) ∘ is.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  exact ⟨_, Lp.memLp (z.val.2 i), fun ψ => he ▸
    (mem_dirichletSobolevJetGraph_iff b z.val).mp z.property i ψ⟩

/-- Every square-integrable function with weak derivatives of order k is
the first component of a closed-graph element. -/
theorem exists_dirichletSobolevJetGraph {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (f : DirichletBallL2 n ℝ)
    (hf : HasDirichletWeakDerivativesL2 (f : E n → ℝ) k) :
    ∃ z : dirichletSobolevJetGraph (k := k) b, z.val.1 = f := by
  classical
  have hFor (i : DirichletJetIndex n k) :=
    hf.2 (dirichletJetDirections b i) (by
      simpa only [dirichletJetDirections, List.length_ofFn] using Nat.le_of_lt_succ i.1.isLt)
  choose F hF heF using hFor
  let z : DirichletJetGraphAmbient n k := (f, fun i => (hF i).toLp (F i))
  refine ⟨⟨z, (mem_dirichletSobolevJetGraph_iff b z).mpr fun i ψ => ?_⟩, rfl⟩
  rw [heF i ψ]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hF i)] with x hx
  change ψ x * F i x = ψ x * ((hF i).toLp (F i)) x
  rw [hx]

private theorem dirichletL2_eq_of_pairings {n : ℕ} (hn : 0 < n)
    (f g : DirichletBallL2 n ℝ) (he : ∀ ψ : 𝓓B[n], dirichletL2Pairing ψ f =
      dirichletL2Pairing ψ g) : f = g := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let h : DirichletBallL2 n ℝ := f - g
  have hLoc : LocallyIntegrableOn (h : E n → ℝ) (unitBall n) ν[n] :=
    ((Lp.memLp h).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn _
  have hZero : ∀ᵐ x ∂ν[n], x ∈ unitBall n → h x = 0 := by
    apply (show IsOpen (unitBall n) from isOpen_ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero hLoc
    intro ψ hψ hψc hψB
    let φ : 𝓓B[n] := ⟨ψ, hψ, hψc, hψB⟩
    change (∫ x, φ x * h x ∂ν[n]) = 0
    rw [← dirichletL2Pairing_apply]
    exact (dirichletL2Pairing φ).map_sub f g |>.trans (sub_eq_zero.mpr (he φ))
  apply sub_eq_zero.mp
  apply Lp.ext
  filter_upwards [hZero, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν[n])] with x h₀ hB hz
  exact (h₀ hB).trans hz.symm

/-- Projection to the underlying function is injective by uniqueness
of weak derivatives. -/
theorem dirichletSobolevJetGraph_fst_injective {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) :
    Function.Injective (fun z : dirichletSobolevJetGraph (k := k) b => z.val.1) := by
  intro x y hxy
  change x.val.1 = y.val.1 at hxy
  apply Subtype.ext
  refine Prod.ext hxy (funext fun i => dirichletL2_eq_of_pairings hn _ _ fun ψ => ?_)
  rw [dirichletL2Pairing_apply, dirichletL2Pairing_apply,
    ← (mem_dirichletSobolevJetGraph_iff b x.val).mp x.property i ψ,
    ← (mem_dirichletSobolevJetGraph_iff b y.val).mp y.property i ψ, hxy]

/-- An operator bounded on L² that gains weak regularity induces a bounded
operator on the corresponding Banach graphs. -/
theorem exists_dirichletSobolevJetGraph_lift {n k m : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (T : DirichletBallL2 n ℝ →L[ℝ] DirichletBallL2 n ℝ)
    (hT : ∀ f : DirichletBallL2 n ℝ, HasDirichletWeakDerivativesL2 (f : E n → ℝ) k →
      HasDirichletWeakDerivativesL2 (T f : E n → ℝ) m) :
    ∃ R : dirichletSobolevJetGraph (k := k) b →L[ℝ] dirichletSobolevJetGraph (k := m) b,
      ∀ z, (R z).val.1 = T z.val.1 := by
  classical
  have hEx (z : dirichletSobolevJetGraph (k := k) b) :=
    exists_dirichletSobolevJetGraph b (T z.val.1)
      (hT z.val.1 (hasDirichletWeakDerivativesL2_of_jetGraph hn b z))
  choose R hR using hEx
  let L : dirichletSobolevJetGraph (k := k) b →ₗ[ℝ] dirichletSobolevJetGraph (k := m) b :=
    { toFun := R
      map_add' := fun x y => dirichletSobolevJetGraph_fst_injective hn b (by
        change (R (x + y)).val.1 = (R x).val.1 + (R y).val.1
        rw [hR, hR, hR]
        exact T.map_add x.val.1 y.val.1)
      map_smul' := fun a x => dirichletSobolevJetGraph_fst_injective hn b (by
        change (R (a • x)).val.1 = a • (R x).val.1
        rw [hR, hR]
        exact T.map_smul a x.val.1) }
  have hCL : Continuous L := by
    apply L.continuous_of_seq_closed_graph
    intro seq x y hx hy
    have h₁ : Tendsto (fun j => (L (seq j)).val.1) atTop (𝓝 y.val.1) :=
      (continuous_fst.comp continuous_subtype_val).continuousAt.tendsto.comp hy
    have h₂ : Tendsto (fun j => (L (seq j)).val.1) atTop (𝓝 (T x.val.1)) := by
      simp only [show ∀ z, (L z).val.1 = T z.val.1 from hR]
      exact (T.continuous.comp (continuous_fst.comp continuous_subtype_val)).continuousAt.tendsto.comp hx
    exact dirichletSobolevJetGraph_fst_injective hn b ((tendsto_nhds_unique h₁ h₂).trans (hR x).symm)
  exact ⟨⟨L, hCL⟩, hR⟩

end KEBall
