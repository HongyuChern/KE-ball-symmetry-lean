import KEBall.DirichletSobolevProduct
import KEBall.DirichletCofactorSobolevInverse
import KEBall.DirichletSmoothLinearizedSolution
import KEBall.DirichletSmoothRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The continuous representative and zero boundary subspace of H^k. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local instance closedBall_compactSpace (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem eqOn_closedUnitBall_of_ae {n : ℕ} {f g : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n)) (hg : ContinuousOn g (closedUnitBall n))
    (he : f =ᵐ[ν[n]] g) : EqOn f g (closedUnitBall n) := by
  have hHaar : (volume0 n).IsAddHaarMeasure := by
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  have he' := (volume0 n).eqOn_open_of_ae_eq he isOpen_ball
    (hf.mono ball_subset_closedBall) (hg.mono ball_subset_closedBall)
  have hClosure : closure (unitBall n) = closedUnitBall n := closure_ball (0 : E n) (by norm_num)
  exact he'.of_subset_closure hf hg ball_subset_closedBall (by rw [hClosure])

/-- Continuous representatives of H^k functions satisfy a common
supremum bound on the closed ball. -/
theorem exists_continuousOn_dirichletSobolevJetGraph_rep {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hk : 2 * (2 * n + 1) ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : dirichletSobolevJetGraph (k := k) b,
      ∃ f : E n → ℝ, ContinuousOn f (closedUnitBall n) ∧ f =ᵐ[ν[n]] z.val.1 ∧
        ∀ x ∈ closedUnitBall n, ‖f x‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC, hBound⟩ := exists_norm_iteratedLineDerivative_le_dirichletSobolevJetOfSmooth hn b
  refine ⟨C, hC, fun z => ?_⟩
  have hReg := hasDirichletWeakDerivativesL2_of_jetGraph hn b z
  have hReg' : HasDirichletWeakDerivativesL2 (z.val.1 : E n → ℝ) (0 + 2 * (2 * n + 1)) :=
    hReg.of_le (by simpa using hk)
  obtain ⟨f, P, hT, he, hLim⟩ := hReg'.exists_closedUnitBall_finiteJet hn
  refine ⟨f, hT.contDiffOn.continuousOn, he, fun x hx => ?_⟩
  let fJ := dirichletSmoothApproximation (z.val.1 : E n → ℝ)
  have hfJ (j : ℕ) : ContDiff ℝ ∞ (fJ j) :=
    contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j
  have hJet := tendsto_dirichletSobolevJetOfSmoothApproximation hn b z
  have hP : Tendsto (fun j => fJ j x) atTop (𝓝 (f x)) := by
    have h := (continuousMultilinearCurryFin0 ℝ (E n) ℝ).continuous.continuousAt.tendsto.comp
      ((hLim 0 le_rfl).tendsto_at hx)
    rw [← hT.zero_eq x hx]
    simpa only [Function.comp_def, continuousMultilinearCurryFin0_apply,
      ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply, fJ] using h
  apply le_of_tendsto_of_tendsto hP.norm (hJet.norm.const_mul C)
  filter_upwards with j
  have h := hBound k (fJ j) (hfJ j) [] (by simp; omega) x hx
  exact h

/-- The continuous representative map is bounded and linear for
sufficiently high finite Sobolev order. -/
theorem exists_dirichletSobolevJetGraph_toContinuousMap {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hk : 2 * (2 * n + 1) ≤ k) :
    ∃ T : dirichletSobolevJetGraph (k := k) b →L[ℝ] C(ClosedBall n, ℝ),
      ∀ (z : dirichletSobolevJetGraph (k := k) b) (f : E n → ℝ),
        ContinuousOn f (closedUnitBall n) → f =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = f x := by
  classical
  let H := dirichletSobolevJetGraph (k := k) b
  obtain ⟨C, hC, hRep⟩ := exists_continuousOn_dirichletSobolevJetGraph_rep hn b hk
  choose f hf he hBound using hRep
  let R (z : H) : C(ClosedBall n, ℝ) :=
    ⟨fun x => f z x, continuousOn_iff_continuous_domRestrict.mp (hf z)⟩
  let L : H →ₗ[ℝ] C(ClosedBall n, ℝ) :=
    { toFun := R
      map_add' := fun z w => by
        ext x
        have hEq : f (z + w) =ᵐ[ν[n]] fun y => f z y + f w y := by
          filter_upwards [he (z + w), he z, he w, Lp.coeFn_add z.val.1 w.val.1]
            with y hzw hz hw hAdd
          change ((z + w : H).val.1 : E n → ℝ) y = _ at hAdd
          rw [hzw, hAdd, hz, hw]
          rfl
        exact eqOn_closedUnitBall_of_ae (hf (z + w)) ((hf z).add (hf w)) hEq x.property
      map_smul' := fun a z => by
        ext x
        have hEq : f (a • z) =ᵐ[ν[n]] fun y => a * f z y := by
          filter_upwards [he (a • z), he z, Lp.coeFn_smul a z.val.1] with y haz hz hSmul
          change ((a • z : H).val.1 : E n → ℝ) y = _ at hSmul
          rw [haz, hSmul]
          simp only [Pi.smul_apply, smul_eq_mul, hz]
        exact eqOn_closedUnitBall_of_ae (hf (a • z))
          (continuousOn_const.mul (hf z)) hEq x.property }
  let T := L.mkContinuous C fun z =>
    (ContinuousMap.norm_le (R z) (mul_nonneg hC (norm_nonneg z))).mpr fun x => hBound z x x.property
  exact ⟨T, fun z g hg hEg x =>
    eqOn_closedUnitBall_of_ae (hf z) hg ((he z).trans hEg.symm) x.property⟩

/-- The spherical zero boundary condition is a closed subspace of the
finite-order Sobolev graph. -/
noncomputable def dirichletSobolevJetGraph_zeroTrace {n k : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)}
    (T : dirichletSobolevJetGraph (k := k) b →L[ℝ] C(ClosedBall n, ℝ)) :
    Submodule ℝ (dirichletSobolevJetGraph (k := k) b) :=
  ⨅ x : Sphere n, ((ContinuousMap.evalCLM ℝ
    (⟨x.val, sphere_subset_closedBall x.property⟩ : ClosedBall n)).comp T).ker

theorem mem_dirichletSobolevJetGraph_zeroTrace {n k : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)}
    (T : dirichletSobolevJetGraph (k := k) b →L[ℝ] C(ClosedBall n, ℝ))
    (z : dirichletSobolevJetGraph (k := k) b) :
    z ∈ dirichletSobolevJetGraph_zeroTrace T ↔
      ∀ x : Sphere n, T z ⟨x.val, sphere_subset_closedBall x.property⟩ = 0 := by
  simp only [dirichletSobolevJetGraph_zeroTrace, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

theorem isClosed_dirichletSobolevJetGraph_zeroTrace {n k : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)}
    (T : dirichletSobolevJetGraph (k := k) b →L[ℝ] C(ClosedBall n, ℝ)) :
    IsClosed (dirichletSobolevJetGraph_zeroTrace T : Set (dirichletSobolevJetGraph (k := k) b)) := by
  simp only [dirichletSobolevJetGraph_zeroTrace, Submodule.coe_iInf]
  exact isClosed_iInter fun x : Sphere n =>
    ((ContinuousMap.evalCLM ℝ
      (⟨x.val, sphere_subset_closedBall x.property⟩ : ClosedBall n)).comp T).isClosed_ker

noncomputable instance {n k : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)}
    (T : dirichletSobolevJetGraph (k := k) b →L[ℝ] C(ClosedBall n, ℝ)) :
    CompleteSpace (dirichletSobolevJetGraph_zeroTrace T) :=
  (isClosed_dirichletSobolevJetGraph_zeroTrace T).completeSpace_coe

/-- The bounded cofactor solution map takes values in the zero-trace
subspace at every order for which the continuous trace exists. -/
theorem exists_dirichletCofactorSobolevInverse_zeroTrace {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (T : dirichletSobolevJetGraph (k := k + 2) b →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : dirichletSobolevJetGraph (k := k + 2) b) (f : E n → ℝ),
      ContinuousOn f (closedUnitBall n) → f =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = f x)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∃ (S : DirichletBallL2 n ℝ →L[ℝ] DirichletSobolev n)
      (R : dirichletSobolevJetGraph (k := k) b →L[ℝ] dirichletSobolevJetGraph_zeroTrace T),
      (∀ g, IsDirichletWeakSolution (dirichletCofactorOperator u) g (S g)) ∧
      ∀ z, (R z).val.val.1 = (S z.val.1 : DirichletBallL2Pair n).fst := by
  obtain ⟨S, R, hS, hR⟩ := exists_dirichletCofactorSobolevInverse hn b
    hu huP ha hl hDensity hElliptic k
  have hSmooth {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) :
      R (dirichletSobolevJetOfSmooth hn b hf) ∈ dirichletSobolevJetGraph_zeroTrace T := by
    let g := dirichletSobolevJetOfSmooth (k := k) hn b hf
    have hf' : SmoothNear (closedUnitBall n) f := ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩
    obtain ⟨w, v, hw, hv, hvW, hv0, _⟩ :=
      exists_smoothNear_closedUnitBall_cofactor_solution hn hu huP ha hl hDensity hElliptic
        g.val.1 hf' (dirichletSobolevJetOfSmooth_fst_ae hn b hf)
    obtain ⟨w₀, _, hUnique⟩ := existsUnique_weakCofactorDirichletSolution hn
      hu huP ha hl hDensity hElliptic g.val.1
    have hwS : w = S g.val.1 := (hUnique w hw).trans (hUnique _ (hS _)).symm
    have hvR : v =ᵐ[ν[n]] (R g).val.1 := by rwa [hR, ← hwS]
    have hvC : ContinuousOn v (closedUnitBall n) :=
      fun x hx => (hv.contDiffAt hx).continuousAt.continuousWithinAt
    exact (mem_dirichletSobolevJetGraph_zeroTrace T (R g)).mpr fun x =>
      (hT (R g) v hvC hvR _).trans (hv0 x.val x.property)
  have hRange (z : dirichletSobolevJetGraph (k := k) b) :
      R z ∈ dirichletSobolevJetGraph_zeroTrace T := by
    have hL := (R.continuous.tendsto z).comp (tendsto_dirichletSobolevJetOfSmoothApproximation hn b z)
    exact (isClosed_dirichletSobolevJetGraph_zeroTrace T).mem_of_tendsto hL
      (Eventually.of_forall fun j => hSmooth (contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j))
  exact ⟨S, R.codRestrict _ hRange, hS, hR⟩

end KEBall
