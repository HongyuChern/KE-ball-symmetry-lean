import KEBall.DirichletSobolevDeterminant
import KEBall.MoserTrudingerSmoothVariation
import KEBall.DirichletSobolevTrace
import KEBall.DirichletCofactorMaximum
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Testing the Sobolev determinant derivative against smooth functions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

private noncomputable def coordinateSobolevPairing {n k : ℕ} (ψ : 𝓓B[n]) :
    CoordinateSobolev n k →L[ℝ] ℝ :=
  (dirichletWeakTestCLM [] ψ).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (CoordinateSobolev n k).subtypeL)

private theorem coordinateSobolevPairing_apply {n k : ℕ}
    (ψ : 𝓓B[n]) (z : CoordinateSobolev n k) :
    coordinateSobolevPairing ψ z = ∫ x, ψ x * z.val.1 x ∂ν[n] :=
  dirichletWeakTestCLM_apply [] ψ z.val.1

private theorem coordinateSobolevJetOfSmooth_affine {n k : ℕ} (hn : 0 < n)
    {f h : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (t : ℝ) :
    let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
    dirichletSobolevJetOfSmooth (k := k) hn b (hf.add (hh.const_smul t)) =
      dirichletSobolevJetOfSmooth hn b hf + t • dirichletSobolevJetOfSmooth hn b hh := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let u := dirichletSobolevJetOfSmooth (k := k) hn b hf
  let v := dirichletSobolevJetOfSmooth (k := k) hn b hh
  apply dirichletSobolevJetGraph_fst_injective hn b
  change (dirichletSobolevJetOfSmooth (k := k) hn b (hf.add (hh.const_smul t))).val.1 =
    u.val.1 + t • v.val.1
  apply Lp.ext
  filter_upwards [dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hf.add (hh.const_smul t)),
    dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b hf, dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b hh,
    Lp.coeFn_smul t v.val.1, Lp.coeFn_add u.val.1 (t • v.val.1)] with x ht hu hv hs ha
  rw [ht, ha, Pi.add_apply, hu, hs, Pi.smul_apply, hv]

/-- The derivative of a smooth Sobolev realization of the determinant is
identified by differentiating its integrals against fixed tests. -/
theorem dirichletSobolevDeterminant_fderiv_test_ofSmooth {n k : ℕ} (hn : 0 < n)
    {F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k} (hF : ContDiff ℝ ∞ F)
    (hEq : ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
      (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
        =ᵐ[ν[n]] fun x => (complexHessian f x).det.re)
    {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (ψ : 𝓓B[n]) :
    let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
    let z := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
    let w := dirichletSobolevJetOfSmooth (k := k + 2) hn b hv
    (∫ x, ψ x * (fderiv ℝ F z w).val.1 x ∂ν[n]) = ∫ x, ψ x * MoserTrudinger.cofactorContraction u v x ∂ν[n] := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let z := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
  let w := dirichletSobolevJetOfSmooth (k := k + 2) hn b hv
  let P : CoordinateSobolev n k →L[ℝ] ℝ := coordinateSobolevPairing ψ
  have he (t : ℝ) : P (F (z + t • w)) =
      ∫ x, ψ x * (complexHessian (u + t • v) x).det.re ∂ν[n] := by
    rw [show z + t • w = dirichletSobolevJetOfSmooth hn b (hu.add (hv.const_smul t)) from
      (coordinateSobolevJetOfSmooth_affine hn hu hv t).symm, coordinateSobolevPairing_apply]
    apply integral_congr_ae
    filter_upwards [hEq _ (hu.add (hv.const_smul t))] with x hx
    rw [hx]
    rfl
  have hLine : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const w).const_add z
  have hD : HasDerivAt (fun t : ℝ => F (z + t • w)) (fderiv ℝ F z w) 0 := by
    have h := (hF.differentiable (by simp) (z + (0 : ℝ) • w)).hasFDerivAt
    simpa only [zero_smul, add_zero, Function.comp_def] using h.comp_hasDerivAt 0 hLine
  have hDP := P.hasFDerivAt.comp_hasDerivAt 0 hD
  have hInt := MoserTrudinger.hasDerivAt_integral_test_mul_det hn isOpen_univ
    (subset_univ _) hu.contDiffOn hv.contDiffOn 0 ψ.continuous.continuousOn
  have hInt' : HasDerivAt (fun t : ℝ => ∫ x, ψ x * (complexHessian (u + t • v) x).det.re ∂ν[n])
      (∫ x, ψ x * MoserTrudinger.cofactorContraction u v x ∂ν[n]) 0 := by
    simpa only [zero_smul, add_zero] using hInt
  change (∫ x, ψ x * (fderiv ℝ F z w).val.1 x ∂ν[n]) = _
  rw [← coordinateSobolevPairing_apply]
  exact hDP.unique (hInt'.congr_of_eventuallyEq (Eventually.of_forall he))

private theorem continuousOn_cofactorContraction_of_smooth {n : ℕ} {u v : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContinuousOn (MoserTrudinger.cofactorContraction u v) (closedUnitBall n) := by
  refine ContinuousOn.mono (s := univ) ?_ (subset_univ _)
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (matrixField_adjugate_contDiffOn
    (complexHessian_contDiffOn isOpen_univ hu.contDiffOn) j i).continuousOn.mul
    (complexHessian_contDiffOn isOpen_univ hv.contDiffOn i j).continuousOn

/-- On smooth directions the Sobolev derivative is represented by the
pointwise cofactor contraction. -/
theorem dirichletSobolevDeterminant_fderiv_ae_ofSmooth {n k : ℕ} (hn : 0 < n)
    {F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k} (hF : ContDiff ℝ ∞ F)
    (hEq : ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
      (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
        =ᵐ[ν[n]] fun x => (complexHessian f x).det.re)
    {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
    let z := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
    let w := dirichletSobolevJetOfSmooth (k := k + 2) hn b hv
    (fderiv ℝ F z w).val.1 =ᵐ[ν[n]] MoserTrudinger.cofactorContraction u v := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let z := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
  let w := dirichletSobolevJetOfSmooth (k := k + 2) hn b hv
  change (fderiv ℝ F z w).val.1 =ᵐ[ν[n]] _
  apply ae_eq_on_unitBall_of_tests
  · exact ((Lp.memLp (fderiv ℝ F z w).val.1).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  · exact ((continuousOn_cofactorContraction_of_smooth hu hv).mono ball_subset_closedBall)
      |>.locallyIntegrableOn measurableSet_ball
  · exact dirichletSobolevDeterminant_fderiv_test_ofSmooth hn hF hEq hu hv

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private theorem tendsto_continuousMap_apply {n : ℕ} (x : ClosedBall n)
    {a : ℕ → C(ClosedBall n, ℝ)} {b : C(ClosedBall n, ℝ)}
    (h : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun j => a j x) atTop (𝓝 (b x)) :=
  ((ContinuousMap.evalCLM ℝ x).continuous.tendsto b).comp h

/-- A null direction of the Sobolev determinant derivative with zero
boundary trace vanishes. The smooth maximum estimate passes to the
Sobolev limit using the continuous traces of both input and output. -/
theorem dirichletSobolevDeterminant_fderiv_eq_zero_of_zeroTrace {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
    {F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k} (hF : ContDiff ℝ ∞ F)
    (hEq : ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
      (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
        =ᵐ[ν[n]] fun x => (complexHessian f x).det.re)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (f : E n → ℝ),
      ContinuousOn f (closedUnitBall n) → f =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = f x)
    (Q : CoordinateSobolev n k →L[ℝ] C(ClosedBall n, ℝ))
    (hQ : ∀ (z : CoordinateSobolev n k) (f : E n → ℝ),
      ContinuousOn f (closedUnitBall n) → f =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, Q z x = f x)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a : ℝ} (ha : 0 < a) (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (z : CoordinateSobolev n (k + 2)) (hz : z ∈ dirichletSobolevJetGraph_zeroTrace T)
    (hLz : fderiv ℝ F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hu) z = 0) :
    z = 0 := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let L := fderiv ℝ F (dirichletSobolevJetOfSmooth hn b hu)
  let v := dirichletSmoothApproximation (z.val.1 : E n → ℝ)
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) := contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j
  let w (j : ℕ) : CoordinateSobolev n (k + 2) := dirichletSobolevJetOfSmooth hn b (hv j)
  have hW : Tendsto w atTop (𝓝 z) := tendsto_dirichletSobolevJetOfSmoothApproximation hn b z
  let c (j : ℕ) := ‖T (w j) - T z‖
  let m (j : ℕ) := ‖Q (L (w j))‖
  have huN : SmoothNear (closedUnitBall n) u := ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  have hCon (j : ℕ) (x : ClosedBall n) :
      Q (L (w j)) x = MoserTrudinger.cofactorContraction u (v j) x :=
    hQ _ _ (continuousOn_cofactorContraction_of_smooth hu (hv j))
      (dirichletSobolevDeterminant_fderiv_ae_ofSmooth hn hF hEq hu (hv j)).symm x
  have hTr (j : ℕ) (x : ClosedBall n) : T (w j) x = v j x :=
    hT _ _ (hv j).continuous.continuousOn (dirichletSobolevJetOfSmooth_fst_ae hn b (hv j)).symm x
  have hBound (j : ℕ) (x : ClosedBall n) : |v j x| ≤ c j + (m j / (a * n)) * (-u x) := by
    apply abs_le_of_cofactorContraction_abs_le_of_boundary hn huN hu0 huP
      (⟨univ, isOpen_univ, subset_univ _, (hv j).contDiffOn⟩ : SmoothNear (closedUnitBall n) (v j))
      _ ha (norm_nonneg _) hDensity _ x.val x.property
    · intro y hy
      let Y : ClosedBall n := ⟨y, sphere_subset_closedBall hy⟩
      have ht0 : T z Y = 0 := (mem_dirichletSobolevJetGraph_zeroTrace T z).mp hz ⟨y, hy⟩
      have hn := ContinuousMap.norm_coe_le_norm (T (w j) - T z) Y
      change ‖T (w j) Y - T z Y‖ ≤ c j at hn
      rw [hTr, ht0, sub_zero, Real.norm_eq_abs] at hn
      exact hn
    · intro y hy
      let Y : ClosedBall n := ⟨y, ball_subset_closedBall hy⟩
      have hn := ContinuousMap.norm_coe_le_norm (Q (L (w j))) Y
      rw [hCon, Real.norm_eq_abs] at hn
      exact hn
  have hTw : Tendsto (fun j => T (w j)) atTop (𝓝 (T z)) :=
    (T.continuous.tendsto z).comp hW
  have hc : Tendsto c atTop (𝓝 0) := by
    have h := (hTw.sub (tendsto_const_nhds (x := T z))).norm
    simpa only [c, sub_self, norm_zero] using h
  have hm : Tendsto m atTop (𝓝 0) := by
    have h := ((Q.comp L).continuous.tendsto z).comp hW
    have hLz' : L z = 0 := hLz
    simpa only [m, Function.comp_def, ContinuousLinearMap.comp_apply, hLz', map_zero, norm_zero] using h.norm
  have hZero (x : ClosedBall n) : T z x = 0 := by
    have hVal : Tendsto (fun j => v j x) atTop (𝓝 (T z x)) :=
      (tendsto_continuousMap_apply x hTw).congr (fun j => hTr j x)
    have hR : Tendsto (fun j => c j + (m j / (a * n)) * (-u x)) atTop (𝓝 0) := by
      simpa only [zero_div, zero_mul, add_zero] using
        hc.add ((hm.div_const (a * n)).mul_const (-u x))
    exact abs_eq_zero.mp (le_antisymm
      (le_of_tendsto_of_tendsto hVal.abs hR (Eventually.of_forall fun j => hBound j x)) (abs_nonneg _))
  obtain ⟨_, _, hRep⟩ := exists_continuousOn_dirichletSobolevJetGraph_rep hn b
    (hk.trans (Nat.le_add_right k 2))
  obtain ⟨f, hf, he, _⟩ := hRep z
  apply dirichletSobolevJetGraph_fst_injective hn b
  apply Lp.ext
  filter_upwards [he, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball),
    Lp.coeFn_zero ℝ 2 ν[n]] with x hx hBall h0
  exact hx.symm.trans (((hT z f hf he ⟨x, ball_subset_closedBall hBall⟩).symm.trans
    (hZero ⟨x, ball_subset_closedBall hBall⟩)).trans h0.symm)

private theorem exists_continuousLinearEquiv_of_bijective {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (hA : Function.Bijective A) :
    ∃ e : X ≃L[ℝ] Y, ∀ x, e x = A x := by
  let e : X ≃ₗ[ℝ] Y := LinearEquiv.ofBijective A.toLinearMap hA
  exact ⟨e.toContinuousLinearEquivOfContinuous A.continuous, fun _ => rfl⟩

private theorem exists_smooth_localInverse_on_nhds_of_equiv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {H : X → Y} {x : X} (hH : ContDiff ℝ ∞ H) (e : X ≃L[ℝ] Y)
    (hD : HasFDerivAt H (e : X →L[ℝ] Y) x) :
    ∃ G : Y → X, (∀ᶠ y in 𝓝 (H x), ContDiffAt ℝ ∞ G y) ∧ G (H x) = x ∧
      ∀ᶠ y in 𝓝 (H x), H (G y) = y := by
  let P := hH.contDiffAt.toOpenPartialHomeomorph H hD (by simp)
  have hX : x ∈ P.source := hH.contDiffAt.mem_toOpenPartialHomeomorph_source hD (by simp)
  have hY : H x ∈ P.target := hH.contDiffAt.image_mem_toOpenPartialHomeomorph_target hD (by simp)
  have hPX : P.symm (H x) = x := P.left_inv hX
  have hRight : ∀ᶠ y in 𝓝 (H x), H (P.symm y) = y :=
    Filter.Eventually.mono (P.open_target.mem_nhds hY) fun y hy => P.right_inv hy
  refine ⟨P.symm, ?_, hPX, hRight⟩
  have hF : Continuous (fderiv ℝ H) :=
    (hH.fderiv_right (m := ∞) (by simp)).continuous
  let A : Set (X →L[ℝ] Y) := range ((↑) : (X ≃L[ℝ] Y) → X →L[ℝ] Y)
  have hA : IsOpen A := ContinuousLinearEquiv.isOpen
  have hxA : fderiv ℝ H x ∈ A := ⟨e, hD.fderiv.symm⟩
  have hQ : Tendsto P.symm (𝓝 (H x)) (𝓝 x) := by
    have ht : Tendsto P.symm (𝓝 (H x)) (𝓝 (P.symm (H x))) :=
      ((P.continuousOn_invFun _ hY).continuousAt (P.open_target.mem_nhds hY)).tendsto
    rwa [hPX] at ht
  filter_upwards [P.open_target.mem_nhds hY,
    (hF.continuousAt.tendsto.comp hQ).eventually (hA.mem_nhds hxA)] with y hy hAy
  obtain ⟨e', he'⟩ := hAy
  apply P.contDiffAt_symm hy (f₀' := e')
  · change HasFDerivAt H (e' : X →L[ℝ] Y) (P.symm y)
    rw [he']
    exact (hH.differentiable (by simp) _).hasFDerivAt
  · exact hH.contDiffAt

private theorem hasFDerivAt_comp_clm {X Y W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (i : X →L[ℝ] Y) {F : Y → W} {x : X} {L : Y →L[ℝ] W}
    (hF : HasFDerivAt F L (i x)) : HasFDerivAt (F ∘ i) (L.comp i) x :=
  hF.comp x i.hasFDerivAt

set_option maxHeartbeats 700000 in
/-- The determinant derivative at a smooth positive Dirichlet potential is
a continuous linear equivalence on the Sobolev space with zero trace. -/
theorem exists_dirichletSobolevDeterminant_fderiv_equiv {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
    {F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k} (hF : ContDiff ℝ ∞ F)
    (hEq : ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
      (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
        =ᵐ[ν[n]] fun x => (complexHessian f x).det.re)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (f : E n → ℝ),
      ContinuousOn f (closedUnitBall n) → f =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = f x)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∃ e : dirichletSobolevJetGraph_zeroTrace T ≃L[ℝ] CoordinateSobolev n k,
      ∀ z, e z = fderiv ℝ F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hu) z.val := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let Z := dirichletSobolevJetGraph_zeroTrace T
  let L := fderiv ℝ F (dirichletSobolevJetOfSmooth hn b hu)
  let A : Z →L[ℝ] CoordinateSobolev n k := L.comp Z.subtypeL
  have huN : SmoothNear (closedUnitBall n) u := ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  obtain ⟨Q, hQ⟩ := exists_dirichletSobolevJetGraph_toContinuousMap hn b hk
  obtain ⟨S, R, hS, hR⟩ := exists_dirichletCofactorSobolevInverse_zeroTrace hn b T hT huN huP
    ha hl hDensity hElliptic
  have hRightSmooth (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) :
      A (R (dirichletSobolevJetOfSmooth hn b hg)) = -dirichletSobolevJetOfSmooth hn b hg := by
    let G : CoordinateSobolev n k := dirichletSobolevJetOfSmooth hn b hg
    have hgN : SmoothNear (closedUnitBall n) g := ⟨univ, isOpen_univ, subset_univ _, hg.contDiffOn⟩
    obtain ⟨w, v, hw, hv, hvW, _, hvEq⟩ :=
      exists_smoothNear_closedUnitBall_cofactor_solution hn huN huP ha hl hDensity hElliptic
        G.val.1 hgN (dirichletSobolevJetOfSmooth_fst_ae hn b hg)
    obtain ⟨_, _, hUnique⟩ := existsUnique_weakCofactorDirichletSolution hn huN huP ha hl hDensity
      hElliptic G.val.1
    have hwS : w = S G.val.1 := (hUnique w hw).trans (hUnique _ (hS _)).symm
    have hvR : v =ᵐ[ν[n]] (R G).val.val.1 := by rwa [hR, ← hwS]
    obtain ⟨U, hU, hSub, hvU⟩ := hv
    obtain ⟨v', _, hv', hvNear⟩ := exists_contDiff_extension_closedUnitBall ⊤ hU hSub hvU
    have hvAE : v' =ᵐ[ν[n]] v := by
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      exact (hvNear x (ball_subset_closedBall hx)).eq_of_nhds
    let V : CoordinateSobolev n (k + 2) := dirichletSobolevJetOfSmooth hn b hv'
    have hV : V = (R G).val := by
      apply dirichletSobolevJetGraph_fst_injective hn b
      exact Lp.ext ((dirichletSobolevJetOfSmooth_fst_ae hn b hv').trans (hvAE.trans hvR))
    change L (R G).val = -G
    rw [← hV]
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [dirichletSobolevDeterminant_fderiv_ae_ofSmooth hn hF hEq hu hv',
      ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball),
      Lp.coeFn_neg G.val.1, dirichletSobolevJetOfSmooth_fst_ae hn b hg]
      with x hx hBall hNeg hG
    change (L V).val.1 x = MoserTrudinger.cofactorContraction u v' x at hx
    change ((-G).val.1 : E n → ℝ) x = _ at hNeg
    rw [hx, hNeg, Pi.neg_apply, hG]
    have hH := complexHessian_congr_of_eventuallyEq (hvNear x (ball_subset_closedBall hBall))
    unfold MoserTrudinger.cofactorContraction
    rw [hH]
    exact hvEq hBall
  have hRight (z : CoordinateSobolev n k) : A (R z) = -z := by
    let G (j : ℕ) : CoordinateSobolev n k := dirichletSobolevJetOfSmooth hn b
      (contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j)
    have hG : Tendsto G atTop (𝓝 z) := tendsto_dirichletSobolevJetOfSmoothApproximation hn b z
    have hAR : Tendsto (fun j => A (R (G j))) atTop (𝓝 (A (R z))) :=
      ((A.comp R).continuous.tendsto z).comp hG
    exact tendsto_nhds_unique hAR (hG.neg.congr (fun j => (hRightSmooth _ _).symm))
  have hSurj : Function.Surjective A := fun z => ⟨R (-z), (hRight (-z)).trans (neg_neg _)⟩
  have hKer : A.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    apply Subtype.ext
    exact dirichletSobolevDeterminant_fderiv_eq_zero_of_zeroTrace hn hk hF hEq T hT Q hQ
      hu hu0 huP ha hDensity z.val z.property hz
  have hInj : Function.Injective A.toLinearMap := by
    intro x y hxy
    have hz : x - y ∈ A.ker := by
      change A (x - y) = 0
      exact (A.map_sub x y).trans (sub_eq_zero.mpr hxy)
    rw [hKer, Submodule.mem_bot] at hz
    exact sub_eq_zero.mp hz
  have hBij : Function.Bijective (A : Z → CoordinateSobolev n k) := ⟨hInj, hSurj⟩
  obtain ⟨e, he⟩ := @exists_continuousLinearEquiv_of_bijective Z (CoordinateSobolev n k)
    _ _ _ _ _ _ A hBij
  exact ⟨e, he⟩

set_option maxHeartbeats 700000 in
/-- Near a smooth positive solution the Sobolev determinant has a
smooth local inverse with the same zero Dirichlet trace. -/
theorem exists_dirichletSobolevDeterminant_localInverse {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
    {F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k} (hF : ContDiff ℝ ∞ F)
    (hEq : ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
      (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
        =ᵐ[ν[n]] fun x => (complexHessian f x).det.re)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (f : E n → ℝ),
      ContinuousOn f (closedUnitBall n) → f =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = f x)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
    let u₀ := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
    ∃ G : CoordinateSobolev n k → dirichletSobolevJetGraph_zeroTrace T,
      (∀ᶠ y in 𝓝 (F u₀), ContDiffAt ℝ ∞ G y) ∧ (G (F u₀)).val = u₀ ∧
      (∀ᶠ z in 𝓝 (F u₀), F (G z).val = z) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let u₀ := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
  let Z := dirichletSobolevJetGraph_zeroTrace T
  have huZ : u₀ ∈ Z :=
    (mem_dirichletSobolevJetGraph_zeroTrace T u₀).mpr fun x =>
      (hT u₀ u hu.continuous.continuousOn
        (dirichletSobolevJetOfSmooth_fst_ae hn b hu).symm _).trans (hu0 x.val x.property)
  let z₀ : Z := ⟨u₀, huZ⟩
  let H : Z → CoordinateSobolev n k := F ∘ Z.subtypeL
  obtain ⟨e, he⟩ := exists_dirichletSobolevDeterminant_fderiv_equiv hn hk hF hEq T hT
    hu hu0 huP ha hl hDensity hElliptic
  let i : Z →L[ℝ] CoordinateSobolev n (k + 2) := Z.subtypeL
  have hiSmooth : ContDiff ℝ ∞ (i : Z → CoordinateSobolev n (k + 2)) :=
    @ContinuousLinearMap.contDiff ℝ Z (CoordinateSobolev n (k + 2)) _ _ _ _ _ ∞ i
  have hH : ContDiff ℝ ∞ H := hF.comp hiSmooth
  have hD : HasFDerivAt H (e : Z →L[ℝ] CoordinateSobolev n k) z₀ := by
    let L : CoordinateSobolev n (k + 2) →L[ℝ] CoordinateSobolev n k := fderiv ℝ F u₀
    have hF₀ : HasFDerivAt F L u₀ := (hF.differentiable (by simp) u₀).hasFDerivAt
    have h : HasFDerivAt H (L.comp i) z₀ :=
      @hasFDerivAt_comp_clm Z (CoordinateSobolev n (k + 2)) (CoordinateSobolev n k)
        _ _ _ _ _ _ i F z₀ L hF₀
    refine h.congr_fderiv ?_
    ext v : 1
    exact (he v).symm
  have hInv := @exists_smooth_localInverse_on_nhds_of_equiv Z (CoordinateSobolev n k)
    _ _ _ _ _ _ H z₀ hH e hD
  obtain ⟨G, hG, hG₀, hGR⟩ := hInv
  refine ⟨G, hG, ?_, hGR⟩
  exact congrArg (fun z : Z => z.val) hG₀

end KEBall
