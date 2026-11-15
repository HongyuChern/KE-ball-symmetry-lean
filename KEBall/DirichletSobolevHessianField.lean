import KEBall.DirichletPositiveMatrix
import KEBall.DirichletUniformEllipticity

/-! Continuous complex Hessian fields on the closed ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private noncomputable def hessianFromJet {n : ℕ} (D : E n [×2]→L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  (4 : ℂ)⁻¹ *
    ((D ![realDirection i, realDirection j] : ℂ) +
      (D ![imagDirection i, imagDirection j] : ℂ) +
      Complex.I * ((D ![realDirection i, imagDirection j] : ℂ) -
        (D ![imagDirection i, realDirection j] : ℂ)))

private theorem continuous_hessianFromJet {n : ℕ} :
    Continuous (hessianFromJet (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h (v w : E n) : Continuous (fun D : E n [×2]→L[ℝ] ℝ => (D ![v, w] : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_eval_const ![v, w])
  exact (continuous_const (y := (4 : ℂ)⁻¹)).mul
    (((h (realDirection i) (realDirection j)).add (h (imagDirection i) (imagDirection j))).add
      ((continuous_const (y := Complex.I)).mul
        ((h (realDirection i) (imagDirection j)).sub (h (imagDirection i) (realDirection j)))))

private theorem hessianFromJet_eq {n : ℕ} {v : E n → ℝ} {x : E n}
    (hv : ContDiffAt ℝ 2 v x) :
    hessianFromJet (iteratedFDeriv ℝ 2 v x) = complexHessian v x := by
  ext i j
  exact (complexHessian_eq_of_iteratedFDeriv_two hv i j).symm

/-- A continuous representative map for the second derivatives gives a
jointly continuous closed-ball field of complex Hessians. -/
theorem exists_dirichletSobolevHessianField {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k) {r : ℕ} (hr : 2 ≤ r)
    (hkr : r + 2 * (2 * n + 1) ≤ k + 2) :
    ∃ H : CoordinateSobolev n (k + 2) × ClosedBall n → Matrix (Fin n) (Fin n) ℂ,
      Continuous H ∧
      (∀ x : ClosedBall n, ∃ L : CoordinateSobolev n (k + 2) →L[ℝ] Matrix (Fin n) (Fin n) ℂ,
        ∀ z, L z = H (z, x)) ∧
      (∀ (v : E n → ℝ) (hv : ContDiff ℝ ∞ v) (x : ClosedBall n),
        H (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hv, x) =
          complexHessian v x) ∧
      ∀ z : CoordinateSobolev n (k + 2), ∃ v : E n → ℝ,
        ContDiffOn ℝ (r : ℕ∞ω) v (closedUnitBall n) ∧ v =ᵐ[ν[n]] z.val.1 ∧
        (∀ x : ClosedBall n, (H (z, x)).IsHermitian) ∧
        ∀ x : ClosedBall n, x.val ∈ unitBall n → H (z, x) = complexHessian v x := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  obtain ⟨Q, hQ⟩ := exists_dirichletSobolevJetGraph_toContinuousMap hn b hk
  let D (i j : Fin n) := dirichletSobolevComplexHessianEntry (k := k) i j
  let X := CoordinateSobolev n (k + 2) × ClosedBall n
  let H (p : X) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    (Q (D i j p.1).1 p.2 : ℂ) + Complex.I * (Q (D i j p.1).2 p.2 : ℂ)
  have hH : Continuous H := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hEval (L : X → C(ClosedBall n, ℝ)) (hL : Continuous L) :
        Continuous (fun p : X => L p p.2) :=
      continuous_eval.comp (hL.prodMk continuous_snd)
    have h1 := hEval _ (Q.continuous.comp (((D i j).continuous.comp continuous_fst).fst))
    have h2 := hEval _ (Q.continuous.comp (((D i j).continuous.comp continuous_fst).snd))
    exact (Complex.continuous_ofReal.comp h1).add
      (continuous_const.mul (Complex.continuous_ofReal.comp h2))
  have hLinear (x : ClosedBall n) : ∃ L : CoordinateSobolev n (k + 2) →L[ℝ]
      Matrix (Fin n) (Fin n) ℂ, ∀ z, L z = H (z, x) := by
    let ev : C(ClosedBall n, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ x
    let R (i j : Fin n) : CoordinateSobolev n (k + 2) →L[ℝ] ℝ :=
      ev.comp (Q.comp ((ContinuousLinearMap.fst ℝ _ _).comp (D i j)))
    let I (i j : Fin n) : CoordinateSobolev n (k + 2) →L[ℝ] ℝ :=
      ev.comp (Q.comp ((ContinuousLinearMap.snd ℝ _ _).comp (D i j)))
    refine ⟨ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
      Complex.ofRealCLM.comp (R i j) + Complex.I • Complex.ofRealCLM.comp (I i j))), ?_⟩
    intro z
    ext i j
    rfl
  have hSmooth (v : E n → ℝ) (hv : ContDiff ℝ ∞ v) (x : ClosedBall n) :
      H (dirichletSobolevJetOfSmooth hn b hv, x) = complexHessian v x := by
    let z : CoordinateSobolev n (k + 2) := dirichletSobolevJetOfSmooth hn b hv
    ext i j
    have hC : ContinuousOn (fun y => complexHessian v y i j) (closedUnitBall n) :=
      ((complexHessian_contDiffOn isOpen_univ hv.contDiffOn i j).continuousOn).mono (subset_univ _)
    have he := dirichletSobolevComplexHessianEntry_ofSmooth_ae (k := k) hn i j hv
    have heR : (fun y => (complexHessian v y i j).re) =ᵐ[ν[n]] (D i j z).1.val.1 := by
      filter_upwards [he] with y hy
      have h := congrArg Complex.re hy
      simpa [D, z, Complex.mul_re] using h.symm
    have heI : (fun y => (complexHessian v y i j).im) =ᵐ[ν[n]] (D i j z).2.val.1 := by
      filter_upwards [he] with y hy
      have h := congrArg Complex.im hy
      simpa [D, z, Complex.mul_im] using h.symm
    change (Q (D i j z).1 x : ℂ) + Complex.I * (Q (D i j z).2 x : ℂ) = _
    rw [hQ _ _ (Complex.continuous_re.comp_continuousOn hC) heR x,
      hQ _ _ (Complex.continuous_im.comp_continuousOn hC) heI x]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  refine ⟨H, hH, hLinear, hSmooth, fun z => ?_⟩
  have hReg := hasDirichletWeakDerivativesL2_of_jetGraph hn b z
  have hReg' : HasDirichletWeakDerivativesL2 (z.val.1 : E n → ℝ) (r + 2 * (2 * n + 1)) :=
    hReg.of_le hkr
  obtain ⟨v, P, hP, he, hLim⟩ := hReg'.exists_closedUnitBall_finiteJet hn
  let g := dirichletSmoothApproximation (z.val.1 : E n → ℝ)
  have hg (j : ℕ) : ContDiff ℝ ∞ (g j) := contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j
  let w (j : ℕ) : CoordinateSobolev n (k + 2) := dirichletSobolevJetOfSmooth hn b (hg j)
  have hW : Tendsto w atTop (𝓝 z) := tendsto_dirichletSobolevJetOfSmoothApproximation hn b z
  have hTwo : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hLimH (x : ClosedBall n) :
      Tendsto (fun j => complexHessian (g j) x) atTop (𝓝 (H (z, x))) := by
    have h := (hH.tendsto (z, x)).comp (hW.prodMk_nhds tendsto_const_nhds)
    exact h.congr (fun j => hSmooth (g j) (hg j) x)
  have hHP (x : ClosedBall n) : H (z, x) = hessianFromJet (P x 2) := by
    have h := (continuous_hessianFromJet.tendsto (P x 2)).comp ((hLim 2 hr).tendsto_at x.property)
    exact tendsto_nhds_unique (hLimH x) (h.congr fun j =>
      hessianFromJet_eq ((hg j).contDiffAt.of_le hTwo))
  refine ⟨v, hP.contDiffOn, he, ?_, ?_⟩
  · intro x
    ext i j
    change star (H (z, x) j i) = H (z, x) i j
    have hEntry (i j : Fin n) : Tendsto (fun l => complexHessian (g l) x i j)
        atTop (𝓝 (H (z, x) i j)) :=
      (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp (hLimH x)) i)) j
    apply tendsto_nhds_unique ((continuous_star.tendsto _).comp (hEntry j i))
    exact (hEntry i j).congr fun l => by
      have h := MoserTrudinger.complexHessian_isHermitian_of_smooth ((hg l).contDiffAt (x := x.val))
      exact (congrFun (congrFun h.eq i) j).symm
  · intro x hx
    have hP' := hP.mono ball_subset_closedBall
    have hr' : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
    have hP2 : P x 2 = iteratedFDeriv ℝ 2 v x := by
      rw [hP'.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := 2) hr'
        isOpen_ball.uniqueDiffOn hx, iteratedFDerivWithin_of_isOpen _ isOpen_ball hx]
    rw [hHP, hP2]
    exact hessianFromJet_eq ((hP'.contDiffOn.contDiffAt (isOpen_ball.mem_nhds hx)).of_le hr')

private theorem exists_hermitian_posDef_open_set (n : ℕ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧
      (∀ A, A.PosDef → A ∈ U) ∧ ∀ A ∈ U, A.IsHermitian → A.PosDef := by
  let S : Set (Set (Matrix (Fin n) (Fin n) ℂ)) :=
    {V | IsOpen V ∧ ∀ A ∈ V, A.IsHermitian → A.PosDef}
  refine ⟨⋃₀ S, isOpen_sUnion (fun V hV => hV.1), ?_, ?_⟩
  · intro A hA
    obtain ⟨V, hV, hAV, h⟩ := exists_isOpen_hermitian_posDef_nhds hA
    exact mem_sUnion.mpr ⟨V, ⟨hV, h⟩, hAV⟩
  · intro A hA hH
    obtain ⟨V, hV, hAV⟩ := mem_sUnion.mp hA
    exact hV.2 A hAV hH

set_option maxHeartbeats 450000 in
/-- Close to the determinant of a smooth elliptic background, every
Sobolev density with a continuous representative has a strictly
plurisubharmonic classical C^r zero-boundary solution. -/
theorem exists_smooth_closedBall_posDef_dirichlet_det_localInverse {n k r : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k) (hr : 2 ≤ r)
    (hkr : r + 2 * (2 * n + 1) ≤ k + 2)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∃ (d : CoordinateSobolev n k) (G : CoordinateSobolev n k → CoordinateSobolev n (k + 2))
        (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ)),
      (∀ᶠ q in 𝓝 d, ContDiffAt ℝ ∞ G q) ∧
      (∀ (z : CoordinateSobolev n (k + 2)) (v : E n → ℝ),
        ContinuousOn v (closedUnitBall n) → v =ᵐ[ν[n]] z.val.1 →
          ∀ x : ClosedBall n, T z x = v x) ∧
      (d.val.1 =ᵐ[ν[n]] fun x => (complexHessian u x).det.re) ∧
      ∀ᶠ q in 𝓝 d, ∀ f : E n → ℝ, ContinuousOn f (unitBall n) → f =ᵐ[ν[n]] q.val.1 →
        ∃ v : E n → ℝ, ContDiffOn ℝ (r : ℕ∞ω) v (closedUnitBall n) ∧
          (∀ x ∈ unitSphere n, v x = 0) ∧
          (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
          EqOn (fun x => (complexHessian v x).det.re) f (unitBall n) ∧
          v =ᵐ[ν[n]] (G q).val.1 := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let u₀ := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
  obtain ⟨F, hF, hEq⟩ := exists_contDiff_dirichletSobolevDeterminant hn hk
  obtain ⟨T, hT⟩ := exists_dirichletSobolevJetGraph_toContinuousMap hn b
    (hk.trans (Nat.le_add_right k 2))
  obtain ⟨G, hG, hG0, hGR⟩ := exists_dirichletSobolevDeterminant_localInverse hn hk hF hEq T hT
    hu hu0 huP ha hl hDensity hElliptic
  obtain ⟨H, hH, _, hHSmooth, hRep⟩ := exists_dirichletSobolevHessianField (k := k) hn hk hr hkr
  obtain ⟨O, hO, hOP, hPO⟩ := exists_hermitian_posDef_open_set n
  have huN : SmoothNear (closedUnitBall n) u := ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  have hDetN : SmoothNear (closedUnitBall n) (fun x => (complexHessian u x).det.re) :=
    ⟨univ, isOpen_univ, subset_univ _, Complex.reCLM.contDiff.contDiffOn.comp
      (matrixField_det_contDiffOn (complexHessian_contDiffOn isOpen_univ hu.contDiffOn))
      (mapsTo_univ _ _)⟩
  let c := min a 1
  have hc : 0 < c := lt_min ha zero_lt_one
  have hcn : c ^ n ≤ c := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_self_of_le_one hc.le (min_le_right _ _) (by exact_mod_cast hn)
  have hBase (x : ClosedBall n) : (H (u₀, x)).PosDef := by
    rw [hHSmooth u hu x]
    exact dirichlet_posDef_on_closedBall huN hDetN huP (fun _ _ => rfl) hc
      (fun y hy => hcn.trans ((min_le_left _ _).trans (hDensity y hy))) x.property
  have hTube : ({u₀} : Set (CoordinateSobolev n (k + 2))) ×ˢ (univ : Set (ClosedBall n)) ⊆ H ⁻¹' O := by
    rintro ⟨z, x⟩ ⟨hz, _⟩
    have he : z = u₀ := hz
    subst z
    exact hOP _ (hBase x)
  obtain ⟨U, V, hU, _, hU0, hV, hUV⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_univ (hO.preimage hH) hTube
  have hG' : Tendsto (fun q => (G q).val) (𝓝 (F u₀)) (𝓝 u₀) := by
    have h := continuous_subtype_val.continuousAt.tendsto.comp hG.self_of_nhds.continuousAt.tendsto
    rwa [hG0] at h
  have hGU : ∀ᶠ q in 𝓝 (F u₀), (G q).val ∈ U :=
    hG'.eventually (hU.mem_nhds (hU0 (mem_singleton u₀)))
  let Z := dirichletSobolevJetGraph_zeroTrace T
  let i : Z →L[ℝ] CoordinateSobolev n (k + 2) := Z.subtypeL
  have hI : ContDiff ℝ ∞ (i : Z → CoordinateSobolev n (k + 2)) :=
    @ContinuousLinearMap.contDiff ℝ Z (CoordinateSobolev n (k + 2)) _ _ _ _ _ ∞ i
  refine ⟨F u₀, i ∘ G, T, hG.mono (fun q hq => hI.contDiffAt.comp q hq), hT, hEq u hu, ?_⟩
  filter_upwards [hGR, hGU] with q hq hQU f hf hFq
  obtain ⟨v, hv, he, hDet⟩ := exists_contDiffOn_closedBall_rep_det_eq_ae hn hk hF.continuous hEq (G q).val
  obtain ⟨w, hw, hW, hHerm, hClassical⟩ := hRep (G q).val
  have hvw : EqOn v w (unitBall n) := by
    have hHaar : (volume0 n).IsAddHaarMeasure := by
      unfold volume0
      exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
    exact (volume0 n).eqOn_open_of_ae_eq (he.trans hW.symm) isOpen_ball
      (hv.continuousOn.mono ball_subset_closedBall) (hw.continuousOn.mono ball_subset_closedBall)
  refine ⟨w, hw, ?_, ?_, ?_, hW⟩
  · intro x hx
    let X : ClosedBall n := ⟨x, sphere_subset_closedBall hx⟩
    exact (hT (G q).val w hw.continuousOn hW X).symm.trans
      ((mem_dirichletSobolevJetGraph_zeroTrace T (G q).val).mp (G q).property ⟨x, hx⟩)
  · intro x hx
    let X : ClosedBall n := ⟨x, ball_subset_closedBall hx⟩
    rw [← hClassical X hx]
    exact hPO _ (hUV ⟨hQU, hV (mem_univ X)⟩) (hHerm X)
  · rw [hq] at hDet
    have hHaar : (volume0 n).IsAddHaarMeasure := by
      unfold volume0
      exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
    have hEqV := (volume0 n).eqOn_open_of_ae_eq (hDet.symm.trans hFq.symm) isOpen_ball
      (continuousOn_det_complexHessian_C2 (hv.mono ball_subset_closedBall)) hf
    intro x hx
    have hNear : v =ᶠ[𝓝 x] w :=
      Filter.Eventually.mono (isOpen_ball.mem_nhds hx) fun y hy => hvw hy
    change (complexHessian w x).det.re = f x
    rw [← complexHessian_congr_of_eventuallyEq hNear]
    exact hEqV hx

/-- Positive finite-regularity classical solutions for densities near the
determinant of a smooth uniformly elliptic Dirichlet solution. -/
theorem eventually_exists_closedBall_posDef_dirichlet_det {n k r : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k) (hr : 2 ≤ r)
    (hkr : r + 2 * (2 * n + 1) ≤ k + 2)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∃ d : CoordinateSobolev n k,
      (d.val.1 =ᵐ[ν[n]] fun x => (complexHessian u x).det.re) ∧
      ∀ᶠ q in 𝓝 d, ∀ f : E n → ℝ, ContinuousOn f (unitBall n) → f =ᵐ[ν[n]] q.val.1 →
        ∃ v : E n → ℝ, ContDiffOn ℝ (r : ℕ∞ω) v (closedUnitBall n) ∧
          (∀ x ∈ unitSphere n, v x = 0) ∧
          (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
          EqOn (fun x => (complexHessian v x).det.re) f (unitBall n) := by
  obtain ⟨d, _, _, _, _, hd, h⟩ := exists_smooth_closedBall_posDef_dirichlet_det_localInverse hn hk hr hkr
    hu hu0 huP ha hl hDensity hElliptic
  refine ⟨d, hd, ?_⟩
  filter_upwards [h] with q hq f hf hFq
  obtain ⟨v, hv, hv0, hvP, hvEq, _⟩ := hq f hf hFq
  exact ⟨v, hv, hv0, hvP, hvEq⟩

end KEBall
