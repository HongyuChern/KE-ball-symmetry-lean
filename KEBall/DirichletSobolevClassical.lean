import KEBall.DirichletSobolevDeterminantDerivative

/-! The actual complex Hessian for finite-order classical representatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology
open KEBallProbe

namespace KEBall

private theorem rd_rd_ofReal_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (a b : E n) :
    rd a (rd b (fun y => (u y : ℂ))) x = (realHessian u x a b : ℝ) := by
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y := by
    filter_upwards [(hu.of_le (m := 1) (by norm_num)).eventually (by simp)] with y hy
    exact hy.differentiableAt one_ne_zero
  have heq : rd b (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u y b : ℂ)) := by
    filter_upwards [hnear] with y hy
    exact rd_ofReal hy b
  change fderiv ℝ (rd b (fun y => (u y : ℂ))) x a = _
  rw [heq.fderiv_eq]
  have hdf := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hr := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  change HasFDerivAt (fun y => (fderiv ℝ u y b : ℂ)) _ x at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, zero_apply, map_zero,
    zero_add, Complex.ofRealCLM_apply]
  rfl

private theorem rd_dz_at_C2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v a b : E) :
    rd v (dz a b f) x = (2 : ℂ)⁻¹ * (rd v (rd a f) x - Complex.I * rd v (rd b f) x) := by
  have hd (w : E) : DifferentiableAt ℝ (rd w f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt one_ne_zero
  let g (y : E) := rd a f y - Complex.I * rd b f y
  have hg := (hd a).hasFDerivAt.sub ((hd b).hasFDerivAt.const_mul Complex.I)
  have h : HasFDerivAt g _ x := hg
  have h' := h.const_mul ((2 : ℂ)⁻¹)
  change (fderiv ℝ (fun y => (2 : ℂ)⁻¹ * g y) x) v = _
  rw [h'.fderiv]
  simp only [FunLike.coe_smul, sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem complexHessian_real_entry_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    complexHessian u x i j = (4 : ℂ)⁻¹ *
      ((realHessian u x (realDirection i) (realDirection j) : ℝ) +
       (realHessian u x (imagDirection i) (imagDirection j) : ℝ) +
       Complex.I * ((realHessian u x (realDirection i) (imagDirection j) : ℝ) -
         (realHessian u x (imagDirection i) (realDirection j) : ℝ))) := by
  have hc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (-imagDirection j) (fun y => (u y : ℂ))) x = _
  rw [dz, rd_dz_at_C2 hc, rd_dz_at_C2 hc]
  simp only [rd_rd_ofReal_C2 hu, map_neg]
  push_cast
  ring_nf
  simp
  ring

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

theorem complexHessian_eq_of_iteratedFDeriv_two {n : ℕ} {u : E n → ℝ}
    {x : E n} (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    complexHessian u x i j = (4 : ℂ)⁻¹ *
      ((iteratedFDeriv ℝ 2 u x ![realDirection i, realDirection j] : ℝ) +
       (iteratedFDeriv ℝ 2 u x ![imagDirection i, imagDirection j] : ℝ) +
       Complex.I * ((iteratedFDeriv ℝ 2 u x ![realDirection i, imagDirection j] : ℝ) -
         (iteratedFDeriv ℝ 2 u x ![imagDirection i, realDirection j] : ℝ))) := by
  rw [complexHessian_real_entry_C2 hu]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, realHessian]

/-- The Sobolev determinant agrees with the actual pointwise determinant
of the C² representative on the open ball. -/
theorem exists_contDiffOn_closedBall_rep_det_eq_ae {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
    {F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k}
    (hF : Continuous F)
    (hEq : ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
      (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
        =ᵐ[ν[n]] fun x => (complexHessian f x).det.re)
    (z : CoordinateSobolev n (k + 2)) :
    ∃ f : E n → ℝ, ContDiffOn ℝ 2 f (closedUnitBall n) ∧ f =ᵐ[ν[n]] z.val.1 ∧
      (F z).val.1 =ᵐ[ν[n]] fun x => (complexHessian f x).det.re := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have hReg := hasDirichletWeakDerivativesL2_of_jetGraph hn b z
  have hReg' : HasDirichletWeakDerivativesL2 (z.val.1 : E n → ℝ) (2 + 2 * (2 * n + 1)) :=
    hReg.of_le (by omega)
  obtain ⟨f, P, hP, he, hLim⟩ := hReg'.exists_closedUnitBall_finiteJet hn
  have hf : ContDiffOn ℝ 2 f (closedUnitBall n) := hP.contDiffOn
  refine ⟨f, hf, he, ?_⟩
  let g := dirichletSmoothApproximation (z.val.1 : E n → ℝ)
  have hg (j : ℕ) : ContDiff ℝ ∞ (g j) := contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j
  let w (j : ℕ) : CoordinateSobolev n (k + 2) := dirichletSobolevJetOfSmooth hn b (hg j)
  have hW : Tendsto w atTop (𝓝 z) := tendsto_dirichletSobolevJetOfSmoothApproximation hn b z
  have hFW : Tendsto (fun j => (F (w j)).val.1) atTop (𝓝 (F z).val.1) :=
    ((continuous_fst.comp continuous_subtype_val).comp hF).continuousAt.tendsto.comp hW
  obtain ⟨φ, hφ, hAe⟩ := (tendstoInMeasure_of_tendsto_Lp hFW).exists_seq_tendsto_ae
  have hApproxEq : ∀ᵐ x ∂ν[n], ∀ j, (F (w j)).val.1 x = (complexHessian (g j) x).det.re :=
    ae_all_iff.mpr fun j => hEq _ (hg j)
  filter_upwards [hAe, hApproxEq, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hE hB
  have hxC := ball_subset_closedBall hB
  have hxD : ContDiffAt ℝ 2 f x :=
    (hf.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hB)
  have hP2 : P x 2 = iteratedFDeriv ℝ 2 f x := by
    have hP' := hP.mono ball_subset_closedBall
    rw [hP'.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := 2) (by norm_num)
      isOpen_ball.uniqueDiffOn hB, iteratedFDerivWithin_of_isOpen _ isOpen_ball hB]
  have hDeriv (a b : E n) :
      Tendsto (fun j => iteratedFDeriv ℝ 2 (g j) x ![a, b]) atTop
        (𝓝 (iteratedFDeriv ℝ 2 f x ![a, b])) := by
    have h := ((continuous_eval_const ![a, b]).tendsto (P x 2)).comp ((hLim 2 le_rfl).tendsto_at hxC)
    rw [hP2] at h
    exact h
  have hH : Tendsto (fun j => complexHessian (g j) x) atTop (𝓝 (complexHessian f x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
    have heq (l : ℕ) := complexHessian_eq_of_iteratedFDeriv_two ((hg l).contDiffAt (x := x) |>.of_le h2) i j
    simp only [complexHessian_eq_of_iteratedFDeriv_two hxD i j, heq]
    have hC (a b : E n) :
        Tendsto (fun j => (iteratedFDeriv ℝ 2 (g j) x ![a, b] : ℂ)) atTop
          (𝓝 (iteratedFDeriv ℝ 2 f x ![a, b] : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hDeriv a b)
    exact ((((hC _ _).add (hC _ _)).add (((hC _ _).sub (hC _ _)).const_mul Complex.I)).const_mul _)
  have hDet := ((Complex.continuous_re.comp continuous_id.matrix_det).tendsto (complexHessian f x)).comp
    (hH.comp hφ.tendsto_atTop)
  exact tendsto_nhds_unique hx (hDet.congr (fun j => (hE (φ j)).symm))

theorem continuousOn_det_complexHessian_C2 {n : ℕ} {v : E n → ℝ}
    (hv : ContDiffOn ℝ 2 v (unitBall n)) :
    ContinuousOn (fun x => (complexHessian v x).det.re) (unitBall n) := by
  have hD : ContinuousOn (iteratedFDeriv ℝ 2 v) (unitBall n) := by
    have h := hv.continuousOn_iteratedFDerivWithin (m := 2) le_rfl isOpen_ball.uniqueDiffOn
    exact h.congr fun x hx => (iteratedFDerivWithin_of_isOpen _ isOpen_ball hx).symm
  have hH : ContinuousOn (complexHessian v) (unitBall n) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    have h (a b : E n) : ContinuousOn (fun x => (iteratedFDeriv ℝ 2 v x ![a, b] : ℂ)) (unitBall n) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((continuous_eval_const _).comp_continuousOn hD)
    refine ((continuousOn_const (c := (4 : ℂ)⁻¹)).mul
      (((h (realDirection i) (realDirection j)).add (h (imagDirection i) (imagDirection j))).add
        ((continuousOn_const (c := Complex.I)).mul
          ((h (realDirection i) (imagDirection j)).sub (h (imagDirection i) (realDirection j)))))).congr ?_
    intro x hx
    exact complexHessian_eq_of_iteratedFDeriv_two (hv.contDiffAt (isOpen_ball.mem_nhds hx)) i j
  exact (Complex.continuous_re.comp continuous_id.matrix_det).comp_continuousOn hH

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

/-- Close to the determinant of a smooth background, every Sobolev density
with a continuous representative has a classical C² zero-boundary solution. -/
theorem eventually_exists_closedBall_C2_dirichlet_det {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
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
        ∃ v : E n → ℝ, ContDiffOn ℝ 2 v (closedUnitBall n) ∧
          (∀ x ∈ unitSphere n, v x = 0) ∧
          EqOn (fun x => (complexHessian v x).det.re) f (unitBall n) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let u₀ := dirichletSobolevJetOfSmooth (k := k + 2) hn b hu
  obtain ⟨F, hF, hEq⟩ := exists_contDiff_dirichletSobolevDeterminant hn hk
  obtain ⟨T, hT⟩ := exists_dirichletSobolevJetGraph_toContinuousMap hn b
    (hk.trans (Nat.le_add_right k 2))
  obtain ⟨G, _, _, hGR⟩ := exists_dirichletSobolevDeterminant_localInverse hn hk hF hEq T hT
    hu hu0 huP ha hl hDensity hElliptic
  refine ⟨F u₀, hEq u hu, ?_⟩
  filter_upwards [hGR] with q hq f hf hFq
  obtain ⟨v, hv, he, hDet⟩ := exists_contDiffOn_closedBall_rep_det_eq_ae hn hk hF.continuous hEq (G q).val
  refine ⟨v, hv, ?_, ?_⟩
  · intro x hx
    let X : ClosedBall n := ⟨x, sphere_subset_closedBall hx⟩
    exact (hT (G q).val v hv.continuousOn he X).symm.trans
      ((mem_dirichletSobolevJetGraph_zeroTrace T (G q).val).mp (G q).property ⟨x, hx⟩)
  · rw [hq] at hDet
    have hHaar : (volume0 n).IsAddHaarMeasure := by
      unfold volume0
      exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
    exact (volume0 n).eqOn_open_of_ae_eq (hDet.symm.trans hFq.symm) isOpen_ball
      (continuousOn_det_complexHessian_C2 (hv.mono ball_subset_closedBall)) hf

end KEBall
