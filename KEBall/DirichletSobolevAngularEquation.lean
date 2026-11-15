import KEBall.DirichletLinearNormalRecovery

/-! The angular derivative satisfies the linearized Monge–Ampère
equation, obtained by differentiating the orbit in the Sobolev space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise Topology

namespace KEBall

open KEBallProbe

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

private theorem hasDerivAt_det_re_curve {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {D : Matrix (Fin n) (Fin n) ℂ} (hA : HasDerivAt A D 0) :
    HasDerivAt (fun t => (A t).det.re) (((A 0).adjugate * D).trace.re) 0 := by
  have hF : HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (fderiv ℝ Matrix.det (A 0)) (A 0) := (complex_det_differentiableAt (A 0)).hasFDerivAt
  have hD := hF.comp_hasDerivAt (0 : ℝ) hA
  rw [fderiv_real_complex_det] at hD
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD

/-- Pointwise evaluation of the Sobolev Hessian agrees with the
classical Hessian of any continuous representative in the interior. -/
theorem exists_sobolev_complexHessian_eval {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {x : E n} (hx : x ∈ unitBall n) :
    ∃ L : CoordinateSobolev n (k + 2) →L[ℝ] Matrix (Fin n) (Fin n) ℂ,
      ∀ (z : CoordinateSobolev n (k + 2)) {u : E n → ℝ},
        ContinuousOn u (closedUnitBall n) → (∀ y : ClosedBall n, T z y = u y) →
          L z = complexHessian u x := by
  obtain ⟨H, _, hL, _, hRep⟩ := exists_dirichletSobolevHessianField hn hk (r := 2)
    le_rfl (by omega)
  have hH (z : CoordinateSobolev n (k + 2)) {u : E n → ℝ}
      (hu : ContinuousOn u (closedUnitBall n)) (he : ∀ x : ClosedBall n, T z x = u x)
      (x : ClosedBall n) (hx : x.val ∈ unitBall n) : H (z, x) = complexHessian u x.val := by
    obtain ⟨w, hw, hwZ, _, hwH⟩ := hRep z
    rw [hwH x hx]
    apply complexHessian_congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    let Y : ClosedBall n := ⟨y, ball_subset_closedBall hy⟩
    exact (hT z w hw.continuousOn hwZ Y).symm.trans (he Y)
  let X : ClosedBall n := ⟨x, ball_subset_closedBall hx⟩
  obtain ⟨L, hLX⟩ := hL X
  exact ⟨L, fun z u hu he => (hLX z).trans (hH z hu he X hx)⟩

/-- A derivative of a rotated density equals the cofactor operator
applied to the first angular derivative of the potential. -/
theorem complexHessian_angularDerivative_eq_linearized_det_of_sobolev_orbit {n k : ℕ}
    (hn : 0 < n) (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v f : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hf : ContDiffOn ℝ 1 f (closedUnitBall n))
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (R : E n →L[ℝ] E n) (hR : star R = -R) (hRJ : ∀ x, R (J x) = J (R x))
    {W : ℝ → CoordinateSobolev n (k + 2)}
    (hW : DifferentiableAt ℝ W 0)
    (hOrbit : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x : ClosedBall n, T (W t) x = v (orthogonalFlow R hR t x)) :
    ∀ x ∈ unitBall n, ((complexHessian v x).adjugate *
      complexHessian (dirichletAngularDerivative R v) x).trace.re =
        dirichletAngularDerivative R f x := by
  have hDW : HasDerivAt W (deriv W 0) 0 := hW.hasDerivAt
  have hD := eqOn_angularDerivative_of_eq_rotated_curve (hv.of_le (by norm_num)) R hR
    (T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hDW) hOrbit
  have hDv : ContinuousOn (dirichletAngularDerivative R v) (closedUnitBall n) := by
    have hS : UniqueDiffOn ℝ (closedUnitBall n) :=
      uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
        rw [closedUnitBall, interior_closedBall _ (by norm_num)]
        exact nonempty_ball.mpr (by norm_num))
    exact ((hv.fderivWithin (m := 1) hS (by norm_num)).clm_apply R.contDiff.contDiffOn).continuousOn
  intro x hx
  let X : ClosedBall n := ⟨x, ball_subset_closedBall hx⟩
  obtain ⟨L, hL⟩ := exists_sobolev_complexHessian_eval hn hk T hT hx
  have hLD : L (deriv W 0) = complexHessian (dirichletAngularDerivative R v) x :=
    hL _ hDv hD
  have hL0 : L (W 0) = complexHessian v x := by
    refine hL _ hv.continuousOn ?_
    intro y
    rw [hOrbit.self_of_nhds y, orthogonalFlow_zero_apply]
  have hLC : HasDerivAt (L ∘ W) (L (deriv W 0)) 0 :=
    (L.hasFDerivAt (x := W 0)).comp_hasDerivAt (0 : ℝ) hDW
  have hDet := hasDerivAt_det_re_curve hLC
  have hY (t : ℝ) : orthogonalFlow R hR t x ∈ unitBall n := by
    simpa only [unitBall, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hF : HasDerivAt (f ∘ fun t => orthogonalFlow R hR t x)
      (dirichletAngularDerivative R f x) 0 :=
    HasFDerivWithinAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
      ((hf.differentiableOn one_ne_zero x X.property).hasFDerivWithinAt)
      (hasDerivAt_orthogonalFlow_apply_zero R hR x)
      (Eventually.of_forall fun t => ball_subset_closedBall (hY t))
      (orthogonalFlow_zero_apply R hR x).symm
  have he : (fun t => (L (W t)).det.re) =ᶠ[𝓝 (0 : ℝ)]
      (f ∘ fun t => orthogonalFlow R hR t x) := by
    filter_upwards [hOrbit] with t ht
    let Q := orthogonalFlow R hR t
    have hQ : ContinuousOn (v ∘ Q) (closedUnitBall n) :=
      hv.continuousOn.comp Q.continuous.continuousOn (orthogonalFlow_mapsTo_closedUnitBall R hR t)
    change (L (W t)).det.re = f (Q x)
    rw [hL _ hQ ht]
    have hCov := (complexHessian_posDef_and_det_comp_unitary Q (orthogonalFlow_apply_J R hR hRJ t)
      ((hv.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds (hY t)))).2
    rw [hCov]
    exact hEq (hY t)
  rw [show (L ∘ W) 0 = L (W 0) from rfl, hL0, hLD] at hDet
  exact hDet.deriv.symm.trans (he.deriv_eq.trans hF.deriv)

/-- The cofactor equation for an angular derivative extends to the
whole closed ball when both potentials have continuous within Hessians. -/
theorem closedBall_withinHessian_angularDerivative_eq_linearized_det_of_sobolev_orbit {n k : ℕ}
    (hn : 0 < n) (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v f : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hf : ContDiffOn ℝ 1 f (closedUnitBall n))
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (R : E n →L[ℝ] E n) (hR : star R = -R) (hRJ : ∀ x, R (J x) = J (R x))
    (hvR : ContDiffOn ℝ 2 (dirichletAngularDerivative R v) (closedUnitBall n))
    {W : ℝ → CoordinateSobolev n (k + 2)}
    (hW : DifferentiableAt ℝ W 0)
    (hOrbit : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x : ClosedBall n, T (W t) x = v (orthogonalFlow R hR t x)) :
    let S := closedUnitBall n
    let A (u : E n → ℝ) (x : E n) := complexHessianOfRealBilinear (fderivWithin ℝ (fderivWithin ℝ u S) S x)
    ∀ x ∈ S, ((A v x).adjugate * A (dirichletAngularDerivative R v) x).trace.re =
      dirichletAngularDerivative R f x := by
  let S := closedUnitBall n
  let A (u : E n → ℝ) (x : E n) := complexHessianOfRealBilinear (fderivWithin ℝ (fderivWithin ℝ u S) S x)
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
    change (interior (closedBall (0 : E n) 1)).Nonempty
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num))
  have hA {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u S) (i j : Fin n) :
      ContDiffOn ℝ 0 (fun x => A u x i j) S :=
    contDiffOn_complexHessianOfRealBilinear
      ((hu.fderivWithin (m := 1) hS (by norm_num)).fderivWithin hS (by norm_num)) i j
  have hLeft : ContinuousOn (fun x => ((A v x).adjugate * A (dirichletAngularDerivative R v) x).trace.re) S := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((contDiffOn_adjugate_of_contDiffOn_entries (hA hv) i j).continuousOn).mul
        (hA hvR j i).continuousOn
  have hRight : ContinuousOn (dirichletAngularDerivative R f) S :=
    ((hf.fderivWithin (m := 0) hS (by norm_num)).clm_apply R.contDiff.contDiffOn).continuousOn
  have hCl : closure (unitBall n) = S := closure_ball (0 : E n) (by norm_num)
  refine EqOn.of_subset_closure ?_ hLeft hRight ball_subset_closedBall hCl.ge
  intro x hx
  have hInterior {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u S) : A u x = complexHessian u x := by
    dsimp only [A]
    have hN : S ∈ 𝓝 x := mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
    rw [fderivWithin_fderivWithin_eq_of_mem_nhds hN]
    exact complexHessianOfRealBilinear_eq
      ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx))
  change ((A v x).adjugate * A (dirichletAngularDerivative R v) x).trace.re =
    dirichletAngularDerivative R f x
  rw [hInterior hv, hInterior hvR]
  exact complexHessian_angularDerivative_eq_linearized_det_of_sobolev_orbit
    hn hk T hT hv hf hEq R hR hRJ hW hOrbit x hx

/-- Second angular derivatives of a positive Dirichlet solution give
C⁵ regularity on a closed-ball annulus through the cofactor equation. -/
theorem contDiffOn_closedBall_inter_five_of_smooth_localInverse {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k) (hkr : 3 + 2 * (2 * n + 1) ≤ k + 2)
    {U : Set (E n)} (hU : IsOpen U) (hAway : (0 : E n) ∉ U)
    {G : dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun _ ℝ) →
      dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ)}
    (T : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ))
      (w : E n → ℝ), ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = w x)
    {d : dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun _ ℝ)}
    (hG : ∀ᶠ q in 𝓝 d, ContDiffAt ℝ ∞ G q)
    (hSol : ∀ᶠ q in 𝓝 d, ∀ f : E n → ℝ, ContinuousOn f (unitBall n) → f =ᵐ[ν[n]] q.val.1 →
      ∃ w : E n → ℝ, ContDiffOn ℝ 2 w (closedUnitBall n) ∧
        (∀ x ∈ unitSphere n, w x = 0) ∧ (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
        EqOn (fun x => (complexHessian w x).det.re) f (unitBall n) ∧
        w =ᵐ[ν[n]] (G q).val.1)
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hv : ContDiffOn ℝ 3 v (closedUnitBall n))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f)
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x) :
    ContDiffOn ℝ 5 v (closedUnitBall n ∩ U) := by
  let S := closedUnitBall n
  let A (w : E n → ℝ) (x : E n) := complexHessianOfRealBilinear
    (fderivWithin ℝ (fderivWithin ℝ w S) S x)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have hv₂ : ContDiffOn ℝ 2 v S := hv.of_le (by norm_num)
  have hf₃ : ContDiffOn ℝ 3 f S :=
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffOn
  have hA := closedBall_withinHessian_posDef_and_det_of_C2 hv₂ hf.continuous.continuousOn hfPos hvP hvEq
  have hv₄ : ContDiffOn ℝ 4 v (S ∩ U) :=
    contDiffOn_closedBall_inter_four_of_smooth_localInverse hn hkr hU hAway T hT hG hSol
      hf hv hv0 hvP hvEq hd hfPos
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
    change (interior (closedBall (0 : E n) 1)).Nonempty
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num))
  have hT' : UniqueDiffOn ℝ (S ∩ U) := hS.inter hU
  have hCoeff (i j : Fin n) : ContDiffOn ℝ 2 (fun x => A v x i j) (S ∩ U) := by
    have hB := ((hv₄.fderivWithin (m := 3) hT' (by norm_num)).fderivWithin (m := 2) hT' (by norm_num))
    refine (contDiffOn_complexHessianOfRealBilinear hB i j).congr fun x hx => ?_
    have hN : S ∩ U ∈ 𝓝[S] x :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.2))
    simp only [A, fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hN
      (hv₂.mono inter_subset_left x hx) hS hT' hx.1]
  have hCentral (x : E n) : JCLM n (J x) = J (JCLM n x) := by simp only [JCLM_apply]
  have hAngle (R : E n →L[ℝ] E n) (hR : star R = -R) (hRJ : ∀ x, R (J x) = J (R x)) :
      ContDiffOn ℝ 4 (dirichletAngularDerivative R v) (S ∩ U) := by
    have hR₃ : ContDiffOn ℝ 3 (dirichletAngularDerivative R v) S :=
      contDiffOn_angularDerivative_of_smooth_localInverse hn hkr T hT hG hSol
        hf hv₂ hv0 hvP hvEq hd R hR hRJ
    have hR₂ : ContDiffOn ℝ 2 (dirichletAngularDerivative R v) S := hR₃.of_le (by norm_num)
    have hF : ContDiffOn ℝ 2 (dirichletAngularDerivative R f) S :=
      (hf₃.fderivWithin hS (by norm_num)).clm_apply R.contDiff.contDiffOn
    obtain ⟨W, hW⟩ := exists_sobolev_unitary_orbit_of_smooth_localInverse hn T hT hG hSol
      hf hv₂ hv0 hvP hvEq hd (orthogonalFlow R hR) 0 (contDiff_orthogonalFlow_apply R hR)
      (orthogonalFlow_zero_apply R hR) (orthogonalFlow_apply_J R hR hRJ)
    have hEqR := closedBall_withinHessian_angularDerivative_eq_linearized_det_of_sobolev_orbit
      hn hk T hT hv₂ (hf₃.of_le (by norm_num)) hvEq R hR hRJ hR₂
      (hW.self_of_nhds.1.differentiableAt (by simp)) (hW.mono fun _ ht => ht.2)
    have hAngle₂ (P : E n →L[ℝ] E n) (hP : star P = -P) (hPJ : ∀ x, P (J x) = J (P x)) :
        ContDiffOn ℝ 3 (dirichletAngularDerivative P (dirichletAngularDerivative R v)) S := by
      have hList : ∀ Q ∈ [P, R], star Q = -Q ∧ ∀ x, Q (J x) = J (Q x) := by
        intro Q hQ
        simp at hQ
        rcases hQ with rfl | rfl
        · exact ⟨hP, hPJ⟩
        · exact ⟨hR, hRJ⟩
      exact contDiffOn_iteratedAngularDerivative_of_smooth_localInverse hn (by norm_num) hkr
        T hT hG hSol hf hv₂ hv0 hvP hvEq hd [P, R] hList
    refine contDiffOn_closedBall_inter_succ_of_angularDerivatives_linearized_det (r := 2)
      hU hAway hR₂ (hR₃.mono inter_subset_left) b ?_ ?_ (hF.mono inter_subset_left)
      hCoeff (fun x hx => (hA x hx.1).1) (fun x hx => hEqR x hx.1)
    · intro i j
      exact (hAngle₂ _ (dirichletUnitaryRotation_star (b i) (b j))
        (dirichletUnitaryRotation_J (b i) (b j))).mono inter_subset_left
    · exact (hAngle₂ _ (JCLM_star n) hCentral).mono inter_subset_left
  refine contDiffOn_closedBall_inter_succ_of_angularDerivatives_det (r := 3) hU hAway hv₂ hv₄ b
    ?_ ?_ (hf₃.mono inter_subset_left) (fun x hx => (hA x hx.1).1) (fun x hx => (hA x hx.1).2)
  · intro i j
    exact hAngle _ (dirichletUnitaryRotation_star (b i) (b j)) (dirichletUnitaryRotation_J (b i) (b j))
  · exact hAngle _ (JCLM_star n) hCentral

end KEBall
