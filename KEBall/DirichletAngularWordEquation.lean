import KEBall.DirichletUnitaryOrbit

/-! The cofactor equation after any finite number of angular derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

open KEBallProbe

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

private theorem contDiff_det_re {n : ℕ} :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.det.re) := by
  rw [← contDiffOn_univ]
  apply Complex.reCLM.contDiff.comp_contDiffOn
  exact contDiffOn_det_of_contDiffOn_entries (A := id) fun i j =>
    (contDiff_pi.mp (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Matrix (Fin n) (Fin n) ℂ)) i) j).contDiffOn

private theorem fderiv_det_re_apply {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (fun C : Matrix (Fin n) (Fin n) ℂ => C.det.re) A B =
      (A.adjugate * B).trace.re := by
  have h := Complex.reCLM.hasFDerivAt.comp A (complex_det_differentiableAt A).hasFDerivAt
  rw [show (fun C : Matrix (Fin n) (Fin n) ℂ => C.det.re) = Complex.reCLM ∘ Matrix.det from rfl,
    h.fderiv, ContinuousLinearMap.comp_apply, fderiv_real_complex_det]
  rfl

/-- The proper-partition terms in the determinant chain rule use only
Hessians of strictly shorter angular words. -/
noncomputable def dirichletAngularDetLowerTerms {n m : ℕ}
    (R : Fin (m + 1) → DirichletUnitaryField n)
    (A : (E n → ℝ) → E n → Matrix (Fin n) (Fin n) ℂ)
    (v : E n → ℝ) (x : E n) : ℝ :=
  ∑ c ∈ Finset.univ.erase (oneBlockPartition m),
    iteratedFDeriv ℝ c.length (fun C : Matrix (Fin n) (Fin n) ℂ => C.det.re) (A v x)
      (fun j => A (dirichletAngularWord (R ∘ c.emb j) v) x)

theorem contDiffOn_dirichletAngularDetLowerTerms {n m : ℕ}
    (R : Fin (m + 1) → DirichletUnitaryField n)
    (A : (E n → ℝ) → E n → Matrix (Fin n) (Fin n) ℂ)
    {v : E n → ℝ} {S : Set (E n)} {r : ℕ∞ω} (hr : r ≤ ∞)
    (hA : ContDiffOn ℝ r (A v) S)
    (hLow : ∀ j ≤ m, ∀ R' : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ r (A (dirichletAngularWord R' v)) S) :
    ContDiffOn ℝ r (dirichletAngularDetLowerTerms R A v) S := by
  exact contDiffOn_iteratedFDeriv_comp_lower_terms contDiff_det_re hr hA
    (fun _ x e => A (dirichletAngularWord (R ∘ e) v) x)
    (fun j hj e => hLow j hj (R ∘ e)) id

/-- Any positive-order angular derivative of a Sobolev rotation orbit
solves the cofactor equation with the proper-partition source terms. -/
theorem complexHessian_angularWord_eq_linearized_det_of_sobolev_orbit {n k m : ℕ}
    (hn : 0 < n) (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v f : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hf : ContDiff ℝ ∞ f)
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hu : ∀ j : ℕ, ∀ R' : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ 1 (dirichletAngularWord R' v) (closedUnitBall n))
    (R : Fin (m + 1) → DirichletUnitaryField n)
    {W : (Fin (m + 1) → ℝ) → CoordinateSobolev n (k + 2)}
    (hW : ∀ᶠ t in 𝓝 (0 : Fin (m + 1) → ℝ), ContDiffAt ℝ ∞ W t ∧
      ∀ x : ClosedBall n, T (W t) x = v (dirichletUnitaryOrbit R t x)) :
    ∀ x ∈ unitBall n, ((complexHessian v x).adjugate *
        complexHessian (dirichletAngularWord R v) x).trace.re +
      dirichletAngularDetLowerTerms R complexHessian v x = dirichletAngularWord R f x := by
  intro x hx
  let X : ClosedBall n := ⟨x, ball_subset_closedBall hx⟩
  obtain ⟨L, hL⟩ := exists_sobolev_complexHessian_eval hn hk T hT hx
  let M := L ∘ W
  let g (C : Matrix (Fin n) (Fin n) ℂ) := C.det.re
  let F (t : Fin (m + 1) → ℝ) := f (dirichletUnitaryOrbit R t x)
  let basisDir (i : Fin (m + 1)) : Fin (m + 1) → ℝ := Pi.single i 1
  have hM : ContDiffAt ℝ ∞ M 0 := L.contDiff.contDiffAt.comp 0 hW.self_of_nhds.1
  have hF : ContDiff ℝ ∞ F :=
    hf.comp ((contDiff_dirichletUnitaryOrbit_apply R).comp (contDiff_id.prodMk contDiff_const))
  have he : g ∘ M =ᶠ[𝓝 (0 : Fin (m + 1) → ℝ)] F := by
    filter_upwards [hW] with t ht
    let Q := dirichletUnitaryOrbit R t
    have hClosed : MapsTo Q (closedUnitBall n) (closedUnitBall n) := by
      intro z hz
      simpa only [closedUnitBall, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hz
    have hQx : Q x ∈ unitBall n := by
      simpa only [unitBall, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
    change (L (W t)).det.re = f (Q x)
    rw [hL _ (hv.continuousOn.comp Q.continuous.continuousOn hClosed) ht.2,
      (complexHessian_posDef_and_det_comp_unitary Q (dirichletUnitaryOrbit_apply_J R t)
        ((hv.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hQx))).2]
    exact hEq hQx
  have hMf : M 0 = complexHessian v x :=
    hL _ hv.continuousOn fun y => by
      simpa only [dirichletUnitaryOrbit_zero_apply] using hW.self_of_nhds.2 y
  have hBlock {j : ℕ} (e : Fin j → Fin (m + 1)) (he : StrictMono e) :
      iteratedFDeriv ℝ j M 0 (basisDir ∘ e) = complexHessian (dirichletAngularWord (R ∘ e) v) x := by
    have hOrd : (j : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
    rw [L.iteratedFDeriv_comp_left hW.self_of_nhds.1 hOrd]
    exact hL _ (hu j (R ∘ e)).continuousOn fun y =>
      eval_iteratedFDeriv_eq_angularWord_of_suborbit ((ContinuousMap.evalCLM ℝ y).comp T)
        R e he hu y (hW.mono fun t ht => ⟨ht.1, ht.2 y⟩)
  have hTop : iteratedFDeriv ℝ (m + 1) M 0 basisDir = complexHessian (dirichletAngularWord R v) x :=
    hBlock id strictMono_id
  have hRight : iteratedFDeriv ℝ (m + 1) F 0 basisDir = dirichletAngularWord R f x :=
    eval_iteratedFDeriv_eq_angularWord_of_orbit (ContinuousLinearMap.id ℝ ℝ) R
      (fun j R' => (contDiffOn_dirichletAngularWord hf.contDiffOn R').of_le (by simp))
      X (Eventually.of_forall fun t => ⟨hF.contDiffAt, rfl⟩)
  have hChain := iteratedFDeriv_comp_succ_eq_linear_add_lower contDiff_det_re hM m basisDir
  change iteratedFDeriv ℝ (m + 1) (g ∘ M) 0 basisDir = _ at hChain
  rw [(he.iteratedFDeriv ℝ (m + 1)).self_of_nhds, hRight, hMf, hTop, fderiv_det_re_apply] at hChain
  rw [hChain, dirichletAngularDetLowerTerms]
  congr 1
  exact Finset.sum_congr rfl fun c _ =>
    congrArg _ (funext fun j => (hBlock (c.emb j) (c.emb_strictMono j)).symm)


/-- The complex Hessian formed using within derivatives on the closed ball. -/
noncomputable def dirichletWithinComplexHessian {n : ℕ} (u : E n → ℝ) (x : E n) :
    Matrix (Fin n) (Fin n) ℂ :=
  complexHessianOfRealBilinear
    (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n) x)

private theorem dirichletWithinComplexHessian_eq {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n} (hx : x ∈ unitBall n) :
    dirichletWithinComplexHessian u x = complexHessian u x := by
  have hN : closedUnitBall n ∈ 𝓝 x := mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  unfold dirichletWithinComplexHessian
  rw [fderivWithin_fderivWithin_eq_of_mem_nhds hN]
  exact complexHessianOfRealBilinear_eq
    ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx))

/-- On a relatively open part of the closed ball, two derivatives are
lost in forming its within Hessian. -/
theorem contDiffOn_dirichletWithinComplexHessian {n r : ℕ}
    {U : Set (E n)} (hU : IsOpen U) {u : E n → ℝ}
    (hu₂ : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hu : ContDiffOn ℝ (r + 2 : ℕ) u (closedUnitBall n ∩ U)) :
    ContDiffOn ℝ r (dirichletWithinComplexHessian u) (closedUnitBall n ∩ U) := by
  let S := closedUnitBall n
  let A := S ∩ U
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
    change (interior (closedBall (0 : E n) 1)).Nonempty
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num))
  have hA := hS.inter hU
  have h2 : ContDiffOn ℝ r (fderivWithin ℝ (fderivWithin ℝ u A) A) A :=
    (hu.fderivWithin (m := ((r + 1 : ℕ) : ℕ∞ω)) hA (by norm_cast)).fderivWithin hA (by norm_cast)
  have hWithin : ContDiffOn ℝ r (fderivWithin ℝ (fderivWithin ℝ u S) S) A := by
    refine h2.congr fun x hx => ?_
    have hN : A ∈ 𝓝[S] x :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.2))
    exact fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hN
      (hu₂.mono inter_subset_left x hx) hS hA hx.1
  exact contDiffOn_pi.mpr fun i =>
    contDiffOn_pi.mpr fun j => contDiffOn_complexHessianOfRealBilinear hWithin i j

/-- The angular word equation holds on the sphere for the within Hessians. -/
theorem closedBall_angularWord_eq_linearized_det_of_sobolev_orbit {n k m : ℕ}
    (hn : 0 < n) (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v f : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hf : ContDiff ℝ ∞ f)
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hu : ∀ j : ℕ, ∀ R' : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ 2 (dirichletAngularWord R' v) (closedUnitBall n))
    (R : Fin (m + 1) → DirichletUnitaryField n)
    {W : (Fin (m + 1) → ℝ) → CoordinateSobolev n (k + 2)}
    (hW : ∀ᶠ t in 𝓝 (0 : Fin (m + 1) → ℝ), ContDiffAt ℝ ∞ W t ∧
      ∀ x : ClosedBall n, T (W t) x = v (dirichletUnitaryOrbit R t x)) :
    ∀ x ∈ closedUnitBall n, ((dirichletWithinComplexHessian v x).adjugate *
        dirichletWithinComplexHessian (dirichletAngularWord R v) x).trace.re +
      dirichletAngularDetLowerTerms R dirichletWithinComplexHessian v x =
        dirichletAngularWord R f x := by
  let S := closedUnitBall n
  let H := dirichletWithinComplexHessian (n := n)
  have hH {w : E n → ℝ} (hw : ContDiffOn ℝ 2 w S) : ContDiffOn ℝ 0 (H w) S := by
    simpa only [inter_univ, Nat.cast_zero] using contDiffOn_dirichletWithinComplexHessian (r := 0)
      isOpen_univ hw (by simpa only [inter_univ, zero_add, Nat.cast_ofNat] using hw)
  have hA := hH hv
  have hB := hH (hu _ R)
  have hFirst : ContinuousOn (fun x => ((H v x).adjugate * H (dirichletAngularWord R v) x).trace.re) S := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      (contDiffOn_adjugate_of_contDiffOn_entries
        (fun a b => contDiffOn_pi.mp (contDiffOn_pi.mp hA a) b) i j).continuousOn.mul
        (contDiffOn_pi.mp (contDiffOn_pi.mp hB j) i).continuousOn
  have hLower := (contDiffOn_dirichletAngularDetLowerTerms R H (by simp) hA
    (fun j _ R' => hH (hu j R'))).continuousOn
  have hRight := (contDiffOn_dirichletAngularWord hf.contDiffOn R).continuousOn
  have hClosure : closure (unitBall n) = S := closure_ball (0 : E n) (by norm_num)
  refine EqOn.of_subset_closure ?_ (hFirst.add hLower) hRight ball_subset_closedBall hClosure.ge
  intro x hx
  have hWord := complexHessian_angularWord_eq_linearized_det_of_sobolev_orbit
    hn hk T hT hv hf hEq (fun j R' => (hu j R').of_le (by norm_num)) R hW x hx
  change ((H v x).adjugate * H (dirichletAngularWord R v) x).trace.re +
    dirichletAngularDetLowerTerms R H v x = _
  have hInterior {w : E n → ℝ} (hw : ContDiffOn ℝ 2 w S) : H w x = complexHessian w x :=
    dirichletWithinComplexHessian_eq hw hx
  rw [hInterior hv, hInterior (hu _ R), ← hWord]
  congr 1
  unfold dirichletAngularDetLowerTerms
  apply Finset.sum_congr rfl
  intro c _
  rw [hInterior hv]
  exact congrArg _ (funext fun j => hInterior (hu _ (R ∘ c.emb j)))

end KEBall
