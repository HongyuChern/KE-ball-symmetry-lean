import KEBall.DirichletSobolevAngularEquation

/-! Parameter derivatives of the cofactor equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

open KEBallProbe

private noncomputable def matrixEntryCLM {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) i)

private theorem hasDerivAt_cofactor_trace_re_curve {n : ℕ}
    {A B : ℝ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt (fun t => (A t).adjugate) A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun t => ((A t).adjugate * B t).trace.re)
      ((A' * B 0).trace.re + ((A 0).adjugate * B').trace.re) 0 := by
  have hEntry (i j : Fin n) : HasDerivAt (fun t => (A t).adjugate i j) (A' i j) 0 :=
    show HasDerivAt ((matrixEntryCLM i j) ∘ fun t => (A t).adjugate) (matrixEntryCLM i j A') 0 from
      (matrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
  have hBEntry (i j : Fin n) : HasDerivAt (fun t => B t i j) (B' i j) 0 :=
    show HasDerivAt ((matrixEntryCLM i j) ∘ B) (matrixEntryCLM i j B') 0 from
      (matrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hB
  have hSum : HasDerivAt (fun t => ∑ i, ∑ j, (A t).adjugate i j * B t j i)
      (∑ i, ∑ j, (A' i j * B 0 j i + (A 0).adjugate i j * B' j i)) 0 :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      (hEntry i j).mul (hBEntry j i)
  have hReal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hSum
  have he : (fun t => ((A t).adjugate * B t).trace.re) =
      Complex.reCLM ∘ fun t => ∑ i, ∑ j, (A t).adjugate i j * B t j i := rfl
  rw [he]
  simpa only [Complex.reCLM_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Finset.sum_add_distrib, Complex.add_re] using hReal

private theorem contDiff_adjugate {n : ℕ} :
    ContDiff ℝ ∞ (Matrix.adjugate : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_adjugate_of_contDiffOn_entries (A := id)
    (fun i j => show ContDiffOn ℝ ∞ (matrixEntryCLM i j) univ from
      (matrixEntryCLM i j).contDiff.contDiffOn) i j

/-- The highest-order term in a mixed derivative of the determinant is
linear in the mixed derivative of the matrix. The remaining term uses
only the first derivatives and the adjugate. -/
theorem hasDerivAt_mixed_det_re_curve {n : ℕ}
    {A B : ℝ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0)
    {M : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ᶠ s in 𝓝 (0 : ℝ),
      M (s, 0) = A s ∧ HasDerivAt (fun t => M (s, t)) (B s) 0) :
    HasDerivAt (fun s => deriv (fun t => (M (s, t)).det.re) 0)
      (((fderiv ℝ Matrix.adjugate (A 0) A') * B 0).trace.re +
        ((A 0).adjugate * B').trace.re) 0 := by
  have hAdj : HasDerivAt (fun s => (A s).adjugate) (fderiv ℝ Matrix.adjugate (A 0) A') 0 :=
    ((contDiff_adjugate.differentiable (by simp) (A 0)).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hA
  refine (hasDerivAt_cofactor_trace_re_curve hAdj hB).congr_of_eventuallyEq ?_
  filter_upwards [hM] with s hs
  have hDet := (complex_det_differentiableAt (M (s, 0))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hs.2
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hDet
  have he := hRe.deriv
  change deriv (fun t => (M (s, t)).det.re) 0 =
    (fderiv ℝ Matrix.det (M (s, 0)) (B s)).re at he
  rw [he, fderiv_real_complex_det, hs.1]

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

private theorem hasDerivAt_scalar_angular {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 1 u (closedUnitBall n))
    (R : E n →L[ℝ] E n) (hR : star R = -R) (x : ClosedBall n) :
    HasDerivAt (u ∘ fun t => orthogonalFlow R hR t x.val) (dirichletAngularDerivative R u x) 0 :=
  HasFDerivWithinAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
    ((hu.differentiableOn one_ne_zero x.val x.property).hasFDerivWithinAt)
    (hasDerivAt_orthogonalFlow_apply_zero R hR x.val)
    (Eventually.of_forall fun t => orthogonalFlow_mapsTo_closedUnitBall R hR t x.property)
    (orthogonalFlow_zero_apply R hR x.val).symm

private theorem eval_deriv_eq_of_angular_curve {n k : ℕ}
    (T : CoordinateSobolev n k →L[ℝ] C(ClosedBall n, ℝ))
    {u : E n → ℝ} (hu : ContDiffOn ℝ 1 u (closedUnitBall n))
    (R : E n →L[ℝ] E n) (hR : star R = -R)
    {W : ℝ → CoordinateSobolev n k} {D : CoordinateSobolev n k}
    (hD : HasDerivAt W D 0) {x y : ClosedBall n}
    (hW : ∀ᶠ t in 𝓝 (0 : ℝ), T (W t) x = u (orthogonalFlow R hR t y.val)) :
    T D x = dirichletAngularDerivative R u y := by
  let L : CoordinateSobolev n k →L[ℝ] ℝ := (ContinuousMap.evalCLM ℝ x).comp T
  have hL : HasDerivAt (L ∘ W) (L D) 0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
  have he : (L ∘ W) =ᶠ[𝓝 (0 : ℝ)] (u ∘ fun t => orthogonalFlow R hR t y.val) := hW
  exact hL.deriv.symm.trans (he.deriv_eq.trans (hasDerivAt_scalar_angular hu R hR y).deriv)

private theorem hasDerivAt_second_parameter {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {W : ℝ × ℝ → X} {s : ℝ} (hW : DifferentiableAt ℝ W (s, 0)) :
    HasDerivAt (fun t => W (s, t)) (fderiv ℝ W (s, 0) (0, 1)) 0 :=
  hW.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 s).prodMk (hasDerivAt_id 0))

private theorem contDiffAt_second_parameter {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {W : ℝ × ℝ → X} (hW : ContDiffAt ℝ ∞ W (0, 0)) :
    ContDiffAt ℝ ∞ (fun s : ℝ => fderiv ℝ W (s, 0) (0, 1)) 0 := by
  have hSlice : ContDiffAt ℝ ∞ (fun s : ℝ => (s, (0 : ℝ))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hD : ContDiffAt ℝ ∞ (fun s : ℝ => fderiv ℝ W (s, 0)) 0 :=
    ContDiffAt.comp (0 : ℝ) (hW.fderiv_right (m := ∞) (by simp)) hSlice
  exact hD.clm_apply contDiffAt_const

/-- A two-parameter Sobolev orbit identifies the two first angular
derivatives and the mixed angular derivative in the determinant equation. -/
theorem complexHessian_mixedAngularDerivative_eq_linearized_det_of_sobolev_orbit {n k : ℕ}
    (hn : 0 < n) (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v f : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hf : ContDiffOn ℝ 1 f (closedUnitBall n))
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (P R : E n →L[ℝ] E n) (hP : star P = -P) (hR : star R = -R)
    (hPJ : ∀ x, P (J x) = J (P x)) (hRJ : ∀ x, R (J x) = J (R x))
    (hvR : ContDiffOn ℝ 1 (dirichletAngularDerivative R v) (closedUnitBall n))
    (hfR : ContDiffOn ℝ 1 (dirichletAngularDerivative R f) (closedUnitBall n))
    {W : ℝ × ℝ → CoordinateSobolev n (k + 2)}
    (hW : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ ∞ W p ∧
      ∀ x : ClosedBall n, T (W p) x =
        v (orthogonalFlow R hR p.2 (orthogonalFlow P hP p.1 x.val))) :
    ∀ x ∈ unitBall n, ((complexHessian v x).adjugate *
        complexHessian (dirichletAngularDerivative P (dirichletAngularDerivative R v)) x).trace.re +
      ((fderiv ℝ Matrix.adjugate (complexHessian v x)
          (complexHessian (dirichletAngularDerivative P v) x)) *
        complexHessian (dirichletAngularDerivative R v) x).trace.re =
      dirichletAngularDerivative P (dirichletAngularDerivative R f) x := by
  have hv₁ : ContDiffOn ℝ 1 v (closedUnitBall n) := hv.of_le (by norm_num)
  have hC := hW.self_of_nhds.1
  rw [nhds_prod_eq] at hW
  obtain ⟨U, hU, V, hV, hUV⟩ := eventually_prod_iff.mp hW
  have h0V : V (0 : ℝ) := hV.self_of_nhds
  let W₀ (s : ℝ) := W (s, 0)
  let W₁ (s : ℝ) := fderiv ℝ W (s, 0) (0, 1)
  have hSlice : ContDiffAt ℝ ∞ (fun s : ℝ => (s, (0 : ℝ))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hCW₀ : ContDiffAt ℝ ∞ W₀ 0 := ContDiffAt.comp (0 : ℝ) hC hSlice
  have hW₀ : HasDerivAt W₀ (deriv W₀ 0) 0 := (hCW₀.differentiableAt (by simp)).hasDerivAt
  have hW₁ : HasDerivAt W₁ (deriv W₁ 0) 0 :=
    ((contDiffAt_second_parameter hC).differentiableAt (by simp)).hasDerivAt
  have he₀ : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x : ClosedBall n, T (W₀ s) x =
      v (orthogonalFlow P hP s x.val) := by
    filter_upwards [hU] with s hs x
    simpa only [W₀, orthogonalFlow_zero_apply] using (hUV hs h0V).2 x
  have he₁ : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x : ClosedBall n, T (W₁ s) x =
      dirichletAngularDerivative R v (orthogonalFlow P hP s x.val) := by
    filter_upwards [hU] with s hs x
    let y : ClosedBall n := ⟨orthogonalFlow P hP s x.val,
      orthogonalFlow_mapsTo_closedUnitBall P hP s x.property⟩
    exact eval_deriv_eq_of_angular_curve T hv₁ R hR
      (hasDerivAt_second_parameter ((hUV hs h0V).1.differentiableAt (by simp))) (x := x) (y := y)
      (Filter.Eventually.mono hV fun t ht => (hUV hs ht).2 x)
  have hV₀ (x : ClosedBall n) : T (W₀ 0) x = v x := by
    simpa only [orthogonalFlow_zero_apply] using he₀.self_of_nhds x
  have hV₁ (x : ClosedBall n) : T (W₁ 0) x = dirichletAngularDerivative R v x := by
    simpa only [orthogonalFlow_zero_apply] using he₁.self_of_nhds x
  have hV₀' (x : ClosedBall n) : T (deriv W₀ 0) x = dirichletAngularDerivative P v x :=
    eval_deriv_eq_of_angular_curve T hv₁ P hP hW₀ (he₀.mono fun _ he => he x)
  have hV₁' (x : ClosedBall n) : T (deriv W₁ 0) x =
      dirichletAngularDerivative P (dirichletAngularDerivative R v) x :=
    eval_deriv_eq_of_angular_curve T hvR P hP hW₁ (he₁.mono fun _ he => he x)
  have hDiff (u : E n → ℝ) (hu : ContDiffOn ℝ 1 u (closedUnitBall n)) (A : E n →L[ℝ] E n) :
      ContinuousOn (dirichletAngularDerivative A u) (closedUnitBall n) := by
    have hS : UniqueDiffOn ℝ (closedUnitBall n) :=
      uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
        rw [closedUnitBall, interior_closedBall _ (by norm_num)]
        exact nonempty_ball.mpr (by norm_num))
    exact ((hu.fderivWithin (m := 0) hS (by norm_num)).clm_apply A.contDiff.contDiffOn).continuousOn
  intro x hx
  let X : ClosedBall n := ⟨x, ball_subset_closedBall hx⟩
  obtain ⟨L, hL⟩ := exists_sobolev_complexHessian_eval hn hk T hT hx
  let A := L ∘ W₀
  let B := L ∘ W₁
  let M := L ∘ W
  have hA : HasDerivAt A (L (deriv W₀ 0)) 0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hW₀
  have hB : HasDerivAt B (L (deriv W₁ 0)) 0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hW₁
  have hM : ∀ᶠ s in 𝓝 (0 : ℝ), M (s, 0) = A s ∧ HasDerivAt (fun t => M (s, t)) (B s) 0 := by
    filter_upwards [hU] with s hs
    refine ⟨rfl, ?_⟩
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_second_parameter ((hUV hs h0V).1.differentiableAt (by simp)))
  have hDet := hasDerivAt_mixed_det_re_curve hA hB hM
  have hE : (fun s => deriv (fun t => (M (s, t)).det.re) 0) =ᶠ[𝓝 (0 : ℝ)]
      (dirichletAngularDerivative R f ∘ fun s => orthogonalFlow P hP s x) := by
    filter_upwards [hU] with s hs
    let y : ClosedBall n := ⟨orthogonalFlow P hP s x,
      orthogonalFlow_mapsTo_closedUnitBall P hP s X.property⟩
    have hF : (fun t => (M (s, t)).det.re) =ᶠ[𝓝 (0 : ℝ)]
        (f ∘ fun t => orthogonalFlow R hR t y.val) := by
      filter_upwards [hV] with t ht
      let Q := (orthogonalFlow P hP s).trans (orthogonalFlow R hR t)
      have hClosed : MapsTo Q (closedUnitBall n) (closedUnitBall n) := by
        intro z hz
        simpa only [closedUnitBall, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hz
      have hQx : Q x ∈ unitBall n := by
        simpa only [unitBall, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
      have hJ (z : E n) : Q (J z) = J (Q z) := by
        change orthogonalFlow R hR t (orthogonalFlow P hP s (J z)) = _
        rw [orthogonalFlow_apply_J P hP hPJ, orthogonalFlow_apply_J R hR hRJ]
        rfl
      change (L (W (s, t))).det.re = f (Q x)
      rw [hL _ (hv.continuousOn.comp Q.continuous.continuousOn hClosed) ((hUV hs ht).2)]
      rw [(complexHessian_posDef_and_det_comp_unitary Q hJ
        ((hv.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hQx))).2]
      exact hEq hQx
    exact hF.deriv_eq.trans (hasDerivAt_scalar_angular hf R hR y).deriv
  have he := hDet.deriv.symm.trans (hE.deriv_eq.trans (hasDerivAt_scalar_angular hfR P hP X).deriv)
  change ((fderiv ℝ Matrix.adjugate (L (W₀ 0)) (L (deriv W₀ 0))) * L (W₁ 0)).trace.re +
    ((L (W₀ 0)).adjugate * L (deriv W₁ 0)).trace.re =
      dirichletAngularDerivative P (dirichletAngularDerivative R f) x at he
  rw [hL _ hv.continuousOn hV₀, hL _ (hDiff v hv₁ P) hV₀', hL _ hvR.continuousOn hV₁,
    hL _ (hDiff _ hvR P) hV₁', add_comm] at he
  exact he

/-- The mixed angular cofactor equation holds up to the sphere for
continuous within Hessians. -/
theorem closedBall_withinHessian_mixedAngularDerivative_eq_linearized_det_of_sobolev_orbit {n k : ℕ}
    (hn : 0 < n) (hk : 2 * (2 * n + 1) ≤ k)
    (T : CoordinateSobolev n (k + 2) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : CoordinateSobolev n (k + 2)) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v f : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hf : ContDiffOn ℝ 1 f (closedUnitBall n))
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (P R : E n →L[ℝ] E n) (hP : star P = -P) (hR : star R = -R)
    (hPJ : ∀ x, P (J x) = J (P x)) (hRJ : ∀ x, R (J x) = J (R x))
    (hvR : ContDiffOn ℝ 1 (dirichletAngularDerivative R v) (closedUnitBall n))
    (hfR : ContDiffOn ℝ 1 (dirichletAngularDerivative R f) (closedUnitBall n))
    (hvP : ContDiffOn ℝ 2 (dirichletAngularDerivative P v) (closedUnitBall n))
    (hvR₂ : ContDiffOn ℝ 2 (dirichletAngularDerivative R v) (closedUnitBall n))
    (hvPR : ContDiffOn ℝ 2 (dirichletAngularDerivative P (dirichletAngularDerivative R v)) (closedUnitBall n))
    (hfPR : ContinuousOn (dirichletAngularDerivative P (dirichletAngularDerivative R f)) (closedUnitBall n))
    {W : ℝ × ℝ → CoordinateSobolev n (k + 2)}
    (hW : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ ∞ W p ∧
      ∀ x : ClosedBall n, T (W p) x =
        v (orthogonalFlow R hR p.2 (orthogonalFlow P hP p.1 x.val))) :
    let S := closedUnitBall n
    let A (u : E n → ℝ) (x : E n) := complexHessianOfRealBilinear
      (fderivWithin ℝ (fderivWithin ℝ u S) S x)
    ∀ x ∈ S, ((A v x).adjugate * A (dirichletAngularDerivative P (dirichletAngularDerivative R v)) x).trace.re +
      ((fderiv ℝ Matrix.adjugate (A v x) (A (dirichletAngularDerivative P v) x)) *
        A (dirichletAngularDerivative R v) x).trace.re =
      dirichletAngularDerivative P (dirichletAngularDerivative R f) x := by
  let S := closedUnitBall n
  let A (u : E n → ℝ) (x : E n) := complexHessianOfRealBilinear
    (fderivWithin ℝ (fderivWithin ℝ u S) S x)
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
    change (interior (closedBall (0 : E n) 1)).Nonempty
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num))
  have hA {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u S) : ContinuousOn (A u) S := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear
      ((hu.fderivWithin (m := 1) hS (by norm_num)).fderivWithin (m := 0) hS (by norm_num)) i j).continuousOn
  have hAdj := contDiff_adjugate (n := n)
  have hF : ContinuousOn (fun x => fderiv ℝ Matrix.adjugate (A v x) (A (dirichletAngularDerivative P v) x)) S :=
    ((hAdj.fderiv_right (m := ∞) (by simp)).continuous.comp_continuousOn (hA hv)).clm_apply (hA hvP)
  have hTrace (B C : E n → Matrix (Fin n) (Fin n) ℂ)
      (hB : ContinuousOn B S) (hC : ContinuousOn C S) :
      ContinuousOn (fun x => (B x * C x).trace.re) S := by
    have hEval (D : E n → Matrix (Fin n) (Fin n) ℂ) (hD : ContinuousOn D S) (i j : Fin n) :
        ContinuousOn (fun x => D x i j) S := (matrixEntryCLM i j).continuous.comp_continuousOn hD
    apply Complex.continuous_re.comp_continuousOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      (hEval _ hB i j).mul (hEval _ hC j i)
  have hLeft := (hTrace _ _ (hAdj.continuous.comp_continuousOn (hA hv)) (hA hvPR)).add
    (hTrace _ _ hF (hA hvR₂))
  have hCl : closure (unitBall n) = S := closure_ball (0 : E n) (by norm_num)
  refine EqOn.of_subset_closure ?_ hLeft hfPR ball_subset_closedBall hCl.ge
  intro x hx
  have hInterior {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u S) : A u x = complexHessian u x := by
    dsimp only [A]
    have hN : S ∈ 𝓝 x := mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
    rw [fderivWithin_fderivWithin_eq_of_mem_nhds hN]
    exact complexHessianOfRealBilinear_eq
      ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx))
  change ((A v x).adjugate * A (dirichletAngularDerivative P (dirichletAngularDerivative R v)) x).trace.re +
    ((fderiv ℝ Matrix.adjugate (A v x) (A (dirichletAngularDerivative P v) x)) *
      A (dirichletAngularDerivative R v) x).trace.re =
    dirichletAngularDerivative P (dirichletAngularDerivative R f) x
  rw [hInterior hv, hInterior hvP, hInterior hvR₂, hInterior hvPR]
  exact complexHessian_mixedAngularDerivative_eq_linearized_det_of_sobolev_orbit
    hn hk T hT hv hf hEq P R hP hR hPJ hRJ hvR hfR hW x hx

/-- A fixed Sobolev inverse gives (C^6) regularity away from the
center by recovering normal derivatives in the mixed angular equation. -/
theorem contDiffOn_closedBall_inter_six_of_smooth_localInverse {n k : ℕ} (hn : 0 < n)
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
    ContDiffOn ℝ 6 v (closedUnitBall n ∩ U) := by
  let S := closedUnitBall n
  let U' := S ∩ U
  let H (w : E n → ℝ) (x : E n) := complexHessianOfRealBilinear
    (fderivWithin ℝ (fderivWithin ℝ w S) S x)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have hv₂ : ContDiffOn ℝ 2 v S := hv.of_le (by norm_num)
  have hf₄ : ContDiffOn ℝ 4 f S :=
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)).contDiffOn
  have hPos := closedBall_withinHessian_posDef_and_det_of_C2 hv₂ hf.continuous.continuousOn hfPos hvP hvEq
  have hv₅ : ContDiffOn ℝ 5 v U' :=
    contDiffOn_closedBall_inter_five_of_smooth_localInverse hn hk hkr hU hAway T hT hG hSol
      hf hv hv0 hvP hvEq hd hfPos
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
    change (interior (closedBall (0 : E n) 1)).Nonempty
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num))
  have hU' : UniqueDiffOn ℝ U' := hS.inter hU
  have hAngF {m : ℕ} {g : E n → ℝ} (hg : ContDiffOn ℝ (m + 1 : ℕ) g S) (R : E n →L[ℝ] E n) :
      ContDiffOn ℝ m (dirichletAngularDerivative R g) S := by
    have hm : (m : ℕ∞ω) + 1 ≤ (m + 1 : ℕ) := by exact_mod_cast (le_refl (m + 1))
    exact (hg.fderivWithin hS hm).clm_apply R.contDiff.contDiffOn
  have hH {m : ℕ} {w : E n → ℝ} (hw₂ : ContDiffOn ℝ 2 w S)
      (hw : ContDiffOn ℝ (m + 2 : ℕ) w U') :
      ContDiffOn ℝ m (H w) U' := by
    have hm₁ : ((m + 1 : ℕ) : ℕ∞ω) + 1 ≤ (m + 2 : ℕ) := by
      exact_mod_cast (show (m + 1) + 1 ≤ m + 2 by omega)
    have hm₂ : (m : ℕ∞ω) + 1 ≤ (m + 1 : ℕ) := by exact_mod_cast (le_refl (m + 1))
    have hB := (hw.fderivWithin hU' hm₁).fderivWithin hU' hm₂
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    refine (contDiffOn_complexHessianOfRealBilinear hB i j).congr fun x hx => ?_
    have hN : U' ∈ 𝓝[S] x :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.2))
    simp only [H, fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hN
      (hw₂.mono inter_subset_left x hx) hS hU' hx.1]
  have hEntry {m : ℕ} {A : E n → Matrix (Fin n) (Fin n) ℂ} (hA : ContDiffOn ℝ m A U') (i j : Fin n) :
      ContDiffOn ℝ m (fun x => A x i j) U' :=
    (matrixEntryCLM i j).contDiff.comp_contDiffOn hA
  have hTrace {m : ℕ} {A B : E n → Matrix (Fin n) (Fin n) ℂ}
      (hA : ContDiffOn ℝ m A U') (hB : ContDiffOn ℝ m B U') :
      ContDiffOn ℝ m (fun x => (A x * B x).trace.re) U' := by
    apply Complex.reCLM.contDiff.comp_contDiffOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (hEntry hA i j).mul (hEntry hB j i)
  have hC := hH (m := 3) hv₂ hv₅
  have hC₂ := hC.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hCentral (x : E n) : JCLM n (J x) = J (JCLM n x) := by simp only [JCLM_apply]
  let good (R : E n →L[ℝ] E n) : Prop := star R = -R ∧ ∀ x, R (J x) = J (R x)
  have hRot (i j : Fin (2 * n)) : good (dirichletUnitaryRotation (b i) (b j)) :=
    ⟨dirichletUnitaryRotation_star (b i) (b j), dirichletUnitaryRotation_J (b i) (b j)⟩
  have hJ : good (JCLM n) := ⟨JCLM_star n, hCentral⟩
  have hBase (Rs : List (E n →L[ℝ] E n)) (hRs : ∀ R ∈ Rs, good R) :
      ContDiffOn ℝ 3 (Rs.foldr dirichletAngularDerivative v) S :=
    contDiffOn_iteratedAngularDerivative_of_smooth_localInverse hn (by norm_num) hkr
      T hT hG hSol hf hv₂ hv0 hvP hvEq hd Rs hRs
  have hA₃ (R : E n →L[ℝ] E n) (hR : good R) :
      ContDiffOn ℝ 3 (dirichletAngularDerivative R v) S := hBase [R] (by simpa)
  have hA₂ (R : E n →L[ℝ] E n) (hR : good R) :
      ContDiffOn ℝ 2 (dirichletAngularDerivative R v) S := (hA₃ R hR).of_le (by norm_num)
  have hEq₁ (R : E n →L[ℝ] E n) (hR : good R) :
      ∀ x ∈ S, ((H v x).adjugate * H (dirichletAngularDerivative R v) x).trace.re =
        dirichletAngularDerivative R f x := by
    obtain ⟨W, hW⟩ := exists_sobolev_unitary_orbit_of_smooth_localInverse hn T hT hG hSol
      hf hv₂ hv0 hvP hvEq hd (orthogonalFlow R hR.1) 0 (contDiff_orthogonalFlow_apply R hR.1)
      (orthogonalFlow_zero_apply R hR.1) (orthogonalFlow_apply_J R hR.1 hR.2)
    exact closedBall_withinHessian_angularDerivative_eq_linearized_det_of_sobolev_orbit
      hn hk T hT hv₂ (hf₄.of_le (by norm_num)) hvEq R hR.1 hR.2 (hA₂ R hR)
      (hW.self_of_nhds.1.differentiableAt (by simp)) (hW.mono fun _ h => h.2)
  have hAngle₄ (R : E n →L[ℝ] E n) (hR : good R) :
      ContDiffOn ℝ 4 (dirichletAngularDerivative R v) U' := by
    have hTwo (P : E n →L[ℝ] E n) (hP : good P) :
        ContDiffOn ℝ 3 (dirichletAngularDerivative P (dirichletAngularDerivative R v)) U' := by
      apply ContDiffOn.mono _ inter_subset_left
      exact hBase [P, R] (by simp [hP, hR])
    exact contDiffOn_closedBall_inter_succ_of_angularDerivatives_linearized_det (r := 2)
      hU hAway (hA₂ R hR) ((hA₃ R hR).mono inter_subset_left) b
      (fun i j => hTwo _ (hRot i j)) (hTwo _ hJ)
      ((hAngF (m := 2) (hf₄.of_le (by norm_num)) R).mono inter_subset_left)
      (hEntry hC₂) (fun x hx => (hPos x hx.1).1) (fun x hx => hEq₁ R hR x hx.1)
  have hAngle₂₄ (P R : E n →L[ℝ] E n) (hP : good P) (hR : good R) :
      ContDiffOn ℝ 4 (dirichletAngularDerivative P (dirichletAngularDerivative R v)) U' := by
    let Q (p : ℝ × ℝ) := (orthogonalFlow P hP.1 p.1).trans (orthogonalFlow R hR.1 p.2)
    have hQ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E n => Q p.1 p.2) :=
      (contDiff_orthogonalFlow_apply R hR.1).comp (contDiff_fst.snd.prodMk
        ((contDiff_orthogonalFlow_apply P hP.1).comp (contDiff_fst.fst.prodMk contDiff_snd)))
    have hQ₀ (x : E n) : Q (0, 0) x = x := by
      change orthogonalFlow R hR.1 0 (orthogonalFlow P hP.1 0 x) = x
      rw [orthogonalFlow_zero_apply, orthogonalFlow_zero_apply]
    have hQJ (t : ℝ × ℝ) (x : E n) : Q t (J x) = J (Q t x) := by
      change orthogonalFlow R hR.1 t.2 (orthogonalFlow P hP.1 t.1 (J x)) = _
      rw [orthogonalFlow_apply_J P hP.1 hP.2, orthogonalFlow_apply_J R hR.1 hR.2]
      rfl
    obtain ⟨W, hW⟩ := exists_sobolev_unitary_orbit_of_smooth_localInverse hn T hT hG hSol
      hf hv₂ hv0 hvP hvEq hd Q (0, 0) hQ hQ₀ hQJ
    have hF₃ : ContDiffOn ℝ 3 (dirichletAngularDerivative R f) S := hAngF (m := 3) hf₄ R
    have hF₂ : ContDiffOn ℝ 2 (dirichletAngularDerivative P (dirichletAngularDerivative R f)) S :=
      hAngF (m := 2) hF₃ P
    have hPR₃ : ContDiffOn ℝ 3 (dirichletAngularDerivative P (dirichletAngularDerivative R v)) S :=
      hBase [P, R] (by simp [hP, hR])
    have hPR₂ := hPR₃.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
    have hEq₂ := closedBall_withinHessian_mixedAngularDerivative_eq_linearized_det_of_sobolev_orbit
      hn hk T hT hv₂ (hf₄.of_le (by norm_num)) hvEq P R hP.1 hR.1 hP.2 hR.2
      ((hA₃ R hR).of_le (by norm_num)) (hF₃.of_le (by norm_num))
      (hA₂ P hP) (hA₂ R hR) hPR₂ hF₂.continuousOn hW
    have hAP := hH (m := 2) (hA₂ P hP) (hAngle₄ P hP)
    have hAR := hH (m := 2) (hA₂ R hR) (hAngle₄ R hR)
    have hAdj : ContDiffOn ℝ 2
        (fun x => fderiv ℝ Matrix.adjugate (H v x) (H (dirichletAngularDerivative P v) x)) U' :=
      (((contDiff_adjugate (n := n)).fderiv_right (m := 2)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).comp_contDiffOn hC₂).clm_apply hAP
    have hThree (A : E n →L[ℝ] E n) (hA : good A) :
        ContDiffOn ℝ 3 (dirichletAngularDerivative A
          (dirichletAngularDerivative P (dirichletAngularDerivative R v))) U' := by
      apply ContDiffOn.mono _ inter_subset_left
      exact hBase [A, P, R] (by simp [hA, hP, hR])
    exact contDiffOn_closedBall_inter_succ_of_angularDerivatives_linearized_det (r := 2)
      hU hAway hPR₂ (hPR₃.mono inter_subset_left) b
      (fun i j => hThree _ (hRot i j)) (hThree _ hJ)
      ((hF₂.mono inter_subset_left).sub (hTrace hAdj hAR))
      (hEntry hC₂) (fun x hx => (hPos x hx.1).1)
      (fun x hx => eq_sub_of_add_eq (hEq₂ x hx.1))
  have hAngle₅ (R : E n →L[ℝ] E n) (hR : good R) :
      ContDiffOn ℝ 5 (dirichletAngularDerivative R v) U' :=
    contDiffOn_closedBall_inter_succ_of_angularDerivatives_linearized_det (r := 3)
      hU hAway (hA₂ R hR) (hAngle₄ R hR) b
      (fun i j => hAngle₂₄ _ R (hRot i j) hR) (hAngle₂₄ _ R hJ hR)
      ((hAngF (m := 3) hf₄ R).mono inter_subset_left) (hEntry hC)
      (fun x hx => (hPos x hx.1).1) (fun x hx => hEq₁ R hR x hx.1)
  exact contDiffOn_closedBall_inter_succ_of_angularDerivatives_det (r := 4) hU hAway hv₂ hv₅ b
    (fun i j => hAngle₅ _ (hRot i j)) (hAngle₅ _ hJ) (hf₄.mono inter_subset_left)
    (fun x hx => (hPos x hx.1).1) (fun x hx => (hPos x hx.1).2)

/-- The log-density path has positive local solutions with C³ regularity
on the closed ball and C⁶ regularity near the sphere. -/
theorem eventually_exists_closedBall_C3_annular_C6_dirichlet_logDensity {n : ℕ} (hn : 0 < n)
    {u g : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (t : ℝ)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) (fun x => Real.exp (t * g x)) (unitBall n))
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∀ᶠ s in 𝓝 t, ∃ v : E n → ℝ, ContDiffOn ℝ 3 v (closedUnitBall n) ∧
      (∀ U : Set (E n), IsOpen U → (0 : E n) ∉ U → ContDiffOn ℝ 6 v (closedUnitBall n ∩ U)) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      EqOn (fun x => (complexHessian v x).det.re) (fun x => Real.exp (s * g x)) (unitBall n) := by
  let k := 3 + 2 * (2 * n + 1)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let f (p : ℝ × E n) := Real.exp (p.1 * g p.2)
  have hf : ContDiff ℝ ∞ f := (contDiff_fst.mul (hg.comp contDiff_snd)).exp
  have hfS (s : ℝ) : ContDiff ℝ ∞ (fun x => f (s, x)) := ((contDiff_const (c := s)).mul hg).exp
  let q (s : ℝ) := dirichletSobolevJetOfSmooth (k := k) hn b (hfS s)
  have hq : Continuous q := continuous_dirichletSobolevJetOfSmooth_family hn b hf hfS
  have hk : 2 * (2 * n + 1) ≤ k := Nat.le_add_left _ _
  have hkr : 3 + 2 * (2 * n + 1) ≤ k + 2 := Nat.le_add_right _ _
  obtain ⟨d, G, T, hG, hT, hd, hSol⟩ := exists_smooth_closedBall_posDef_dirichlet_det_localInverse
    hn hk (r := 3) (by norm_num) hkr hu hu0 huP ha hl hDensity hElliptic
  have hBase : q t = d := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [hd, dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hfS t),
      ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hD hQ hB
    exact hQ.trans ((hEq hB).symm.trans hD.symm)
  have hQ : Tendsto q (𝓝 t) (𝓝 d) := hBase ▸ hq.continuousAt
  filter_upwards [hQ.eventually hSol, hQ.eventually (eventually_eventually_nhds.mpr hG),
    hQ.eventually (eventually_eventually_nhds.mpr hSol)] with s hs hGs hSols
  have hqS := dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hfS s)
  obtain ⟨v, hv, hv0, hvP, hvEq, hvG⟩ := hs _ (hfS s).continuous.continuousOn hqS.symm
  refine ⟨v, hv, ?_, hv0, hvP, hvEq⟩
  intro U hU hAway
  apply contDiffOn_closedBall_inter_six_of_smooth_localInverse hn hk hkr hU hAway T hT hGs _ (hfS s)
    hv hv0 hvP hvEq hqS
  · intro x _
    exact Real.exp_pos _
  · filter_upwards [hSols] with z hz F hF hFz
    obtain ⟨w, hw, hw0, hwP, hwEq, hwG⟩ := hz F hF hFz
    exact ⟨w, hw.of_le (by norm_num), hw0, hwP, hwEq, hwG⟩

end KEBall
