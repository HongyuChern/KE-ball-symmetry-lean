import KEBall.DirichletUnitaryHessian
import KEBall.DirichletSobolevParameter

/-! Identifying angular derivatives by uniqueness of the rotated Dirichlet solution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

/-- A smooth curve of closed-ball representatives that agrees with the
rotated solution has derivative given by the angular derivative. -/
theorem eqOn_angularDerivative_of_eq_rotated_curve {n : ℕ} {v : E n → ℝ}
    (hv : ContDiffOn ℝ 1 v (closedUnitBall n))
    (R : E n →L[ℝ] E n) (hR : star R = -R)
    {L : ℝ → C(ClosedBall n, ℝ)} {L' : C(ClosedBall n, ℝ)}
    (hL : HasDerivAt L L' 0)
    (he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x : ClosedBall n, L t x = v (orthogonalFlow R hR t x)) :
    ∀ x : ClosedBall n, L' x = fderivWithin ℝ v (closedUnitBall n) x (R x) := by
  intro x
  have hX := hasDerivAt_orthogonalFlow_apply_zero R hR x.val
  have hD := (hv.differentiableOn one_ne_zero x.val x.property).hasFDerivWithinAt
  have hV := HasFDerivWithinAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hD hX
    (Filter.Eventually.of_forall fun t => orthogonalFlow_mapsTo_closedUnitBall R hR t x.property)
    (orthogonalFlow_zero_apply R hR x.val).symm
  let hEval := (ContinuousMap.evalCLM ℝ x : C(ClosedBall n, ℝ) →L[ℝ] ℝ)
  have hE := hEval.hasFDerivAt.comp_hasDerivAt 0 hL
  have hEq : (hEval ∘ L) =ᶠ[𝓝 (0 : ℝ)] (v ∘ fun t => orthogonalFlow R hR t x.val) :=
    he.mono fun t ht => by
      simpa only [hEval, Function.comp_apply, ContinuousMap.evalCLM_apply] using ht x
  simpa only [hEval, ContinuousMap.evalCLM_apply] using
    hE.deriv.symm.trans (hEq.deriv_eq.trans hV.deriv)

/-- The Sobolev local inverse identifies a smooth orbit of unitary pullbacks
of the classical solution by uniqueness of the Dirichlet problem. -/
theorem exists_sobolev_unitary_orbit_of_smooth_localInverse {n k : ℕ}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (hn : 0 < n)
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
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f)
    (Q : P → E n ≃ₗᵢ[ℝ] E n) (t₀ : P)
    (hQ : ContDiff ℝ ∞ (fun p : P × E n => Q p.1 p.2))
    (hQ₀ : ∀ x, Q t₀ x = x) (hQJ : ∀ t x, Q t (J x) = J (Q t x)) :
    ∃ W : P → dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ),
      ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ ∞ W t ∧ ∀ x : ClosedBall n, T (W t) x = v (Q t x) := by
  let a (p : P × E n) := f (Q p.1 p.2)
  have ha : ContDiff ℝ ∞ a := hf.comp hQ
  have haS (t : P) : ContDiff ℝ ∞ (fun x => a (t, x)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let q (t : P) := dirichletSobolevJetOfSmooth (k := k) hn b (haS t)
  have hq : ContDiff ℝ ∞ q := contDiff_dirichletSobolevJetOfSmooth_family hn b ha haS
  have hq0 : q t₀ = d := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (haS t₀), hd] with x hq' hD
    exact hq'.trans ((congrArg f (hQ₀ x)).trans hD.symm)
  have hToward : Tendsto q (𝓝 t₀) (𝓝 d) := hq0 ▸ hq.continuous.continuousAt.tendsto
  refine ⟨G ∘ q, ?_⟩
  filter_upwards [hToward.eventually hSol, hToward.eventually hG] with t ht hGt
  refine ⟨hGt.comp t hq.contDiffAt, ?_⟩
  obtain ⟨w, hw, hw0, hwP, hwEq, hW⟩ := ht _ (haS t).continuous.continuousOn
    (dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (haS t)).symm
  have hClosed : MapsTo (Q t) (closedUnitBall n) (closedUnitBall n) := by
    intro x hx
    simpa only [closedUnitBall, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hOpen : MapsTo (Q t) (unitBall n) (unitBall n) := by
    intro x hx
    simpa only [unitBall, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hSphere : MapsTo (Q t) (unitSphere n) (unitSphere n) := by
    intro x hx
    simpa only [unitSphere, mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hV : ContDiffOn ℝ 2 (v ∘ Q t) (closedUnitBall n) :=
    hv.comp (Q t).toContinuousLinearEquiv.contDiff.contDiffOn hClosed
  have hLocal (x : E n) (hx : x ∈ unitBall n) :
      ((complexHessian (v ∘ Q t) x).PosDef ↔ (complexHessian v (Q t x)).PosDef) ∧
        (complexHessian (v ∘ Q t) x).det = (complexHessian v (Q t x)).det :=
    complexHessian_posDef_and_det_comp_unitary (Q t) (hQJ t)
      ((hv.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds (hOpen hx)))
  have hvP' (x : E n) (hx : x ∈ unitBall n) : (complexHessian (v ∘ Q t) x).PosDef :=
    (hLocal x hx).1.mpr (hvP _ (hOpen hx))
  have hDet (x : E n) (hx : x ∈ unitBall n) :
      (complexHessian (v ∘ Q t) x).det.re = a (t, x) :=
    (congrArg Complex.re (hLocal x hx).2).trans (hvEq (hOpen hx))
  have he := eqOn_of_det_eq_of_closedBall_C2 hn hw hV hw0
    (fun x hx => hv0 _ (hSphere hx)) hwP hvP' (fun x hx => (hwEq hx).trans (hDet x hx).symm)
  intro x
  exact (hT (G (q t)) w hw.continuousOn hW x).trans (he x.property)

/-- For a nearby positive classical solution, a fixed Sobolev local inverse
and C² uniqueness identify the angular derivative as a closed-ball
representative of a vector in the same Sobolev space. -/
theorem exists_sobolev_angularDerivative_of_smooth_localInverse {n k : ℕ} (hn : 0 < n)
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
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f)
    (R : E n →L[ℝ] E n) (hR : star R = -R) (hJ : ∀ x, R (J x) = J (R x)) :
    ∃ z : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ),
      ∀ x : ClosedBall n, T z x = fderivWithin ℝ v (closedUnitBall n) x (R x) := by
  obtain ⟨W, hW⟩ := exists_sobolev_unitary_orbit_of_smooth_localInverse hn T hT hG hSol
    hf hv hv0 hvP hvEq hd (orthogonalFlow R hR) 0
    (contDiff_orthogonalFlow_apply R hR) (orthogonalFlow_zero_apply R hR) (orthogonalFlow_apply_J R hR hJ)
  have hD := (hW.self_of_nhds.1.differentiableAt (by simp)).hasDerivAt
  have hDT := T.hasFDerivAt.comp_hasDerivAt 0 hD
  exact ⟨_, eqOn_angularDerivative_of_eq_rotated_curve (hv.of_le (by norm_num)) R hR hDT
    (hW.mono fun _ h => h.2)⟩

/-- Angular derivatives have the same finite closed-ball regularity as
the Sobolev representatives produced by the local inverse. -/
theorem contDiffOn_angularDerivative_of_smooth_localInverse {n k r : ℕ} (hn : 0 < n)
    (hkr : r + 2 * (2 * n + 1) ≤ k + 2)
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
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f)
    (R : E n →L[ℝ] E n) (hR : star R = -R) (hJ : ∀ x, R (J x) = J (R x)) :
    ContDiffOn ℝ r (fun x => fderivWithin ℝ v (closedUnitBall n) x (R x)) (closedUnitBall n) := by
  obtain ⟨z, hz⟩ := exists_sobolev_angularDerivative_of_smooth_localInverse hn T hT hG hSol
    hf hv hv0 hvP hvEq hd R hR hJ
  have hReg := hasDirichletWeakDerivativesL2_of_jetGraph hn (EuclideanSpace.basisFun _ ℝ) z
  obtain ⟨w, hw, he⟩ := (hReg.of_le hkr).exists_contDiffOn_closedUnitBall_finite hn
  exact hw.congr fun x hx => (hz ⟨x, hx⟩).symm.trans (hT z w hw.continuousOn he ⟨x, hx⟩)

end KEBall
