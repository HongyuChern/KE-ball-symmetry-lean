import KEBall.DirichletAngularBootstrap

/-! Iterating angular differentiation preserves the fixed-order Sobolev
regularity of a positive Dirichlet solution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

/-- Within derivative in a linear direction field tangent to the sphere. -/
noncomputable def dirichletAngularDerivative {n : ℕ} (R : E n →L[ℝ] E n)
    (v : E n → ℝ) (x : E n) : ℝ :=
  fderivWithin ℝ v (closedUnitBall n) x (R x)

private def HasSobolevUnitaryOrbits {n k : ℕ}
    (T : CoordinateSobolev n k →L[ℝ] C(ClosedBall n, ℝ)) (v : E n → ℝ) : Prop :=
  ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (Q : P → E n ≃ₗᵢ[ℝ] E n) (t₀ : P),
    ContDiff ℝ ∞ (fun p : P × E n => Q p.1 p.2) →
    (∀ x, Q t₀ x = x) → (∀ t x, Q t (J x) = J (Q t x)) →
    ∃ W : P → CoordinateSobolev n k,
      ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ ∞ W t ∧ ∀ x : ClosedBall n, T (W t) x = v (Q t x)

private theorem HasSobolevUnitaryOrbits.contDiffOn {n k r : ℕ} (hn : 0 < n)
    (hkr : r + 2 * (2 * n + 1) ≤ k)
    {T : CoordinateSobolev n k →L[ℝ] C(ClosedBall n, ℝ)}
    (hT : ∀ (z : CoordinateSobolev n k) (w : E n → ℝ),
      ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 → ∀ x : ClosedBall n, T z x = w x)
    {v : E n → ℝ} (h : HasSobolevUnitaryOrbits T v) :
    ContDiffOn ℝ r v (closedUnitBall n) := by
  obtain ⟨W, hW⟩ := h (fun _ : ℝ => LinearIsometryEquiv.refl ℝ (E n)) 0
    contDiff_snd (fun _ => rfl) (fun _ _ => rfl)
  have hReg := hasDirichletWeakDerivativesL2_of_jetGraph hn (EuclideanSpace.basisFun _ ℝ) (W 0)
  obtain ⟨w, hw, he⟩ := (hReg.of_le hkr).exists_contDiffOn_closedUnitBall_finite hn
  exact hw.congr fun x hx =>
    (hW.self_of_nhds.2 ⟨x, hx⟩).symm.trans (hT (W 0) w hw.continuousOn he ⟨x, hx⟩)

private theorem HasSobolevUnitaryOrbits.angularDerivative {n k : ℕ}
    {T : CoordinateSobolev n k →L[ℝ] C(ClosedBall n, ℝ)}
    {v : E n → ℝ} (h : HasSobolevUnitaryOrbits T v)
    (hv : ContDiffOn ℝ 1 v (closedUnitBall n))
    (R : E n →L[ℝ] E n) (hR : star R = -R) (hRJ : ∀ x, R (J x) = J (R x)) :
    HasSobolevUnitaryOrbits T (dirichletAngularDerivative R v) := by
  intro P _ _ _ Q t₀ hQ hQ₀ hQJ
  let A (p : P × ℝ) := (Q p.1).trans (orthogonalFlow R hR p.2)
  have hA : ContDiff ℝ ∞ (fun p : (P × ℝ) × E n => A p.1 p.2) :=
    (contDiff_orthogonalFlow_apply R hR).comp (contDiff_fst.snd.prodMk
      (hQ.comp (contDiff_fst.fst.prodMk contDiff_snd)))
  have hA₀ (x : E n) : A (t₀, 0) x = x := by
    change orthogonalFlow R hR 0 (Q t₀ x) = x
    rw [orthogonalFlow_zero_apply, hQ₀]
  have hAJ (t : P × ℝ) (x : E n) : A t (J x) = J (A t x) := by
    change orthogonalFlow R hR t.2 (Q t.1 (J x)) = J (orthogonalFlow R hR t.2 (Q t.1 x))
    rw [hQJ, orthogonalFlow_apply_J R hR hRJ]
  obtain ⟨W, hW⟩ := h A (t₀, 0) hA hA₀ hAJ
  rw [nhds_prod_eq] at hW
  obtain ⟨U, hU, V, hV, hUV⟩ := eventually_prod_iff.mp hW
  let D (t : P) := fderiv ℝ W (t, 0) (0, 1)
  refine ⟨D, ?_⟩
  filter_upwards [hU] with t ht
  have hW₀ := hUV ht (mem_of_mem_nhds hV)
  have hD : ContDiffAt ℝ ∞ D t :=
    ((hW₀.1.fderiv_right (m := ∞) (by simp)).comp t (contDiffAt_id.prodMk contDiffAt_const)).clm_apply
      contDiffAt_const
  refine ⟨hD, fun x => ?_⟩
  let y : ClosedBall n := ⟨Q t x, by
    simpa only [closedUnitBall, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
      using x.property⟩
  let Wt (s : ℝ) := W (t, s)
  have hWDeriv : HasDerivAt Wt (D t) 0 := by
    exact (hW₀.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 t).prodMk (hasDerivAt_id 0))
  let L := T ∘ Wt
  have hL : HasDerivAt L (T (D t)) 0 := T.hasFDerivAt.comp_hasDerivAt 0 hWDeriv
  let Eₓ := (ContinuousMap.evalCLM ℝ x : C(ClosedBall n, ℝ) →L[ℝ] ℝ)
  have hE := Eₓ.hasFDerivAt.comp_hasDerivAt 0 hL
  have hX := hasDerivAt_orthogonalFlow_apply_zero R hR y.val
  have hV' := HasFDerivWithinAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
    ((hv.differentiableOn one_ne_zero y.val y.property).hasFDerivWithinAt) hX
    (Filter.Eventually.of_forall fun s => orthogonalFlow_mapsTo_closedUnitBall R hR s y.property)
    (orthogonalFlow_zero_apply R hR y.val).symm
  have he : (Eₓ ∘ L) =ᶠ[𝓝 (0 : ℝ)] (v ∘ fun s => orthogonalFlow R hR s y.val) :=
    Filter.Eventually.mono hV fun s hs => by
      simp only [Eₓ, L, Wt, Function.comp_apply, ContinuousMap.evalCLM_apply]
      exact (hUV ht hs).2 x
  simpa only [Eₓ, dirichletAngularDerivative, ContinuousMap.evalCLM_apply] using
    hE.deriv.symm.trans (he.deriv_eq.trans hV'.deriv)

/-- Every finite composition of admissible angular derivatives retains
the same spatial regularity furnished by one fixed-order Sobolev inverse. -/
theorem contDiffOn_iteratedAngularDerivative_of_smooth_localInverse {n k r : ℕ} (hn : 0 < n)
    (hr : 1 ≤ r) (hkr : r + 2 * (2 * n + 1) ≤ k + 2)
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
    (Rs : List (E n →L[ℝ] E n))
    (hRs : ∀ R ∈ Rs, star R = -R ∧ ∀ x, R (J x) = J (R x)) :
    ContDiffOn ℝ r (Rs.foldr dirichletAngularDerivative v) (closedUnitBall n) := by
  have h : HasSobolevUnitaryOrbits T v := by
    intro P _ _ _ Q t₀ hQ hQ₀ hQJ
    exact exists_sobolev_unitary_orbit_of_smooth_localInverse hn T hT hG hSol
      hf hv hv0 hvP hvEq hd Q t₀ hQ hQ₀ hQJ
  have hOrbit : HasSobolevUnitaryOrbits T (Rs.foldr dirichletAngularDerivative v) := by
    induction Rs with
    | nil => exact h
    | cons R Rs ih =>
      have hRest : HasSobolevUnitaryOrbits T (Rs.foldr dirichletAngularDerivative v) := ih fun Q hQ => hRs Q (List.mem_cons_of_mem _ hQ)
      have hField := hRs R List.mem_cons_self
      intro P _ _ _ Q t₀ hQ hQ₀ hQJ
      exact hRest.angularDerivative
        ((hRest.contDiffOn hn hkr hT).of_le (by exact_mod_cast hr))
        R hField.1 hField.2 Q t₀ hQ hQ₀ hQJ
  exact hOrbit.contDiffOn hn hkr hT

end KEBall
