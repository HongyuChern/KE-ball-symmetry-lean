import KEBall.DirichletAngularWordEquation

/-! Repeated normal recovery on the closed ball away from the center. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private theorem dirichletAngularWord_cons {n m : ℕ}
    (P : DirichletUnitaryField n) (R : Fin m → DirichletUnitaryField n) (u : E n → ℝ) :
    dirichletAngularWord (Fin.cons P R) u =
      dirichletAngularDerivative P.val (dirichletAngularWord R u) := by
  simp only [dirichletAngularWord, Fin.cons_zero, Fin.tail_cons]

/-- If every angular word has two derivatives on the closed ball and the
cofactor equations hold, normal recovery bootstraps all words to smoothness
on any relatively open annulus with positive complex Hessian. -/
theorem contDiffOn_closedBall_inter_infty_of_angularWord_equations {n : ℕ}
    {U : Set (E n)} (hU : IsOpen U) (hAway : (0 : E n) ∉ U)
    {v f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f (closedUnitBall n))
    (hBase : ∀ j : ℕ, ∀ R : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ 2 (dirichletAngularWord R v) (closedUnitBall n))
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian v x).PosDef)
    (hDet : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian v x).det.re = f x)
    (hEq : ∀ m : ℕ, ∀ R : Fin (m + 1) → DirichletUnitaryField n,
      ∀ x ∈ closedUnitBall n, ((dirichletWithinComplexHessian v x).adjugate *
        dirichletWithinComplexHessian (dirichletAngularWord R v) x).trace.re +
        dirichletAngularDetLowerTerms R dirichletWithinComplexHessian v x =
          dirichletAngularWord R f x) :
    ∀ j : ℕ, ∀ R : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ ∞ (dirichletAngularWord R v) (closedUnitBall n ∩ U) := by
  let S := closedUnitBall n
  let A := S ∩ U
  let H := dirichletWithinComplexHessian (n := n)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let rot (i j : Fin (2 * n)) : DirichletUnitaryField n :=
    ⟨dirichletUnitaryRotation (b i) (b j), dirichletUnitaryRotation_star _ _,
      dirichletUnitaryRotation_J _ _⟩
  let central : DirichletUnitaryField n :=
    ⟨JCLM n, JCLM_star n, fun x => by simp only [JCLM_apply]⟩
  have hv₂ : ContDiffOn ℝ 2 v S := hBase 0 Fin.elim0
  have hFinite (q : ℕ) : ∀ j : ℕ, ∀ R : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ (q + 2 : ℕ) (dirichletAngularWord R v) A := by
    induction q with
    | zero =>
      intro j R
      simpa only [zero_add, Nat.cast_ofNat] using (hBase j R).mono inter_subset_left
    | succ q ih =>
      have hOrd : (q + 1 : ℕ) + 1 = q + 2 := by omega
      have hOrder : ((q + 1 : ℕ) : ℕ∞ω) ≤ ∞ :=
        ENat.natCast_le_of_coe_top_le_withTop le_rfl (q + 1)
      have hOld (j : ℕ) (R : Fin j → DirichletUnitaryField n) :
          ContDiffOn ℝ ((q + 1 : ℕ) + 1 : ℕ) (dirichletAngularWord R v) A :=
        hOrd.symm ▸ ih j R
      have hNext {j : ℕ} (R : Fin j → DirichletUnitaryField n)
          (P : DirichletUnitaryField n) :
          ContDiffOn ℝ ((q + 1 : ℕ) + 1 : ℕ)
            (dirichletAngularDerivative P.val (dirichletAngularWord R v)) A := by
        rw [← dirichletAngularWord_cons P R v]
        exact hOld _ _
      have hv : ContDiffOn ℝ ((q + 1 : ℕ) + 2 : ℕ) v A :=
        contDiffOn_closedBall_inter_succ_of_angularDerivatives_det (r := q + 1) hU hAway
          hv₂ (hOld 0 Fin.elim0) b
          (fun i j => hNext (Fin.elim0 : Fin 0 → DirichletUnitaryField n) (rot i j))
          (hNext (Fin.elim0 : Fin 0 → DirichletUnitaryField n) central)
          ((hf.of_le hOrder).mono inter_subset_left) (fun x hx => hPos x hx.1)
          (fun x hx => hDet x hx.1)
      have hH : ContDiffOn ℝ (q + 1 : ℕ) (H v) A :=
        contDiffOn_dirichletWithinComplexHessian hU hv₂ hv
      have hCoeff (i j : Fin n) : ContDiffOn ℝ (q + 1 : ℕ) (fun x => H v x i j) A :=
        contDiffOn_pi.mp (contDiffOn_pi.mp hH i) j
      intro j
      induction j using Nat.strong_induction_on with
      | h j hShort =>
        intro R
        cases j with
        | zero => exact hv
        | succ m =>
          have hLow : ContDiffOn ℝ (q + 1 : ℕ) (dirichletAngularDetLowerTerms R H v) A :=
            contDiffOn_dirichletAngularDetLowerTerms R H hOrder hH fun j hj R' =>
              contDiffOn_dirichletWithinComplexHessian hU (hBase j R')
                (hShort j (Nat.lt_succ_of_le hj) R')
          have hF : ContDiffOn ℝ (q + 1 : ℕ)
              (fun x => dirichletAngularWord R f x - dirichletAngularDetLowerTerms R H v x) A :=
            (((contDiffOn_dirichletAngularWord hf R).of_le hOrder).mono inter_subset_left).sub hLow
          exact contDiffOn_closedBall_inter_succ_of_angularDerivatives_linearized_det
            (r := q + 1) hU hAway (hBase _ R) (hOld _ R) b
            (fun i j => hNext R (rot i j)) (hNext R central) hF hCoeff
            (fun x hx => hPos x hx.1) (fun x hx => eq_sub_of_add_eq (hEq m R x hx.1))
  intro j R
  apply contDiffOn_infty.mpr
  intro q
  exact (hFinite q j R).of_le (by exact_mod_cast Nat.le_add_right q 2)


/-- Smooth prescribed density and a fixed-order Sobolev inverse imply
smoothness away from the center, including at the sphere. -/
theorem contDiffOn_closedBall_inter_infty_of_smooth_localInverse {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k)
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
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f)
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x) :
    ContDiffOn ℝ ∞ v (closedUnitBall n ∩ U) := by
  have hBase (j : ℕ) (R : Fin j → DirichletUnitaryField n) :
      ContDiffOn ℝ 2 (dirichletAngularWord R v) (closedUnitBall n) := by
    rw [dirichletAngularWord_eq_foldr]
    exact contDiffOn_iteratedAngularDerivative_of_smooth_localInverse (r := 2) hn (by norm_num) (by omega)
      T hT hG hSol hf hv hv0 hvP hvEq hd _
      (fun R' hR' => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hR'
        exact (R i).property)
  have hPos := closedBall_withinHessian_posDef_and_det_of_C2 hv
    hf.continuous.continuousOn hfPos hvP hvEq
  have hEquation (m : ℕ) (R : Fin (m + 1) → DirichletUnitaryField n) :
      ∀ x ∈ closedUnitBall n, ((dirichletWithinComplexHessian v x).adjugate *
        dirichletWithinComplexHessian (dirichletAngularWord R v) x).trace.re +
        dirichletAngularDetLowerTerms R dirichletWithinComplexHessian v x =
          dirichletAngularWord R f x := by
    obtain ⟨W, hW⟩ := exists_sobolev_unitary_orbit_of_smooth_localInverse hn T hT hG hSol
      hf hv hv0 hvP hvEq hd (dirichletUnitaryOrbit R) 0 (contDiff_dirichletUnitaryOrbit_apply R)
      (dirichletUnitaryOrbit_zero_apply R) (dirichletUnitaryOrbit_apply_J R)
    exact closedBall_angularWord_eq_linearized_det_of_sobolev_orbit hn hk T hT hv hf hvEq hBase R hW
  exact contDiffOn_closedBall_inter_infty_of_angularWord_equations hU hAway hf.contDiffOn hBase
    (fun x hx => (hPos x hx).1) (fun x hx => (hPos x hx).2) hEquation 0 Fin.elim0

end KEBall
