import KEBall.DirichletHighestDerivative

/-! Ordered products of the flows of finitely many unitary generators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Metric Set
open scoped ContDiff Topology

namespace KEBall

/-- A real skew-adjoint linear field commuting with the complex structure. -/
abbrev DirichletUnitaryField (n : ℕ) :=
  {R : E n →L[ℝ] E n // star R = -R ∧ ∀ x, R (J x) = J (R x)}

noncomputable def dirichletUnitaryOrbit {n : ℕ} :
    {m : ℕ} → (Fin m → DirichletUnitaryField n) → (Fin m → ℝ) → E n ≃ₗᵢ[ℝ] E n
  | 0, _, _ => LinearIsometryEquiv.refl ℝ (E n)
  | _m + 1, R, t =>
    (orthogonalFlow (R 0).val (R 0).property.1 (t 0)).trans
      (dirichletUnitaryOrbit (Fin.tail R) (Fin.tail t))

@[simp] theorem dirichletUnitaryOrbit_succ_apply {n m : ℕ}
    (R : Fin (m + 1) → DirichletUnitaryField n) (t : Fin (m + 1) → ℝ) (x : E n) :
    dirichletUnitaryOrbit R t x = dirichletUnitaryOrbit (Fin.tail R) (Fin.tail t)
      (orthogonalFlow (R 0).val (R 0).property.1 (t 0) x) := rfl

@[simp] theorem dirichletUnitaryOrbit_zero_apply {n m : ℕ}
    (R : Fin m → DirichletUnitaryField n) (x : E n) : dirichletUnitaryOrbit R 0 x = x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [dirichletUnitaryOrbit_succ_apply]
    change dirichletUnitaryOrbit (Fin.tail R) 0
      (orthogonalFlow (R 0).val (R 0).property.1 0 x) = x
    rw [orthogonalFlow_zero_apply, ih]

theorem dirichletUnitaryOrbit_apply_J {n m : ℕ}
    (R : Fin m → DirichletUnitaryField n) (t : Fin m → ℝ) (x : E n) :
    dirichletUnitaryOrbit R t (J x) = J (dirichletUnitaryOrbit R t x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [dirichletUnitaryOrbit_succ_apply]
    rw [orthogonalFlow_apply_J _ _ (R 0).property.2, ih]

theorem contDiff_dirichletUnitaryOrbit_apply {n m : ℕ}
    (R : Fin m → DirichletUnitaryField n) :
    ContDiff ℝ ∞ (fun p : (Fin m → ℝ) × E n => dirichletUnitaryOrbit R p.1 p.2) := by
  induction m with
  | zero => exact contDiff_snd
  | succ m ih =>
    simp only [dirichletUnitaryOrbit_succ_apply]
    have hTail : ContDiff ℝ ∞ (fun p : (Fin (m + 1) → ℝ) × E n => Fin.tail p.1) :=
      contDiff_pi.mpr fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ)
        i.succ).contDiff.comp contDiff_fst
    have hHead : ContDiff ℝ ∞ (fun p : (Fin (m + 1) → ℝ) × E n => p.1 0) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ)
        0).contDiff.comp contDiff_fst
    have hInner := (contDiff_orthogonalFlow_apply (R 0).val (R 0).property.1).comp
      (hHead.prodMk contDiff_snd)
    exact (ih (Fin.tail R)).comp (hTail.prodMk hInner)

/-- The iterated derivative in the order induced by the product of flows. -/
noncomputable def dirichletAngularWord {n : ℕ} :
    {m : ℕ} → (Fin m → DirichletUnitaryField n) → (E n → ℝ) → E n → ℝ
  | 0, _, u => u
  | _m + 1, R, u => dirichletAngularDerivative (R 0).val (dirichletAngularWord (Fin.tail R) u)

/-- A local version of differentiation after a continuous linear pullback. -/
private theorem iteratedFDeriv_comp_linear_at {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : X →L[ℝ] Y) {f : Y → Z} {x : X}
    (hf : ContDiffAt ℝ ∞ f (L x)) (m : ℕ) (v : Fin m → X) :
    iteratedFDeriv ℝ m (f ∘ L) x v = iteratedFDeriv ℝ m f (L x) (fun i => L (v i)) := by
  have hOrd : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  obtain ⟨U, hU, hUF⟩ := (hf.of_le hOrd).contDiffOn (m := m) le_rfl (by simp)
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hUF.mono hVU) hV.uniqueDiffOn
    (hV.preimage L.continuous).uniqueDiffOn hxV (i := m) (by rfl)
  rw [iteratedFDerivWithin_of_isOpen _ (hV.preimage L.continuous) hxV,
    iteratedFDerivWithin_of_isOpen _ hV hxV] at he
  exact congrFun (congrArg DFunLike.coe he) v

private theorem iteratedFDeriv_comp_affine_at_zero {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : X →L[ℝ] Y) (a : Y) {f : Y → Z}
    (hf : ContDiffAt ℝ ∞ f a) (m : ℕ) (v : Fin m → X) :
    iteratedFDeriv ℝ m (fun x => f (a + L x)) 0 v =
      iteratedFDeriv ℝ m f a (fun i => L (v i)) := by
  let g (y : Y) := f (a + y)
  have hg : ContDiffAt ℝ ∞ g (L 0) := by
    have h0 : a + L 0 = a := by simp
    have hAdd : ContDiffAt ℝ ∞ (fun y : Y => a + y) (L 0) := contDiffAt_const.add contDiffAt_id
    exact ContDiffAt.comp (L 0) (h0.symm ▸ hf) hAdd
  change iteratedFDeriv ℝ m (g ∘ L) 0 v = _
  rw [iteratedFDeriv_comp_linear_at L hg, map_zero, show g = (fun y => f (a + y)) from rfl,
    iteratedFDeriv_comp_add_left, add_zero]

private noncomputable def tailParameterInclusion (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0
    (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) i)

private theorem tailParameterInclusion_apply (m : ℕ) (t : Fin m → ℝ) :
    tailParameterInclusion m t = Fin.cons 0 t := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

private theorem cons_eq_single_add_tail (m : ℕ) (s : ℝ) (t : Fin m → ℝ) :
    Fin.cons s t = Pi.single (0 : Fin (m + 1)) s + tailParameterInclusion m t := by
  rw [tailParameterInclusion_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

private theorem tailParameterInclusion_single (m : ℕ) (j : Fin m) :
    tailParameterInclusion m (Pi.single j 1) = Pi.single j.succ 1 := by
  rw [tailParameterInclusion_apply]
  funext i
  refine Fin.cases ?_ (fun l => ?_) i
  · simp
  · by_cases h : l = j
    · subst l
      simp
    · have h' : l.succ ≠ j.succ := fun he => h (Fin.succ_injective _ he)
      simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

/-- The mixed derivative in the tail parameters is the ambient iterated
derivative in the corresponding coordinate directions. -/
theorem iteratedFDeriv_tail_parameter_slice {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} {F : (Fin (m + 1) → ℝ) → X} {s : ℝ}
    (hF : ContDiffAt ℝ ∞ F (Fin.cons s 0)) :
    iteratedFDeriv ℝ m (fun t : Fin m → ℝ => F (Fin.cons s t)) 0 (fun i => Pi.single i 1) =
      iteratedFDeriv ℝ m F (Fin.cons s 0) (fun i => Pi.single i.succ 1) := by
  have hA : (fun t : Fin m → ℝ => F (Fin.cons s t)) =
      (fun t => F (Pi.single (0 : Fin (m + 1)) s + tailParameterInclusion m t)) :=
    funext fun t => congrArg F (cons_eq_single_add_tail m s t)
  have h0 : Fin.cons s (0 : Fin m → ℝ) = (Pi.single (0 : Fin (m + 1)) s : Fin (m + 1) → ℝ) := by
    rw [cons_eq_single_add_tail, map_zero, add_zero]
  rw [hA, h0, iteratedFDeriv_comp_affine_at_zero _ _ (h0 ▸ hF)]
  simp only [tailParameterInclusion_single]

private theorem derivative_first_parameter_slice {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} {F : (Fin (m + 1) → ℝ) → X} (hF : ContDiffAt ℝ ∞ F 0) :
    HasDerivAt
      (fun s : ℝ => iteratedFDeriv ℝ m F (Fin.cons s 0) (fun i => Pi.single i.succ 1))
      (iteratedFDeriv ℝ (m + 1) F 0 (fun i => Pi.single i 1)) 0 := by
  let e : Fin (m + 1) → ℝ := Pi.single 0 1
  let G (y : Fin (m + 1) → ℝ) := iteratedFDeriv ℝ m F y (fun i => Pi.single i.succ 1)
  have hOrder : (1 : ℕ∞ω) + m ≤ ∞ := by
    have h := ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + m)
    exact_mod_cast h
  have hM := hF.iteratedFDeriv_right (m := 1) hOrder
  have hEval : ContDiffAt ℝ 1 G 0 := by
    let v : Fin m → (Fin (m + 1) → ℝ) := fun i => Pi.single i.succ 1
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Fin (m + 1) → ℝ) X v
    exact L.contDiff.contDiffAt.comp 0 hM
  have hD : DifferentiableAt ℝ G 0 := hEval.differentiableAt one_ne_zero
  have h : HasDerivAt (G ∘ fun s : ℝ => s • e) (fderiv ℝ G 0 e) 0 := by
    have hS : HasDerivAt (fun s : ℝ => s • e) e 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const e
    exact HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hD.hasFDerivAt hS (zero_smul ℝ e).symm
  have hG : (G ∘ fun s : ℝ => s • e) =
      fun s => iteratedFDeriv ℝ m F (Fin.cons s 0) (fun i => Pi.single i.succ 1) := by
    funext s
    apply congrArg G
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  rw [hG] at h
  refine h.congr_deriv ?_
  rw [(hM.differentiableAt one_ne_zero).iteratedFDeriv_succ_apply_left']
  rfl

/-- Evaluation of the mixed derivative of a rotation orbit equals the
successive angular derivatives of the represented potential. -/
theorem eval_iteratedFDeriv_eq_angularWord_of_orbit {n m : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] ℝ)
    (R : Fin m → DirichletUnitaryField n) {u : E n → ℝ}
    (hu : ∀ j : ℕ, ∀ R' : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ 1 (dirichletAngularWord R' u) (closedUnitBall n))
    {W : (Fin m → ℝ) → X} (x : ClosedBall n)
    (hW : ∀ᶠ t in 𝓝 (0 : Fin m → ℝ), ContDiffAt ℝ ∞ W t ∧
      L (W t) = u (dirichletUnitaryOrbit R t x)) :
    L (iteratedFDeriv ℝ m W 0 (fun i => Pi.single i 1)) = dirichletAngularWord R u x := by
  induction m generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    exact hW.self_of_nhds.2
  | succ m ih =>
    let e (p : ℝ × (Fin m → ℝ)) : Fin (m + 1) → ℝ := Fin.cons p.1 p.2
    have hE : ContDiff ℝ ∞ e := by
      apply contDiff_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact contDiff_fst
      · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).contDiff.comp contDiff_snd
    have he₀ : e (0, 0) = 0 := by
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    have hTe : Tendsto e (𝓝 ((0 : ℝ), (0 : Fin m → ℝ))) (𝓝 0) :=
      he₀ ▸ hE.continuous.continuousAt.tendsto
    have hEW := hTe.eventually hW
    rw [nhds_prod_eq] at hEW
    obtain ⟨U, hU, V, hV, hUV⟩ := eventually_prod_iff.mp hEW
    have hV₀ := hV.self_of_nhds
    let D (s : ℝ) := iteratedFDeriv ℝ m W (Fin.cons s 0) (fun i => Pi.single i.succ 1)
    let w := dirichletAngularWord (Fin.tail R) u
    have hD : HasDerivAt D (iteratedFDeriv ℝ (m + 1) W 0 (fun i => Pi.single i 1)) 0 :=
      derivative_first_parameter_slice hW.self_of_nhds.1
    have hValues : (L ∘ D) =ᶠ[𝓝 (0 : ℝ)]
        (w ∘ fun s => orthogonalFlow (R 0).val (R 0).property.1 s x.val) := by
      filter_upwards [hU] with s hs
      let Ws (t : Fin m → ℝ) := W (Fin.cons s t)
      let y : ClosedBall n := ⟨orthogonalFlow (R 0).val (R 0).property.1 s x.val,
        orthogonalFlow_mapsTo_closedUnitBall (R 0).val (R 0).property.1 s x.property⟩
      have hSlice : ContDiff ℝ ∞ (fun t : Fin m → ℝ => e (s, t)) :=
        hE.comp (contDiff_const.prodMk contDiff_id)
      have hWs : ∀ᶠ t in 𝓝 (0 : Fin m → ℝ), ContDiffAt ℝ ∞ Ws t ∧
          L (Ws t) = u (dirichletUnitaryOrbit (Fin.tail R) t y) := by
        filter_upwards [hV] with t ht
        exact ⟨ContDiffAt.comp t (hUV hs ht).1 hSlice.contDiffAt, (hUV hs ht).2⟩
      have hI := ih (R := Fin.tail R) (W := Ws) y hWs
      change L (D s) = w y
      have hCs : ContDiffAt ℝ ∞ W (Fin.cons s (0 : Fin m → ℝ)) := (hUV hs hV₀).1
      have hEq : iteratedFDeriv ℝ m Ws 0 (fun i => Pi.single i 1) = D s :=
        iteratedFDeriv_tail_parameter_slice hCs
      exact (congrArg L hEq).symm.trans hI
    have hL := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
    have hX := hasDerivAt_orthogonalFlow_apply_zero (R 0).val (R 0).property.1 x.val
    have hDw := ((hu m (Fin.tail R)).differentiableOn one_ne_zero x.val x.property).hasFDerivWithinAt
    have hDeriv := HasFDerivWithinAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hDw hX
      (Eventually.of_forall fun t =>
        orthogonalFlow_mapsTo_closedUnitBall (R 0).val (R 0).property.1 t x.property)
      (orthogonalFlow_zero_apply (R 0).val (R 0).property.1 x.val).symm
    exact hL.deriv.symm.trans (hValues.deriv_eq.trans hDeriv.deriv)


private noncomputable def insertOrbitParameters {k m : ℕ} (e : Fin k → Fin m) :
    (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ∑ j, (ContinuousLinearMap.single (R := ℝ) (φ := fun _ : Fin m => ℝ) (e j)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j)

private theorem insertOrbitParameters_apply {k m : ℕ} (e : Fin k → Fin m)
    (t : Fin k → ℝ) (i : Fin m) :
    insertOrbitParameters e t i = ∑ j, (Pi.single (e j) (t j) : Fin m → ℝ) i := by
  simp [insertOrbitParameters, Finset.sum_apply]

private theorem insertOrbitParameters_single {k m : ℕ} (e : Fin k → Fin m) (j : Fin k) :
    insertOrbitParameters e (Pi.single j 1) = Pi.single (e j) 1 := by
  funext i
  rw [insertOrbitParameters_apply, Finset.sum_eq_single j]
  · simp
  · intro l _ h
    simp [Pi.single_eq_of_ne h]
  · simp

private theorem insertOrbitParameters_head_none {k m : ℕ}
    (e : Fin k → Fin (m + 1)) (h : ∀ j, e j ≠ 0) (t : Fin k → ℝ) :
    insertOrbitParameters e t 0 = 0 := by
  rw [insertOrbitParameters_apply]
  exact Finset.sum_eq_zero fun j _ => Pi.single_eq_of_ne (Ne.symm (h j)) _

private theorem insertOrbitParameters_tail_none {k m : ℕ}
    (e : Fin k → Fin (m + 1)) (h : ∀ j, e j ≠ 0) (t : Fin k → ℝ) :
    Fin.tail (insertOrbitParameters e t) =
      insertOrbitParameters (fun j => (e j).pred (h j)) t := by
  funext i
  simp only [Fin.tail, insertOrbitParameters_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hj : ((e j).pred (h j)).succ = e j := Fin.succ_pred _ _
  by_cases he : i = (e j).pred (h j)
  · subst i
    rw [hj]
    simp
  · have hn : i.succ ≠ e j := fun he' => he (Fin.succ_injective _ (he'.trans hj.symm))
    rw [Pi.single_eq_of_ne hn, Pi.single_eq_of_ne he]

private theorem insertOrbitParameters_head_some {k m : ℕ}
    (e : Fin (k + 1) → Fin (m + 1)) (he : StrictMono e) (h₀ : e 0 = 0)
    (t : Fin (k + 1) → ℝ) : insertOrbitParameters e t 0 = t 0 := by
  rw [insertOrbitParameters_apply, Finset.sum_eq_single 0]
  · simp [h₀]
  · intro j _ hj
    exact Pi.single_eq_of_ne (fun h => hj (he.injective (h.symm.trans h₀.symm))) _
  · simp

private theorem insertOrbitParameters_tail_some {k m : ℕ}
    (e : Fin (k + 1) → Fin (m + 1)) (he : StrictMono e) (h₀ : e 0 = 0)
    (t : Fin (k + 1) → ℝ) :
    Fin.tail (insertOrbitParameters e t) =
      insertOrbitParameters (fun j => (e j.succ).pred (fun h =>
        Fin.succ_ne_zero j (he.injective (h.trans h₀.symm)))) (Fin.tail t) := by
  funext i
  simp only [Fin.tail, insertOrbitParameters_apply, Fin.sum_univ_succ, h₀]
  rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i), zero_add]
  apply Finset.sum_congr rfl
  intro j _
  let h := fun h : e j.succ = 0 => Fin.succ_ne_zero j (he.injective (h.trans h₀.symm))
  have hj : ((e j.succ).pred h).succ = e j.succ := Fin.succ_pred _ _
  by_cases he' : i = (e j.succ).pred h
  · subst i
    rw [hj]
    simp
  · have hn : i.succ ≠ e j.succ := fun hn => he' (Fin.succ_injective _ (hn.trans hj.symm))
    rw [Pi.single_eq_of_ne hn, Pi.single_eq_of_ne he']

private theorem dirichletUnitaryOrbit_insert_parameters {n k m : ℕ}
    (R : Fin m → DirichletUnitaryField n) (e : Fin k → Fin m) (he : StrictMono e)
    (t : Fin k → ℝ) (x : E n) :
    dirichletUnitaryOrbit R (insertOrbitParameters e t) x = dirichletUnitaryOrbit (R ∘ e) t x := by
  induction m generalizing k x with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => exact Fin.elim0 (e 0)
  | succ m ih =>
    by_cases h : ∀ j, e j ≠ 0
    · let d (j : Fin k) := (e j).pred (h j)
      have hd (j : Fin k) : (d j).succ = e j := Fin.succ_pred _ _
      have hMono : StrictMono d := fun i j hij => Fin.succ_lt_succ_iff.mp (by
        rw [hd, hd]
        exact he hij)
      rw [dirichletUnitaryOrbit_succ_apply, insertOrbitParameters_head_none e h,
        insertOrbitParameters_tail_none e h, orthogonalFlow_zero_apply, ih _ d hMono]
      have hR : Fin.tail R ∘ d = R ∘ e := funext fun j => congrArg R (hd j)
      rw [hR]
    · cases k with
      | zero => exact False.elim (h fun j => Fin.elim0 j)
      | succ k =>
        push Not at h
        obtain ⟨j, hj⟩ := h
        have h₀ : e 0 = 0 := le_antisymm (hj ▸ he.monotone (Fin.zero_le j)) (Fin.zero_le _)
        let d (j : Fin k) := (e j.succ).pred
          (fun h => Fin.succ_ne_zero j (he.injective (h.trans h₀.symm)))
        have hd (j : Fin k) : (d j).succ = e j.succ := Fin.succ_pred _ _
        have hMono : StrictMono d := fun i j hij => Fin.succ_lt_succ_iff.mp (by
          rw [hd, hd]
          exact he (Fin.succ_lt_succ_iff.mpr hij))
        rw [dirichletUnitaryOrbit_succ_apply, dirichletUnitaryOrbit_succ_apply,
          insertOrbitParameters_head_some e he h₀, insertOrbitParameters_tail_some e he h₀,
          ih _ d hMono]
        have hTail : Fin.tail R ∘ d = Fin.tail (R ∘ e) :=
          funext fun j => congrArg R (hd j)
        have hFirst : (R ∘ e) 0 = R 0 := congrArg R h₀
        rw [hTail, hFirst]


/-- The mixed parameter derivative in a coordinate subspace equals the
angular word of the corresponding ordered subsequence of fields. -/
theorem eval_iteratedFDeriv_eq_angularWord_of_suborbit {n k m : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] ℝ) (R : Fin m → DirichletUnitaryField n)
    (e : Fin k → Fin m) (he : StrictMono e) {u : E n → ℝ}
    (hu : ∀ j : ℕ, ∀ R' : Fin j → DirichletUnitaryField n,
      ContDiffOn ℝ 1 (dirichletAngularWord R' u) (closedUnitBall n))
    {W : (Fin m → ℝ) → X} (x : ClosedBall n)
    (hW : ∀ᶠ t in 𝓝 (0 : Fin m → ℝ), ContDiffAt ℝ ∞ W t ∧
      L (W t) = u (dirichletUnitaryOrbit R t x)) :
    L (iteratedFDeriv ℝ k W 0 (fun i => Pi.single (e i) 1)) =
      dirichletAngularWord (R ∘ e) u x := by
  let A := insertOrbitParameters e
  have hA : Tendsto A (𝓝 0) (𝓝 0) :=
    (A.map_zero) ▸ A.continuous.continuousAt.tendsto
  have hWA : ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), ContDiffAt ℝ ∞ (W ∘ A) t ∧
      L ((W ∘ A) t) = u (dirichletUnitaryOrbit (R ∘ e) t x) := by
    filter_upwards [hA.eventually hW] with t ht
    exact ⟨ht.1.comp t A.contDiff.contDiffAt,
      ht.2.trans (congrArg u (dirichletUnitaryOrbit_insert_parameters R e he t x))⟩
  have h := eval_iteratedFDeriv_eq_angularWord_of_orbit L (R ∘ e) hu x hWA
  have hC : ContDiffAt ℝ ∞ W (A 0) := (A.map_zero).symm ▸ hW.self_of_nhds.1
  rw [iteratedFDeriv_comp_linear_at A hC, A.map_zero] at h
  simpa only [A, insertOrbitParameters_single] using h

theorem dirichletAngularWord_eq_foldr {n m : ℕ}
    (R : Fin m → DirichletUnitaryField n) (u : E n → ℝ) :
    dirichletAngularWord R u =
      (List.ofFn (fun i => (R i).val)).foldr dirichletAngularDerivative u := by
  induction m with
  | zero => simp [dirichletAngularWord]
  | succ m ih =>
    rw [dirichletAngularWord, List.ofFn_succ, List.foldr_cons, ih]
    rfl

theorem contDiffOn_dirichletAngularWord {n m : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedUnitBall n)) (R : Fin m → DirichletUnitaryField n) :
    ContDiffOn ℝ ∞ (dirichletAngularWord R u) (closedUnitBall n) := by
  have hB : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
      rw [closedUnitBall, interior_closedBall _ (by norm_num)]
      exact nonempty_ball.mpr (by norm_num))
  induction m with
  | zero => exact hu
  | succ m ih =>
    rw [dirichletAngularWord]
    exact ((ih (Fin.tail R)).fderivWithin hB
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by rw [ENat.coe_top_add_one])).clm_apply
        (R 0).val.contDiff.contDiffOn

end KEBall
