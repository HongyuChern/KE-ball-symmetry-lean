import KEBall.DirichletSobolevDensity

/-! Sobolev estimates for the pointwise product on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions ENNReal NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem integral_norm_le_L2_of_ae_eq {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} {F : DirichletBallL2 n ℝ} (hF : F =ᵐ[ν[n]] f) :
    (∫ x, ‖f x‖ ∂ν[n]) ≤ ‖F‖ := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have h : (∫ x, ‖f x‖ ∂ν[n]) = ∫ x, ‖F x‖ ∂ν[n] :=
    integral_congr_ae (hF.symm.mono (fun _ hx => congrArg norm hx))
  rw [h, integral_norm_eq_lintegral_enorm (Lp.memLp F).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.memLp F).aestronglyMeasurable)

private theorem norm_dirichletJetGraph_snd_apply_le {n k : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)}
    (z : dirichletSobolevJetGraph (k := k) b) (i : DirichletJetIndex n k) :
    ‖z.val.2 i‖ ≤ ‖z‖ := by
  exact ((pi_norm_le_iff_of_nonneg (norm_nonneg z.val.2)).mp le_rfl i).trans
    (norm_snd_le z.val)

/-- The coordinate derivative of a smooth function is controlled by the
Sobolev graph norm whenever one has at least 2n+1 spare derivative orders. -/
theorem exists_norm_iteratedLineDerivative_le_dirichletSobolevJetOfSmooth {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (f : E n → ℝ) (hf : ContDiff ℝ (∞ : ℕ∞ω) f)
      (is : List (Fin (2 * n))), is.length + (2 * n + 1) ≤ k →
        ∀ x ∈ closedUnitBall n,
          ‖((is.map b).foldr (fun d D y => fderiv ℝ D y d) f) x‖ ≤
            C * ‖dirichletSobolevJetOfSmooth (k := k) hn b hf‖ := by
  classical
  let m := 2 * n
  let A (j : ℕ) : ℝ := Fintype.card (Fin j → Fin (2 * n))
  let c (j : ℕ) : ℝ := (2 : ℝ) ^ j / j.factorial
  let D : ℝ := (2 : ℝ) ^ (m + 1) / m.factorial
  let C : ℝ := (∑ j ∈ Finset.range (m + 1), c j * A j) + D * A (m + 1)
  have hC : 0 ≤ C := by dsimp [C, c, A, D]; positivity
  refine ⟨C, hC, fun k f hf is hLen x hx => ?_⟩
  let g := (is.map b).foldr (fun d D y => fderiv ℝ D y d) f
  let z := dirichletSobolevJetOfSmooth (k := k) hn b hf
  have hg : ContDiff ℝ (∞ : ℕ∞ω) g := iteratedLineDerivative_contDiff hf _
  have hJ (j : ℕ) (hj : j ≤ m + 1) (ι : Fin j → Fin (2 * n)) :
      (∫ y, ‖iteratedFDeriv ℝ j g y (fun s => b (ι s))‖ ∂ν[n]) ≤ ‖z‖ := by
    let ls := List.ofFn ι ++ is
    have hls : ls.length ≤ k := by
      simp only [ls, List.length_append, List.length_ofFn]
      dsimp only [m] at hj
      omega
    let i : DirichletJetIndex n k := ⟨⟨ls.length, Nat.lt_succ_of_le hls⟩, ls.get⟩
    have he : dirichletJetDirections b i = (List.ofFn (fun s => b (ι s))) ++ is.map b := by
      change List.ofFn ((b : Fin (2 * n) → E n) ∘ ls.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
      simp only [ls, List.map_append, List.map_ofFn, Function.comp_def]
    have hF := dirichletSobolevJetOfSmooth_snd_ae (k := k) hn b hf i
    rw [he, List.foldr_append] at hF
    simp_rw [iteratedFDeriv_eq_foldr_directions hg]
    exact (integral_norm_le_L2_of_ae_eq hn hF).trans (norm_dirichletJetGraph_snd_apply_le z i)
  have hA (j : ℕ) (hj : j ≤ m + 1) :
      (∫ y, ‖iteratedFDeriv ℝ j g y‖ ∂ν[n]) ≤ A j * ‖z‖ := by
    have hc : Continuous (iteratedFDeriv ℝ j g) :=
      hg.continuous_iteratedFDeriv (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
    have hInt {w : E n → ℝ} (hw : Continuous w) : Integrable w ν[n] :=
      (hw.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
        ball_subset_closedBall
    have hI (i : Fin j → Fin (2 * n)) :
        Integrable (fun y => ‖iteratedFDeriv ℝ j g y (fun s => b (i s))‖) ν[n] :=
      hInt ((continuous_eval_const _).comp hc).norm
    calc
      _ ≤ ∫ y, ∑ i : Fin j → Fin (2 * n),
        ‖iteratedFDeriv ℝ j g y (fun s => b (i s))‖ ∂ν[n] :=
        integral_mono (hInt hc.norm) (integrable_finsetSum _ fun i _ => hI i)
          (fun y => ContinuousMultilinearMap.norm_le_sum_orthonormalBasis _ b)
      _ = ∑ i : Fin j → Fin (2 * n), ∫ y,
          ‖iteratedFDeriv ℝ j g y (fun s => b (i s))‖ ∂ν[n] :=
        integral_finsetSum _ fun i _ => hI i
      _ ≤ ∑ _ : Fin j → Fin (2 * n), ‖z‖ := Finset.sum_le_sum fun i _ => hJ j hj i
      _ = _ := by simp [A, nsmul_eq_mul]
  change ‖g x‖ ≤ C * ‖z‖
  refine (norm_le_integral_iteratedFDeriv_closedUnitBall hn hg hx).trans ?_
  change (∑ j ∈ Finset.range (m + 1), c j * ∫ y, ‖iteratedFDeriv ℝ j g y‖ ∂ν[n]) +
    D * ∫ y, ‖iteratedFDeriv ℝ (m + 1) g y‖ ∂ν[n] ≤ _
  calc
    _ ≤ (∑ j ∈ Finset.range (m + 1), c j * (A j * ‖z‖)) + D * (A (m + 1) * ‖z‖) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (hA j (Finset.mem_range.mp hj).le) (by dsimp [c]; positivity)
      · exact mul_le_mul_of_nonneg_left (hA _ le_rfl) (by dsimp [D]; positivity)
    _ = _ := by
      simp only [C, add_mul, Finset.sum_mul, mul_assoc]

private noncomputable def lineDerivatives {n : ℕ} (ds : List (E n)) (f : E n → ℝ) :
    E n → ℝ :=
  ds.foldr (fun d D y => fderiv ℝ D y d) f

private def leibnizDirections {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | d :: ds => ((leibnizDirections ds).map (fun p => (d :: p.1, p.2))) ++
    ((leibnizDirections ds).map (fun p => (p.1, d :: p.2)))

private theorem leibnizDirections_lengths {α : Type*} {ds : List α}
    {p : List α × List α} (hp : p ∈ leibnizDirections ds) :
    p.1.length + p.2.length = ds.length := by
  induction ds generalizing p with
  | nil =>
      have he : p = ([], []) := by simpa [leibnizDirections] using hp
      simp [he]
  | cons d ds ih =>
      simp only [leibnizDirections, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      all_goals have h := ih hq; simp only [List.length_cons]; omega

private theorem leibnizDirections_length {α : Type*} (ds : List α) :
    (leibnizDirections ds).length = 2 ^ ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [leibnizDirections, List.length_append, List.length_map, List.length_cons, ih, pow_succ]
      omega

private theorem fderiv_list_sum {n : ℕ} {α : Type*} (l : List α)
    (f : α → E n → ℝ) (hf : ∀ i, ContDiff ℝ (∞ : ℕ∞ω) (f i)) (x d : E n) :
    fderiv ℝ (fun y => (l.map (fun i => f i y)).sum) x d =
      (l.map (fun i => fderiv ℝ (f i) x d)).sum := by
  have hCont (l : List α) : ContDiff ℝ (∞ : ℕ∞ω) (fun y => (l.map (fun i => f i y)).sum) := by
    induction l with
    | nil => exact contDiff_const
    | cons i l ih => exact (hf i).add ih
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [fderiv_fun_add ((hf i).differentiable (by simp) x)
        ((hCont l).differentiable (by simp) x), add_apply, ih]

private theorem list_sum_map_add {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map (fun i => f i + g i)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem lineDerivatives_mul {n : ℕ} {f g : E n → ℝ}
    (hf : ContDiff ℝ (∞ : ℕ∞ω) f) (hg : ContDiff ℝ (∞ : ℕ∞ω) g) (ds : List (E n)) (x : E n) :
    lineDerivatives ds (f * g) x =
      ((leibnizDirections ds).map (fun p => lineDerivatives p.1 f x * lineDerivatives p.2 g x)).sum := by
  induction ds generalizing x with
  | nil => simp [lineDerivatives, leibnizDirections]
  | cons d ds ih =>
      change fderiv ℝ (lineDerivatives ds (f * g)) x d = _
      rw [funext ih, fderiv_list_sum]
      · simp only [leibnizDirections, List.map_append, List.map_map, List.sum_append, Function.comp_def]
        rw [← list_sum_map_add]
        congr 1
        apply List.map_congr_left
        intro p _
        have hfP : DifferentiableAt ℝ (lineDerivatives p.1 f) x :=
          (iteratedLineDerivative_contDiff hf _).differentiable (by simp) x
        have hgP : DifferentiableAt ℝ (lineDerivatives p.2 g) x :=
          (iteratedLineDerivative_contDiff hg _).differentiable (by simp) x
        rw [fderiv_fun_mul hfP hgP, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
        change lineDerivatives p.1 f x * lineDerivatives (d :: p.2) g x +
          lineDerivatives p.2 g x * lineDerivatives (d :: p.1) f x = _
        ring
      · intro p
        exact (iteratedLineDerivative_contDiff hf _).mul (iteratedLineDerivative_contDiff hg _)

private theorem leibnizDirections_map {α β : Type*} (f : α → β) (ds : List α) :
    leibnizDirections (ds.map f) =
      (leibnizDirections ds).map (fun p => (p.1.map f, p.2.map f)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, leibnizDirections, ih, List.map_append, List.map_map, Function.comp_def]

private theorem integral_sq_mul_le_of_bound {n : ℕ} (hn : 0 < n)
    {f g : E n → ℝ} (hf : Continuous f) (hg : Continuous g)
    {F G : DirichletBallL2 n ℝ} (hF : F =ᵐ[ν[n]] fun x => f x * g x)
    (hG : G =ᵐ[ν[n]] g)
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ x ∈ closedUnitBall n, ‖f x‖ ≤ C) :
    ‖F‖ ≤ C * ‖G‖ := by
  have : NeZero n := ⟨hn.ne'⟩
  have normSq (w : DirichletBallL2 n ℝ) :
      ‖w‖ ^ 2 = ∫ x, (w x) ^ 2 ∂ν[n] := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [Real.inner_apply, pow_two]
  have hI {w : E n → ℝ} (hw : Continuous w) : Integrable w ν[n] :=
    (hw.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have hLeft : ‖F‖ ^ 2 = ∫ x, (f x * g x) ^ 2 ∂ν[n] := by
    rw [normSq]
    exact integral_congr_ae (hF.mono fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
  have hRight : ‖G‖ ^ 2 = ∫ x, g x ^ 2 ∂ν[n] := by
    rw [normSq]
    exact integral_congr_ae (hG.mono fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, hLeft, hRight, ← integral_const_mul]
  apply integral_mono_ae (hI ((hf.mul hg).pow 2)) ((hI (hg.pow 2)).const_mul _)
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := pow_le_pow_left₀ (norm_nonneg _) (hBound x (ball_subset_closedBall hx)) 2
  change f x ^ 2 ≤ C ^ 2
  simpa only [Real.norm_eq_abs, sq_abs] using h

private theorem exists_L2_of_continuous_dirichlet {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : Continuous f) :
    ∃ F : DirichletBallL2 n ℝ, F =ᵐ[ν[n]] f := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hf.continuousOn
  have hLp : MemLp f 2 ν[n] := by
    refine MemLp.of_bound hf.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact hC x (ball_subset_closedBall hx)
  exact ⟨hLp.toLp f, MemLp.coeFn_toLp hLp⟩

private theorem exists_L2_of_list_sum {n : ℕ} {α : Type*} (l : List α)
    (f : α → E n → ℝ) (M : ℝ)
    (h : ∀ i ∈ l, ∃ F : DirichletBallL2 n ℝ, F =ᵐ[ν[n]] f i ∧ ‖F‖ ≤ M) :
    ∃ F : DirichletBallL2 n ℝ, F =ᵐ[ν[n]] (fun x => (l.map (fun i => f i x)).sum) ∧
      ‖F‖ ≤ l.length * M := by
  induction l with
  | nil =>
      refine ⟨0, ?_, by simp⟩
      change ((0 : DirichletBallL2 n ℝ) : E n → ℝ) =ᵐ[ν[n]] (0 : E n → ℝ)
      exact Lp.coeFn_zero _ _ _
  | cons i l ih =>
      obtain ⟨F, hF, hFM⟩ := h i (List.mem_cons_self ..)
      obtain ⟨G, hG, hGM⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      refine ⟨F + G, ?_, ?_⟩
      · filter_upwards [Lp.coeFn_add F G, hF, hG] with x hx hFx hGx
        simp only [hx, Pi.add_apply, hFx, hGx, List.map_cons, List.sum_cons]
      · refine (norm_add_le _ _).trans ((add_le_add hFM hGM).trans_eq ?_)
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- For k at least twice the number of derivative orders used for the
uniform estimate, multiplication is bounded on smooth Sobolev jets. -/
theorem exists_norm_dirichletSobolevJetOfSmooth_mul_le {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hk : 2 * (2 * n + 1) ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : E n → ℝ) (hf : ContDiff ℝ (∞ : ℕ∞ω) f)
      (hg : ContDiff ℝ (∞ : ℕ∞ω) g),
      ‖dirichletSobolevJetOfSmooth (k := k) hn b (hf.mul hg)‖ ≤
        C * ‖dirichletSobolevJetOfSmooth (k := k) hn b hf‖ *
          ‖dirichletSobolevJetOfSmooth (k := k) hn b hg‖ := by
  obtain ⟨C, hC, hCest⟩ := exists_norm_iteratedLineDerivative_le_dirichletSobolevJetOfSmooth hn b
  refine ⟨(2 : ℝ) ^ k * C, by positivity, fun f g hf hg => ?_⟩
  let F := dirichletSobolevJetOfSmooth (k := k) hn b hf
  let G := dirichletSobolevJetOfSmooth (k := k) hn b hg
  let FG := dirichletSobolevJetOfSmooth (k := k) hn b (hf.mul hg)
  let M := C * ‖F‖ * ‖G‖
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hC (norm_nonneg _)) (norm_nonneg _)
  have hTerm (is js : List (Fin (2 * n))) (hLen : is.length + js.length ≤ k) :
      ∃ R : DirichletBallL2 n ℝ, (R =ᵐ[ν[n]] fun x =>
        lineDerivatives (is.map b) f x * lineDerivatives (js.map b) g x) ∧ ‖R‖ ≤ M := by
    let fi := lineDerivatives (is.map b) f
    let gj := lineDerivatives (js.map b) g
    have hfi : Continuous fi := (iteratedLineDerivative_contDiff hf _).continuous
    have hgj : Continuous gj := (iteratedLineDerivative_contDiff hg _).continuous
    let i : DirichletJetIndex n k := ⟨⟨is.length, by omega⟩, is.get⟩
    let j : DirichletJetIndex n k := ⟨⟨js.length, by omega⟩, js.get⟩
    have hi : dirichletJetDirections b i = is.map b := by
      change List.ofFn ((b : Fin (2 * n) → E n) ∘ is.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    have hj : dirichletJetDirections b j = js.map b := by
      change List.ofFn ((b : Fin (2 * n) → E n) ∘ js.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    have hF := dirichletSobolevJetOfSmooth_snd_ae (k := k) hn b hf i
    have hG := dirichletSobolevJetOfSmooth_snd_ae (k := k) hn b hg j
    rw [hi] at hF
    rw [hj] at hG
    obtain ⟨R, hR⟩ := exists_L2_of_continuous_dirichlet hn (hfi.mul hgj)
    refine ⟨R, hR, ?_⟩
    by_cases hSmall : is.length + (2 * n + 1) ≤ k
    · exact (integral_sq_mul_le_of_bound hn hfi hgj hR hG (by positivity)
        (hCest k f hf is hSmall)).trans
        (mul_le_mul_of_nonneg_left (norm_dirichletJetGraph_snd_apply_le G j) (by positivity))
    · have hSmall' : js.length + (2 * n + 1) ≤ k := by omega
      have hR' : R =ᵐ[ν[n]] fun x => gj x * fi x :=
        hR.trans (Eventually.of_forall fun x => mul_comm _ _)
      calc
        ‖R‖ ≤ C * ‖G‖ * ‖F.val.2 i‖ :=
          integral_sq_mul_le_of_bound hn hgj hfi hR' hF (by positivity) (hCest k g hg js hSmall')
        _ ≤ C * ‖G‖ * ‖F‖ :=
          mul_le_mul_of_nonneg_left (norm_dirichletJetGraph_snd_apply_le F i) (by positivity)
        _ = M := by dsimp only [M]; ring
  have hAll (is : List (Fin (2 * n))) (hLen : is.length ≤ k)
      (R : DirichletBallL2 n ℝ)
      (hR : R =ᵐ[ν[n]] lineDerivatives (is.map b) (f * g)) :
      ‖R‖ ≤ (2 : ℝ) ^ k * M := by
    let l := leibnizDirections is
    let D (p : List (Fin (2 * n)) × List (Fin (2 * n))) (x : E n) :=
      lineDerivatives (p.1.map b) f x * lineDerivatives (p.2.map b) g x
    obtain ⟨S, hS, hB⟩ := exists_L2_of_list_sum l D M fun p hp =>
      hTerm p.1 p.2 ((leibnizDirections_lengths hp).trans_le hLen)
    have hEq : R = S := by
      apply Lp.ext
      filter_upwards [hR, hS] with x hx hy
      rw [hx, hy, lineDerivatives_mul hf hg, leibnizDirections_map]
      simp only [List.map_map, Function.comp_def, l, D]
    rw [hEq]
    refine hB.trans ?_
    dsimp only [l]
    rw [leibnizDirections_length, Nat.cast_pow, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hLen) hM
  have hNorm : ‖FG‖ ≤ (2 : ℝ) ^ k * M := by
    change ‖FG.val‖ ≤ _
    apply norm_prod_le_iff.mpr
    refine ⟨hAll [] (by simp) FG.val.1 (dirichletSobolevJetOfSmooth_fst_ae hn b (hf.mul hg)), ?_⟩
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    let is := List.ofFn i.2
    have hLen : is.length ≤ k := by simpa only [is, List.length_ofFn] using Nat.le_of_lt_succ i.1.isLt
    have hi : dirichletJetDirections b i = is.map b := by
      simp only [dirichletJetDirections, is, List.map_ofFn, Function.comp_def]
    have he := dirichletSobolevJetOfSmooth_snd_ae hn b (hf.mul hg) i
    rw [hi] at he
    exact hAll is hLen _ he
  exact hNorm.trans_eq (by dsimp only [M]; ring)

private theorem dirichletSobolevJetOfSmooth_sub {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {f g : E n → ℝ} (hf : ContDiff ℝ (∞ : ℕ∞ω) f) (hg : ContDiff ℝ (∞ : ℕ∞ω) g) :
    dirichletSobolevJetOfSmooth (k := k) hn b (hf.sub hg) =
      dirichletSobolevJetOfSmooth hn b hf - dirichletSobolevJetOfSmooth hn b hg := by
  apply dirichletSobolevJetGraph_fst_injective hn b
  let F := (dirichletSobolevJetOfSmooth (k := k) hn b hf).val.1
  let G := (dirichletSobolevJetOfSmooth (k := k) hn b hg).val.1
  change (dirichletSobolevJetOfSmooth (k := k) hn b (hf.sub hg)).val.1 = F - G
  apply Lp.ext
  filter_upwards [dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hf.sub hg),
    dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b hf,
    dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b hg, Lp.coeFn_sub F G]
    with x hfg hf' hg' hSub
  change _ = F x - G x at hSub
  change F x = f x at hf'
  change G x = g x at hg'
  rw [hfg, hSub, hf', hg']

private theorem dirichletSobolevJetOfSmooth_product_sub {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f g p q : E n → ℝ}
    (hf : ContDiff ℝ (∞ : ℕ∞ω) f) (hg : ContDiff ℝ (∞ : ℕ∞ω) g)
    (hp : ContDiff ℝ (∞ : ℕ∞ω) p) (hq : ContDiff ℝ (∞ : ℕ∞ω) q) :
    dirichletSobolevJetOfSmooth (k := k) hn b (hf.mul hg) - dirichletSobolevJetOfSmooth hn b (hp.mul hq) =
      dirichletSobolevJetOfSmooth hn b ((hf.sub hp).mul hg) +
        dirichletSobolevJetOfSmooth hn b (hp.mul (hg.sub hq)) := by
  apply dirichletSobolevJetGraph_fst_injective hn b
  let F := (dirichletSobolevJetOfSmooth (k := k) hn b (hf.mul hg)).val.1
  let G := (dirichletSobolevJetOfSmooth (k := k) hn b (hp.mul hq)).val.1
  let P := (dirichletSobolevJetOfSmooth (k := k) hn b ((hf.sub hp).mul hg)).val.1
  let Q := (dirichletSobolevJetOfSmooth (k := k) hn b (hp.mul (hg.sub hq))).val.1
  change F - G = P + Q
  have hF : F =ᵐ[ν[n]] f * g := dirichletSobolevJetOfSmooth_fst_ae hn b (hf.mul hg)
  have hG : G =ᵐ[ν[n]] p * q := dirichletSobolevJetOfSmooth_fst_ae hn b (hp.mul hq)
  have hP : P =ᵐ[ν[n]] (f - p) * g := dirichletSobolevJetOfSmooth_fst_ae hn b ((hf.sub hp).mul hg)
  have hQ : Q =ᵐ[ν[n]] p * (g - q) := dirichletSobolevJetOfSmooth_fst_ae hn b (hp.mul (hg.sub hq))
  apply Lp.ext
  filter_upwards [hF, hG, hP, hQ, Lp.coeFn_sub F G, Lp.coeFn_add P Q]
    with x hFx hGx hPx hQx hSub hAdd
  rw [hSub, hAdd]
  simp only [Pi.sub_apply, Pi.add_apply, hFx, hGx, hPx, hQx, Pi.mul_apply]
  ring

/-- Pointwise multiplication of two H^k functions stays in H^k and is
bounded in the Sobolev graph norm. -/
theorem exists_dirichletSobolevJetGraph_product {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hk : 2 * (2 * n + 1) ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : dirichletSobolevJetGraph (k := k) b,
      ∃ z : dirichletSobolevJetGraph (k := k) b,
        (z.val.1 =ᵐ[ν[n]] fun x => v.val.1 x * w.val.1 x) ∧ ‖z‖ ≤ C * ‖v‖ * ‖w‖ := by
  obtain ⟨C, hC, hEst⟩ := exists_norm_dirichletSobolevJetOfSmooth_mul_le hn b hk
  refine ⟨C, hC, fun v w => ?_⟩
  let f := dirichletSmoothApproximation (v.val.1 : E n → ℝ)
  let g := dirichletSmoothApproximation (w.val.1 : E n → ℝ)
  have hf (j : ℕ) : ContDiff ℝ (∞ : ℕ∞ω) (f j) :=
    contDiff_dirichletSmoothApproximation (Lp.memLp v.val.1) j
  have hg (j : ℕ) : ContDiff ℝ (∞ : ℕ∞ω) (g j) :=
    contDiff_dirichletSmoothApproximation (Lp.memLp w.val.1) j
  let V (j : ℕ) := dirichletSobolevJetOfSmooth (k := k) hn b (hf j)
  let W (j : ℕ) := dirichletSobolevJetOfSmooth (k := k) hn b (hg j)
  let Z (j : ℕ) := dirichletSobolevJetOfSmooth (k := k) hn b ((hf j).mul (hg j))
  have hV : Tendsto V atTop (𝓝 v) := tendsto_dirichletSobolevJetOfSmoothApproximation hn b v
  have hW : Tendsto W atTop (𝓝 w) := tendsto_dirichletSobolevJetOfSmoothApproximation hn b w
  have hDiff (i j : ℕ) : ‖Z i - Z j‖ ≤ C * ‖V i - V j‖ * ‖W i‖ +
      C * ‖V j‖ * ‖W i - W j‖ := by
    change ‖dirichletSobolevJetOfSmooth (k := k) hn b ((hf i).mul (hg i)) -
      dirichletSobolevJetOfSmooth hn b ((hf j).mul (hg j))‖ ≤ _
    rw [dirichletSobolevJetOfSmooth_product_sub hn b (hf i) (hg i) (hf j) (hg j)]
    apply (norm_add_le _ _).trans
    have h₁ := hEst _ _ ((hf i).sub (hf j)) (hg i)
    have h₂ := hEst _ _ (hf j) ((hg i).sub (hg j))
    rw [dirichletSobolevJetOfSmooth_sub hn b (hf i) (hf j)] at h₁
    rw [dirichletSobolevJetOfSmooth_sub hn b (hg i) (hg j)] at h₂
    exact add_le_add h₁ h₂
  have hCauchy : CauchySeq Z := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    rw [← prod_atTop_atTop_eq]
    have hv₁ : Tendsto (fun p : ℕ × ℕ => V p.1) (atTop ×ˢ atTop) (𝓝 v) :=
      hV.comp tendsto_fst
    have hv₂ : Tendsto (fun p : ℕ × ℕ => V p.2) (atTop ×ˢ atTop) (𝓝 v) :=
      hV.comp tendsto_snd
    have hw₁ : Tendsto (fun p : ℕ × ℕ => W p.1) (atTop ×ˢ atTop) (𝓝 w) :=
      hW.comp tendsto_fst
    have hw₂ : Tendsto (fun p : ℕ × ℕ => W p.2) (atTop ×ˢ atTop) (𝓝 w) :=
      hW.comp tendsto_snd
    have hLim : Tendsto (fun p : ℕ × ℕ => C * ‖V p.1 - V p.2‖ * ‖W p.1‖ +
        C * ‖V p.2‖ * ‖W p.1 - W p.2‖) (atTop ×ˢ atTop) (𝓝 0) := by
      simpa only [sub_self, norm_zero, mul_zero, zero_mul, add_zero] using
        (((hv₁.sub hv₂).norm.const_mul C).mul hw₁.norm).add
          ((hv₂.norm.const_mul C).mul (hw₁.sub hw₂).norm)
    exact squeeze_zero (fun _ => dist_nonneg) (fun p => by
      rw [dist_eq_norm]
      exact hDiff p.1 p.2) hLim
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨z, ?_, le_of_tendsto_of_tendsto hz.norm ((hV.norm.const_mul C).mul hW.norm)
    (Eventually.of_forall fun j => hEst _ _ (hf j) (hg j))⟩
  have hFirst : Tendsto (fun j => (Z j).val.1) atTop (𝓝 z.val.1) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.tendsto.comp hz
  obtain ⟨φ, hφ, hAe⟩ := (tendstoInMeasure_of_tendsto_Lp hFirst).exists_seq_tendsto_ae
  have hfAe := ae_tendsto_dilatedDirichletTranslationPairing (Lp.memLp v.val.1) (1 / 2) (by norm_num)
  have hgAe := ae_tendsto_dilatedDirichletTranslationPairing (Lp.memLp w.val.1) (1 / 2) (by norm_num)
  have hZae : ∀ᵐ x ∂ν[n], ∀ j, (Z j).val.1 x = f j x * g j x :=
    ae_all_iff.mpr fun j => dirichletSobolevJetOfSmooth_fst_ae hn b ((hf j).mul (hg j))
  filter_upwards [hAe, hfAe, hgAe, hZae] with x hZ hfX hgX hZX
  exact tendsto_nhds_unique hZ (((hfX.mul hgX).comp hφ.tendsto_atTop).congr
    (fun j => (hZX (φ j)).symm))

/-- Pointwise multiplication extends to a bounded bilinear map on the
finite-order Sobolev graph. -/
theorem exists_dirichletSobolevJetGraph_mulCLM {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hk : 2 * (2 * n + 1) ≤ k) :
    ∃ B : dirichletSobolevJetGraph (k := k) b →L[ℝ] dirichletSobolevJetGraph (k := k) b →L[ℝ]
        dirichletSobolevJetGraph (k := k) b,
      ∀ v w, (B v w).val.1 =ᵐ[ν[n]] fun x => v.val.1 x * w.val.1 x := by
  classical
  let H := dirichletSobolevJetGraph (k := k) b
  obtain ⟨C, hC, h⟩ := exists_dirichletSobolevJetGraph_product hn b hk
  choose P hP hBound using h
  have hAdd (u v w : H) : P (u + v) w = P u w + P v w := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    change (P (u + v) w).val.1 = (P u w).val.1 + (P v w).val.1
    apply Lp.ext
    filter_upwards [hP (u + v) w, hP u w, hP v w,
      Lp.coeFn_add u.val.1 v.val.1, Lp.coeFn_add (P u w).val.1 (P v w).val.1]
      with x hL hU hV huv hR
    change ((u + v : H).val.1 : E n → ℝ) x = _ at huv
    rw [hL, hR, huv]
    simp only [Pi.add_apply, hU, hV, add_mul]
  have hSmul (a : ℝ) (u w : H) : P (a • u) w = a • P u w := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    change (P (a • u) w).val.1 = a • (P u w).val.1
    apply Lp.ext
    filter_upwards [hP (a • u) w, hP u w,
      Lp.coeFn_smul a u.val.1, Lp.coeFn_smul a (P u w).val.1] with x hL hU hu hR
    change ((a • u : H).val.1 : E n → ℝ) x = _ at hu
    rw [hL, hR, hu]
    simp only [Pi.smul_apply, hU, smul_eq_mul, mul_assoc]
  have hComm (u w : H) : P u w = P w u := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [hP u w, hP w u] with x hu hw
    rw [hu, hw, mul_comm]
  let L₁ (u : H) : H →ₗ[ℝ] H :=
    { toFun := P u
      map_add' := fun v w => by
        calc
          P u (v + w) = P (v + w) u := hComm u (v + w)
          _ = P v u + P w u := hAdd v w u
          _ = P u v + P u w := congrArg₂ (· + ·) (hComm v u) (hComm w u)
      map_smul' := fun a v => by
        change P u (a • v) = a • P u v
        calc
          P u (a • v) = P (a • v) u := hComm u (a • v)
          _ = a • P v u := hSmul a v u
          _ = a • P u v := congrArg (a • ·) (hComm v u) }
  let L : H →ₗ[ℝ] H →ₗ[ℝ] H :=
    { toFun := L₁
      map_add' := fun u v => LinearMap.ext (hAdd u v)
      map_smul' := fun a u => LinearMap.ext (hSmul a u) }
  let B := L.mkContinuous₂ C hBound
  exact ⟨B, hP⟩

end KEBall
