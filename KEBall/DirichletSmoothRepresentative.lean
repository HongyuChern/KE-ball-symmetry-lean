import KEBall.DirichletSmoothLimit

/-! Classical representatives of functions with all finite weak orders. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem uniformCauchySeqOn_iteratedFDeriv_dirichletSmoothApproximation_of_order
    {n N : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : HasDirichletWeakDerivativesL2 f N) (k : ℕ)
    (hk : k + 2 * (2 * n + 1) ≤ N) :
    UniformCauchySeqOn (fun j => iteratedFDeriv ℝ k (dirichletSmoothApproximation f j))
      atTop (closedUnitBall n) := by
  classical
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let F := dirichletSmoothApproximation f
  let I := Fin k → Fin (2 * n)
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.uniformity_basis_dist.mem_iff.mp hU
  let δ := ε / ((Fintype.card I : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hComponent (i : I) : ∀ᶠ p : ℕ × ℕ in atTop ×ˢ atTop, ∀ x ∈ closedUnitBall n,
      ‖iteratedFDeriv ℝ k (F p.1) x (fun s => b (i s)) -
        iteratedFDeriv ℝ k (F p.2) x (fun s => b (i s))‖ < δ := by
    let ds := List.ofFn (fun s => b (i s))
    have hLen : ds.length + 2 * (2 * n + 1) ≤ N := by
      simpa only [ds, List.length_ofFn] using hk
    have hC := uniformCauchySeqOn_iteratedLineDerivative_dirichletSmoothApproximation_of_order hn hf ds hLen
      {p | dist p.1 p.2 < δ} (Metric.uniformity_basis_dist.mem_of_mem hδ)
    filter_upwards [hC] with p hp x hx
    rw [iteratedFDeriv_eq_foldr_directions (contDiff_dirichletSmoothApproximation hf.1 p.1),
      iteratedFDeriv_eq_foldr_directions (contDiff_dirichletSmoothApproximation hf.1 p.2)]
    exact hp x hx
  have hAll := Filter.eventually_all.mpr hComponent
  filter_upwards [hAll] with p hp x hx
  apply hsub
  change dist (iteratedFDeriv ℝ k (F p.1) x) (iteratedFDeriv ℝ k (F p.2) x) < ε
  rw [dist_eq_norm]
  refine (ContinuousMultilinearMap.norm_le_sum_orthonormalBasis _ b).trans_lt ?_
  calc
    _ ≤ ∑ _ : I, δ := Finset.sum_le_sum fun i _ => (hp i x hx).le
    _ = (Fintype.card I : ℝ) * δ := by simp [nsmul_eq_mul]
    _ < ε := by dsimp only [δ]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

private theorem exists_tendstoUniformlyOn_of_uniformCauchy {α β : Type*} [UniformSpace β]
    [CompleteSpace β] [Inhabited β] {F : ℕ → α → β} {s : Set α}
    (h : UniformCauchySeqOn F atTop s) :
    ∃ g, TendstoUniformlyOn F g atTop s := by
  classical
  have hPoint (x : s) : ∃ y, Tendsto (fun j => F j x) atTop (𝓝 y) :=
    CompleteSpace.complete (h.cauchy_map x.property) |>.imp fun _ hy => hy
  choose u hu using hPoint
  let g (x : α) := if hx : x ∈ s then u ⟨x, hx⟩ else default
  exact ⟨g, h.tendstoUniformlyOn_of_tendsto fun x hx => by simpa only [g, dif_pos hx] using hu ⟨x, hx⟩⟩

/-- A single smooth approximating sequence has limits of every
Fréchet derivative uniformly on the closed ball. -/
theorem exists_dirichletSmoothApproximation_jetLimit {n : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : ∀ k, HasDirichletWeakDerivativesL2 f k) :
    ∃ P : E n → FormalMultilinearSeries ℝ (E n) ℝ,
      ∀ k, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ k (dirichletSmoothApproximation f j))
        (fun x => P x k) atTop (closedUnitBall n) := by
  have h (k : ℕ) := exists_tendstoUniformlyOn_of_uniformCauchy
    (uniformCauchySeqOn_iteratedFDeriv_dirichletSmoothApproximation_of_order hn (hf _) k le_rfl)
  choose P hP using h
  exact ⟨fun x k => P k x, hP⟩

/-- The uniform jet limit defines the representative and its closed-ball
derivatives, with the same approximation sequence at each order. -/
theorem HasDirichletWeakDerivativesL2.exists_closedUnitBall_smoothJet {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ∀ k, HasDirichletWeakDerivativesL2 f k) :
    ∃ (g : E n → ℝ) (P : E n → FormalMultilinearSeries ℝ (E n) ℝ),
      HasFTaylorSeriesUpToOn ∞ g P (closedUnitBall n) ∧ g =ᵐ[ν[n]] f ∧
      ∀ k, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ k (dirichletSmoothApproximation f j))
        (fun x => P x k) atTop (closedUnitBall n) := by
  obtain ⟨P, hP⟩ := exists_dirichletSmoothApproximation_jetLimit hn hf
  let F := dirichletSmoothApproximation f
  let g (x : E n) := (P x 0).curry0
  have hF (j : ℕ) : ContDiff ℝ ∞ (F j) := contDiff_dirichletSmoothApproximation (hf 0).1 j
  have hCont (k : ℕ) : ContinuousOn (fun x => P x k) (closedUnitBall n) :=
    (hP k).continuousOn (Eventually.frequently (Eventually.of_forall fun j =>
      ((hF j).continuous_iteratedFDeriv
        (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousOn))
  have hInt (k : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      HasFDerivAt (fun y => P y k) (P x (k + 1)).curryLeft x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E n) ℝ
    have hLim := C.isometry.uniformContinuous.comp_tendstoUniformlyOn (hP (k + 1))
    refine hasFDerivAt_of_tendstoUniformlyOn (s := unitBall n) isOpen_ball
      (hLim.mono ball_subset_closedBall) (fun j y _ => ?_)
      (fun y hy => (hP k).tendsto_at (ball_subset_closedBall hy)) hx
    have hD : Differentiable ℝ (iteratedFDeriv ℝ k (F j)) :=
      (hF j).differentiable_iteratedFDeriv (show (k : ℕ∞ω) < ∞ from
        WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
    rw [← show fderiv ℝ (iteratedFDeriv ℝ k (F j)) y = _ from
      congrFun fderiv_iteratedFDeriv y]
    exact (hD y).hasFDerivAt
  have hClosure : closure (unitBall n) = closedUnitBall n :=
    closure_ball (0 : E n) (by norm_num)
  have hTaylor : HasFTaylorSeriesUpToOn ∞ g P (closedUnitBall n) := by
    refine ⟨fun _ _ => rfl, fun k _ x hx => ?_, fun k _ => hCont k⟩
    rw [← hClosure]
    refine hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hInt k y hy).differentiableAt.differentiableWithinAt)
      (convex_ball _ _) isOpen_ball ?_ ?_
    · intro y hy
      rw [hClosure] at hy
      exact ((hCont k) y hy).mono ball_subset_closedBall
    · let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E n) ℝ
      have hL : Tendsto (fun y => (P y (k + 1)).curryLeft) (𝓝[unitBall n] x)
          (𝓝 (P x (k + 1)).curryLeft) :=
        (C.continuous.continuousAt.tendsto).comp
          (((hCont (k + 1)) x hx).mono ball_subset_closedBall)
      refine hL.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hInt k y hy).fderiv.symm
  refine ⟨g, P, hTaylor, ?_, hP⟩
  have hAe : ∀ᵐ x ∂ν[n], Tendsto (fun j => F j x) atTop (𝓝 (f x)) :=
    ae_tendsto_dilatedDirichletTranslationPairing (hf 0).1 (1 / 2) (by norm_num)
  filter_upwards [hAe, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hBall
  have h₀ := (continuousMultilinearCurryFin0 ℝ (E n) ℝ).continuous.continuousAt.tendsto.comp
    ((hP 0).tendsto_at (ball_subset_closedBall hBall))
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, F, g,
    continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.curry0_apply,
    iteratedFDeriv_zero_apply] using h₀) hx

/-- A scalar function with square-integrable weak derivatives of every
finite order has a smooth representative on the closed ball. -/
theorem HasDirichletWeakDerivativesL2.exists_contDiffOn_closedUnitBall {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ∀ k, HasDirichletWeakDerivativesL2 f k) :
    ∃ g : E n → ℝ, ContDiffOn ℝ ∞ g (closedUnitBall n) ∧ g =ᵐ[ν[n]] f := by
  obtain ⟨g, _, hTaylor, he, _⟩ := HasDirichletWeakDerivativesL2.exists_closedUnitBall_smoothJet hn hf
  exact ⟨g, hTaylor.contDiffOn, he⟩

/-- Weak derivatives through order r + 2(2n+1) give a C^r representative
on the closed ball, with uniform convergence of the mollified jets. -/
theorem HasDirichletWeakDerivativesL2.exists_closedUnitBall_finiteJet
    {n r : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : HasDirichletWeakDerivativesL2 f (r + 2 * (2 * n + 1))) :
    ∃ (g : E n → ℝ) (P : E n → FormalMultilinearSeries ℝ (E n) ℝ),
      HasFTaylorSeriesUpToOn (r : ℕ∞ω) g P (closedUnitBall n) ∧ g =ᵐ[ν[n]] f ∧
      ∀ k ≤ r, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ k (dirichletSmoothApproximation f j))
        (fun x => P x k) atTop (closedUnitBall n) := by
  classical
  have hEx (k : ℕ) (hk : k ≤ r) := exists_tendstoUniformlyOn_of_uniformCauchy
    (uniformCauchySeqOn_iteratedFDeriv_dirichletSmoothApproximation_of_order hn hf k (by omega))
  choose Q hQ using hEx
  let P (x : E n) (k : ℕ) : E n [×k]→L[ℝ] ℝ := if hk : k ≤ r then Q k hk x else 0
  have hP (k : ℕ) (hk : k ≤ r) :
      TendstoUniformlyOn (fun j => iteratedFDeriv ℝ k (dirichletSmoothApproximation f j))
        (fun x => P x k) atTop (closedUnitBall n) := by
    simpa only [P, dif_pos hk] using hQ k hk
  let F := dirichletSmoothApproximation f
  let g (x : E n) := (P x 0).curry0
  have hF (j : ℕ) : ContDiff ℝ ∞ (F j) := contDiff_dirichletSmoothApproximation hf.1 j
  have hCont (k : ℕ) (hk : k ≤ r) : ContinuousOn (fun x => P x k) (closedUnitBall n) :=
    (hP k hk).continuousOn (Eventually.frequently (Eventually.of_forall fun j =>
      ((hF j).continuous_iteratedFDeriv
        (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousOn))
  have hInt (k : ℕ) (hk : k < r) (x : E n) (hx : x ∈ unitBall n) :
      HasFDerivAt (fun y => P y k) (P x (k + 1)).curryLeft x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E n) ℝ
    have hLim := C.isometry.uniformContinuous.comp_tendstoUniformlyOn (hP (k + 1) (Nat.succ_le_of_lt hk))
    refine hasFDerivAt_of_tendstoUniformlyOn (s := unitBall n) isOpen_ball
      (hLim.mono ball_subset_closedBall) (fun j y _ => ?_)
      (fun y hy => (hP k hk.le).tendsto_at (ball_subset_closedBall hy)) hx
    have hD : Differentiable ℝ (iteratedFDeriv ℝ k (F j)) :=
      (hF j).differentiable_iteratedFDeriv (show (k : ℕ∞ω) < ∞ from
        WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
    rw [← show fderiv ℝ (iteratedFDeriv ℝ k (F j)) y = _ from
      congrFun fderiv_iteratedFDeriv y]
    exact (hD y).hasFDerivAt
  have hClosure : closure (unitBall n) = closedUnitBall n :=
    closure_ball (0 : E n) (by norm_num)
  have hTaylor : HasFTaylorSeriesUpToOn (r : ℕ∞ω) g P (closedUnitBall n) := by
    refine ⟨fun _ _ => rfl, fun k hk x hx => ?_, fun k hk => hCont k (by exact_mod_cast hk)⟩
    have hk' : k < r := by exact_mod_cast hk
    rw [← hClosure]
    refine hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hInt k hk' y hy).differentiableAt.differentiableWithinAt)
      (convex_ball _ _) isOpen_ball ?_ ?_
    · intro y hy
      rw [hClosure] at hy
      exact ((hCont k hk'.le) y hy).mono ball_subset_closedBall
    · let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E n) ℝ
      have hL : Tendsto (fun y => (P y (k + 1)).curryLeft) (𝓝[unitBall n] x)
          (𝓝 (P x (k + 1)).curryLeft) :=
        (C.continuous.continuousAt.tendsto).comp
          (((hCont (k + 1) (Nat.succ_le_of_lt hk')) x hx).mono ball_subset_closedBall)
      refine hL.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hInt k hk' y hy).fderiv.symm
  refine ⟨g, P, hTaylor, ?_, hP⟩
  have hAe : ∀ᵐ x ∂ν[n], Tendsto (fun j => F j x) atTop (𝓝 (f x)) :=
    ae_tendsto_dilatedDirichletTranslationPairing hf.1 (1 / 2) (by norm_num)
  filter_upwards [hAe, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hBall
  have h₀ := (continuousMultilinearCurryFin0 ℝ (E n) ℝ).continuous.continuousAt.tendsto.comp
    ((hP 0 (Nat.zero_le _)).tendsto_at (ball_subset_closedBall hBall))
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, F, g,
    continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.curry0_apply,
    iteratedFDeriv_zero_apply] using h₀) hx

theorem HasDirichletWeakDerivativesL2.exists_contDiffOn_closedUnitBall_finite
    {n r : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : HasDirichletWeakDerivativesL2 f (r + 2 * (2 * n + 1))) :
    ∃ g : E n → ℝ, ContDiffOn ℝ (r : ℕ∞ω) g (closedUnitBall n) ∧ g =ᵐ[ν[n]] f := by
  obtain ⟨g, _, hTaylor, he, _⟩ := hf.exists_closedUnitBall_finiteJet hn
  exact ⟨g, hTaylor.contDiffOn, he⟩

end KEBall
