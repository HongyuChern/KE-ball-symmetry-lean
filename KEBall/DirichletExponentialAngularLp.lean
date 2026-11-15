import KEBall.DirichletAngularWordFiniteLpJets
import KEBall.DirichletExponentialTensorLp

/-! Every actual mixed angular word has Hessian and lower jets in every finite Lp for the exponential equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2*n)) ℝ

theorem memLp_realHessian_iteratedAngularDerivative_even_of_exponential_C2_solution {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    MemLp (realHessian (dirichletInteriorAngularIterate S u k)) (2*r : ℝ≥0∞)
      ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨δ,hδ,C,hC,hBound⟩ := exists_dirichlet_exponential_iterated_difference_uniform_hessian_even_power_bound
    hn hu huS hu0 hPos a c hEq S hS k hr
  let t (m : ℕ) : ℝ := 1 / ((m:ℝ)+1)
  let v (m : ℕ) := dirichletIteratedOrthogonalDifference (orthogonalFlow S hS (t m)) (t m) u k
  have htPos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have ht : Tendsto t atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htPunct : Tendsto t atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun m => (htPos m).ne')⟩
  have hSmall : ∀ᶠ m in atTop, |t m| < δ :=
    ht.abs.eventually_lt_const (show |(0:ℝ)| < δ by simpa using hδ)
  have hLimit (x : E n) (hx : x ∈ unitBall n) (a b : E n) :
      Tendsto (fun m => dirichletWithinRealHessian (v m) x a b) atTop
        (𝓝 (realHessian (dirichletInteriorAngularIterate S u k) x a b)) := by
    simp only [dirichletWithinRealHessian_eq_on_ball _ hx]
    exact (tendsto_realHessian_iteratedOrthogonalDifference_flow_entry huS S hS hx a b k).comp htPunct
  have h := memLp_realHessian_of_dirichlet_power_energy_limit hn (by omega : 0 < 2*r)
    (contDiffOn_dirichletInteriorAngularIterate huS S k)
    (fun m => contDiffOn_dirichletIteratedOrthogonalDifference (orthogonalFlow S hS (t m)) (t m) hu k)
    (fun x hx i j => hLimit x hx _ _) hC (hSmall.mono (fun m hm => hBound _ (htPos m).ne' hm))
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.1

theorem memLp_realHessian_iteratedAngularDerivative_of_exponential_C2_solution_finite {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (realHessian (dirichletInteriorAngularIterate S u k)) p
      ((volume0 n).restrict (unitBall n)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  obtain ⟨r,hr⟩ := exists_nat_gt p.toReal
  have hEven := memLp_realHessian_iteratedAngularDerivative_even_of_exponential_C2_solution
    hn hu huS hu0 hPos a c hEq S hS k (by omega : 2 ≤ r+2)
  have hrE : p < (r : ℝ≥0∞) := (ENNReal.toReal_lt_toReal hp (by simp)).mp (by simpa using hr)
  have hle : p ≤ 2*((r+2 : ℕ) : ℝ≥0∞) := hrE.le.trans (by
    exact_mod_cast (show r ≤ 2*(r+2) by omega))
  exact hEven.mono_exponent hle

theorem memLp_withinHessian_angularWord_of_exponential_C2_solution_finite {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (dirichletWithinRealHessian (dirichletAngularWord R u))
      p ((volume0 n).restrict (unitBall n)) := by
  let v : dirichletInteriorSmoothSpace n := ⟨u, huS⟩
  let ev : Module.End ℝ (dirichletInteriorSmoothSpace n) →ₗ[ℝ] dirichletInteriorSmoothSpace n :=
    { toFun := fun A => A v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P := (dirichletInteriorHessianLpSpace n p).comap ev
  have hPure : dirichletLiePowerSpan (dirichletSkewAngularLieSpace n) m ≤ P := by
    apply Submodule.span_le.mpr
    rintro A ⟨Q, hQ, k, _, rfl⟩
    rcases Submodule.mem_map.mp hQ with ⟨S, hS, rfl⟩
    change MemLp (realHessian ((dirichletAngularEnd S ^ k) v).val) p _
    have h := memLp_realHessian_iteratedAngularDerivative_of_exponential_C2_solution_finite
      hn hu huS hu0 hPos a c hEq S hS k p hp
    refine MemLp.ae_eq ?_ h
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    have he : ((dirichletAngularEnd S ^ k) v).val =ᶠ[𝓝 x]
        dirichletInteriorAngularIterate S u k := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact dirichletAngularEnd_pow_eq_on_ball S v k hy
    exact he.fderiv.fderiv_eq.symm
  let w := List.ofFn (fun i => dirichletAngularEnd (R i).val)
  have hw : ∀ A ∈ w, A ∈ dirichletSkewAngularLieSpace n := by
    intro A hA
    rcases List.mem_ofFn.mp hA with ⟨i, rfl⟩
    exact dirichletAngularEnd_mem_skewLieSpace (R i).val (R i).property.1
  have hword := dirichlet_lie_word_mem_span_powers (dirichletSkewAngularLieSpace n)
    (fun A hA B hB => dirichletSkewAngularLieSpace_commutator A hA B hB) w hw
  have hl : w.length = m := List.length_ofFn
  rw [hl] at hword
  have hMem := hPure hword
  change MemLp (realHessian (w.prod v).val) p ((volume0 n).restrict (unitBall n)) at hMem
  refine MemLp.ae_eq ?_ hMem
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  rw [dirichletWithinRealHessian_eq_on_ball _ hx]
  have he : (w.prod v).val =ᶠ[𝓝 x] dirichletAngularWord R u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularEnd_prod_eq_word_on_ball R v hy
  exact he.fderiv.fderiv_eq


theorem memLp_angularWord_lower_jets_of_exponential_C2_solution_finite {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (dirichletAngularWord R u) p ((volume0 n).restrict (unitBall n)) ∧
    MemLp (fderiv ℝ (dirichletAngularWord R u)) p ((volume0 n).restrict (unitBall n)) := by
  have hH {j : ℕ} (Q : Fin j → DirichletUnitaryField n) :
      MemLp (realHessian (dirichletAngularWord Q u)) p ((volume0 n).restrict (unitBall n)) := by
    refine MemLp.ae_eq ?_ (memLp_withinHessian_angularWord_of_exponential_C2_solution_finite
      hn hu huS hu0 hPos a c hEq Q p hp)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact dirichletWithinRealHessian_eq_on_ball _ hx
  induction m with
  | zero =>
    refine ⟨dirichlet_memLp_of_continuousOn hn hu.continuousOn p, ?_⟩
    have hB : UniqueDiffOn ℝ (closedUnitBall n) :=
      uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
        rw [closedUnitBall, interior_closedBall _ (by norm_num)]
        exact nonempty_ball.mpr (by norm_num))
    have hC := (hu.fderivWithin (m := 1) hB (by norm_num)).continuousOn
    refine MemLp.ae_eq ?_ (dirichlet_memLp_of_continuousOn hn hC p)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact fderivWithin_of_mem_nhds (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  | succ m ih =>
    exact memLp_dirichletAngularDerivative_and_fderiv
      (contDiffOn_dirichletAngularWord_interior huS (Fin.tail R)) (R 0).val p
      (ih (Fin.tail R)).2 (hH (Fin.tail R))

theorem hasDirichletFiniteLpJets_two_angularWord_of_exponential_C2_solution {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets (unitBall n) ((volume0 n).restrict (unitBall n)) 2
      (dirichletAngularWord R u) := by
  apply hasDirichletFiniteLpJets_two_of_hessian (contDiffOn_dirichletAngularWord_interior huS R)
  · intro p hp
    exact (memLp_angularWord_lower_jets_of_exponential_C2_solution_finite hn hu huS hu0 hPos a c hEq R p hp).1
  · intro p hp
    exact (memLp_angularWord_lower_jets_of_exponential_C2_solution_finite hn hu huS hu0 hPos a c hEq R p hp).2
  · intro p hp
    refine MemLp.ae_eq ?_ (memLp_withinHessian_angularWord_of_exponential_C2_solution_finite
      hn hu huS hu0 hPos a c hEq R p hp)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact dirichletWithinRealHessian_eq_on_ball _ hx

end KEBall
