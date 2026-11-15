import KEBall.DirichletHigherAngularHessianLimit
import KEBall.DirichletAngularWithinL2
import KEBall.DirichletLogDensityAllOrderHessian

/-! Every pure angular order of the same actual potential has an L2 Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem sum_dirichlet_bilinear_entries_sq_le_norm {n : ℕ}
    (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    (∑ i, ∑ j, (H (e[n] i) (e[n] j)) ^ 2) ≤ (2 * n : ℝ) ^ 2 * ‖H‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), ‖H‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_dirichlet_bilinear_entry_le_norm H i j) 2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring

theorem integral_dirichlet_hessian_entries_sq_le_norm {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    (∫ x in unitBall n, ∑ i, ∑ j,
      (dirichletWithinRealHessian u x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
      (2 * n : ℝ) ^ 2 * (∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖ ^ 2 ∂volume0 n) := by
  have hH := continuousOn_dirichletWithinRealHessian hu
  have hSum : ContinuousOn (fun x => ∑ i, ∑ j,
      (dirichletWithinRealHessian u x (e[n] i) (e[n] j)) ^ 2) (closedUnitBall n) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((hH.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have h := setIntegral_mono_on (hInt hSum) (hInt ((hH.norm.pow 2).const_mul ((2 * n : ℝ) ^ 2)))
    measurableSet_ball (fun x _ => sum_dirichlet_bilinear_entries_sq_le_norm (dirichletWithinRealHessian u x))
  rw [integral_const_mul] at h
  exact h

theorem memLp_realHessian_iteratedAngularDerivative_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    MemLp (realHessian (dirichletInteriorAngularIterate S u k))
      2 ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨δ, hδ, C, hC, hBound⟩ :=
    exists_dirichlet_orthogonal_iterated_difference_uniform_hessian_bound hn hu huS hu0 hPos hf hEq S hS k
  let t (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let v (m : ℕ) := dirichletIteratedOrthogonalDifference (orthogonalFlow S hS (t m)) (t m) u k
  have htPos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have ht : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htPunct : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun m => (htPos m).ne')⟩
  have hSmall : ∀ᶠ m in atTop, |t m| < δ :=
    ht.abs.eventually_lt_const (show |(0 : ℝ)| < δ by simpa using hδ)
  have hw := contDiffOn_dirichletInteriorAngularIterate huS S k
  have hv (m : ℕ) : ContDiffOn ℝ 2 (v m) (closedUnitBall n) :=
    contDiffOn_dirichletIteratedOrthogonalDifference _ _ hu k
  have hLimit (x : E n) (hx : x ∈ unitBall n) (i j : Fin (2 * n)) :
      Tendsto (fun m => dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) atTop
        (𝓝 (realHessian (dirichletInteriorAngularIterate S u k) x (e[n] i) (e[n] j))) := by
    simp_rw [dirichletWithinRealHessian_eq_on_ball _ hx]
    exact (tendsto_realHessian_iteratedOrthogonalDifference_flow_entry huS S hS hx (e[n] i) (e[n] j) k).comp htPunct
  apply (memLp_realHessian_of_dirichlet_discrete_energy_limit hn hw hv hLimit
    (mul_nonneg (sq_nonneg (2 * n : ℝ)) hC) ?_).1
  filter_upwards [hSmall] with m hm
  exact (integral_dirichlet_hessian_entries_sq_le_norm hn (hv m)).trans
    (mul_le_mul_of_nonneg_left (hBound (t m) (htPos m).ne' hm) (sq_nonneg _))

theorem dirichletAngularDerivative_iterate_eq_on_ball {n : ℕ}
    (S : E n →L[ℝ] E n) (u : E n → ℝ) (k : ℕ) {x : E n} (hx : x ∈ unitBall n) :
    (dirichletAngularDerivative S)^[k] u x = dirichletInteriorAngularIterate S u k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', dirichletAngularDerivative_eq_fderiv_on_ball S _ hx]
    have he : (dirichletAngularDerivative S)^[k] u =ᶠ[𝓝 x] dirichletInteriorAngularIterate S u k := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact ih hy
    rw [he.fderiv_eq]
    rfl

theorem memLp_withinHessian_iteratedAngularDerivative_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    MemLp (dirichletWithinRealHessian ((dirichletAngularDerivative S)^[k] u))
      2 ((volume0 n).restrict (unitBall n)) := by
  have h := memLp_realHessian_iteratedAngularDerivative_of_C2_solution hn hu huS hu0 hPos hf hEq S hS k
  refine MemLp.ae_eq ?_ h
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  rw [dirichletWithinRealHessian_eq_on_ball _ hx]
  have he : (dirichletAngularDerivative S)^[k] u =ᶠ[𝓝 x] dirichletInteriorAngularIterate S u k := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularDerivative_iterate_eq_on_ball S u k hy
  exact he.fderiv.fderiv_eq.symm

theorem exists_dirichlet_closedBall_limit_with_all_pure_angular_hessian_L2
    {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ w : E n → ℝ,
      TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      ∀ S : E n →L[ℝ] E n, star S = -S → ∀ k : ℕ,
        MemLp (dirichletWithinRealHessian ((dirichletAngularDerivative S)^[k] w))
          2 ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨w, hUw, hw, hwS, hw0, hP, hD, hDiscrete⟩ :=
    exists_dirichlet_closedBall_limit_with_all_order_discrete_hessian hn hg ht hT hu hu0 huP hEq
  refine ⟨w, hUw, hw, hwS, hw0, hP, hD, ?_⟩
  intro S hS k
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀ * g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  exact memLp_withinHessian_iteratedAngularDerivative_of_C2_solution
    (by omega : 0 < n) hw hwS hw0 hP hf hD S hS k

end KEBall
