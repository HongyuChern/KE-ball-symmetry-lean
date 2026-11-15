import KEBall.DirichletAllOrderHessianLp
import KEBall.DirichletHessianLpFatou

/-! Every pure angular order of the actual potential has Hessian in every finite Lp. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem memLp_realHessian_iteratedAngularDerivative_even_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    MemLp (realHessian (dirichletInteriorAngularIterate S u k)) (2*r : ℝ≥0∞)
      ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨δ,hδ,C,hC,hBound⟩ := exists_dirichlet_iterated_difference_uniform_hessian_even_power_bound
    hn hu huS hu0 hPos hf hEq S hS k hr
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

theorem memLp_realHessian_iteratedAngularDerivative_of_C2_solution_finite {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (realHessian (dirichletInteriorAngularIterate S u k)) p
      ((volume0 n).restrict (unitBall n)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  obtain ⟨r,hr⟩ := exists_nat_gt p.toReal
  have hEven := memLp_realHessian_iteratedAngularDerivative_even_of_C2_solution
    hn hu huS hu0 hPos hf hEq S hS k (by omega : 2 ≤ r+2)
  have hrE : p < (r : ℝ≥0∞) := (ENNReal.toReal_lt_toReal hp (by simp)).mp (by simpa using hr)
  have hle : p ≤ 2*((r+2 : ℕ) : ℝ≥0∞) := hrE.le.trans (by
    exact_mod_cast (show r ≤ 2*(r+2) by omega))
  exact hEven.mono_exponent hle

end KEBall
