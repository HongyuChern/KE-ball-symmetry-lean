import KEBall.DirichletAllOrderHessianLp
import KEBall.DirichletExponentialAllOrderHessian

/-! All finite even powers of the actual Hessian differences for exponential density. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2*n)) ℝ

theorem exists_dirichlet_exponential_spatial_hessian_difference_uniform_even_power_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {k r : ℕ} (hk : 0 < k) (hr : 2 ≤ r) :
    ∃ δ > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t
        (dirichletWithinRealHessian u) k x‖^(2*r) ∂volume0 n) ≤ C := by
  classical
  let q := k*r
  have hq : 2 ≤ q := by dsimp [q]; nlinarith
  have hkq : k < q := by dsimp [q]; nlinarith
  obtain ⟨A, hA, hTame⟩ := exists_dirichlet_hessian_monomial_tame_bound hn hq
    (Finset.univ : Finset (Fin r)) (fun _ => k) (fun _ _ => hkq)
    (by simp [q, Nat.mul_comm]) hu huS hu0 S hS (Λ := 1) zero_le_one (ε := 1) zero_lt_one
  obtain ⟨δ, hδ, B, hB, hBound⟩ := exists_dirichlet_exponential_all_order_uniform_hessian_bound
    hn hu huS hu0 hPos a c hEq S hS q
  let C₀ : ℝ := B+A*((q:ℝ)*B)+A
  let N : ℝ := (2*n:ℝ)^2
  let C : ℝ := N^(2*r-1)*N*C₀
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC : 0 ≤ C := by dsimp [C,N]; positivity
  refine ⟨δ,hδ,C,hC,?_⟩
  intro t ht htδ
  let R := orthogonalFlow S hS t
  let H := dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k
  have hH : ContinuousOn H (closedUnitBall n) :=
    continuousOn_dirichletIteratedFieldDifference R t (continuousOn_dirichletWithinRealHessian hu) k
  have hLow : (∑ j ∈ Finset.range q, dirichletFlowHessianEnergy u S hS j t) ≤ (q:ℝ)*B := by
    calc
      _ ≤ ∑ _j ∈ Finset.range q, B := Finset.sum_le_sum (fun j hj =>
        hBound t ht htδ j (Nat.le_of_lt (Finset.mem_range.mp hj)))
      _ = _ := by simp
  have hEntry (i j : Fin (2*n)) :
      (∫ x in unitBall n, |H x (e[n] i) (e[n] j)|^(2*r) ∂volume0 n) ≤ C₀ := by
    have hh := hTame t ht (fun _ => LinearIsometryEquiv.refl ℝ (E n))
      (fun _ => dirichletComplexBilinearEntryCLM i j)
      (fun _ _ => norm_dirichletComplexBilinearEntryCLM_le_one i j)
    simp only [LinearIsometryEquiv.refl, dirichletComplexBilinearEntryCLM_apply,
      Complex.norm_real, Real.norm_eq_abs, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, one_mul] at hh
    exact hh.trans (add_le_add (add_le_add (hBound t ht htδ q le_rfl)
      (mul_le_mul_of_nonneg_left hLow hA)) le_rfl)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {g : E n → ℝ} (hg : ContinuousOn g (closedUnitBall n)) :
      IntegrableOn g (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hg 1).integrable le_rfl
  have hEC (i j : Fin (2*n)) : ContinuousOn (fun x => |H x (e[n] i) (e[n] j)|^(2*r))
      (closedUnitBall n) := ((hH.clm_apply continuousOn_const).clm_apply continuousOn_const).abs.pow _
  have hSumC : ContinuousOn (fun x => ∑ i, ∑ j, |H x (e[n] i) (e[n] j)|^(2*r))
      (closedUnitBall n) := continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ => hEC i j))
  have hI := setIntegral_mono_on (hInt (hH.norm.pow (2*r))) (hInt (hSumC.const_mul (N^(2*r-1))))
    measurableSet_ball (fun x _ => norm_dirichlet_bilinear_nat_pow_le_entries (by omega) (H x))
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt (hEC i j)))] at hI
  simp_rw [integral_finsetSum _ (fun j _ => hInt (hEC _ j))] at hI
  refine hI.trans ?_
  calc
    _ ≤ N^(2*r-1) * (∑ _i : Fin (2*n), ∑ _j : Fin (2*n), C₀) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEntry i j)))
        (by dsimp [N]; positivity)
    _ = C := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat]; dsimp [C,N]; ring

theorem exists_dirichlet_exponential_all_spatial_hessian_differences_uniform_even_power_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    ∃ δ > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ j ≤ k,
      (∫ x in unitBall n, ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t
        (dirichletWithinRealHessian u) j x‖^(2*r) ∂volume0 n) ≤ C := by
  induction k with
  | zero =>
    refine ⟨1,zero_lt_one,∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖^(2*r) ∂volume0 n,
      integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _),?_⟩
    intro t ht htδ j hj
    have hj0 : j=0 := by omega
    subst j
    exact le_rfl
  | succ k ih =>
    obtain ⟨δ₀,hδ₀,B,hB,hPrev⟩ := ih
    obtain ⟨δ₁,hδ₁,A,hA,hNew⟩ := exists_dirichlet_exponential_spatial_hessian_difference_uniform_even_power_bound
      hn hu huS hu0 hPos a c hEq S hS (Nat.succ_pos k) hr
    refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,max B A,hB.trans (le_max_left _ _),?_⟩
    intro t ht htδ j hj
    by_cases hjk : j ≤ k
    · exact (hPrev t ht (htδ.trans_le (min_le_left _ _)) j hjk).trans (le_max_left _ _)
    · have he : j=k+1 := by omega
      subst j
      exact (hNew t ht (htδ.trans_le (min_le_right _ _))).trans (le_max_right _ _)

theorem exists_dirichlet_exponential_iterated_difference_uniform_hessian_even_power_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    ∃ δ > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ‖dirichletWithinRealHessian
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x‖^(2*r)
          ∂volume0 n) ≤ C := by
  obtain ⟨δ,hδ,B,hB,hBound⟩ := exists_dirichlet_exponential_all_spatial_hessian_differences_uniform_even_power_bound
    hn hu huS hu0 hPos a c hEq S hS k hr
  let A : ℝ := (1+2*‖S‖)^k
  let K : ℝ := A^(2*r)*(k+1:ℝ)^(2*r-1)
  have hK : 0 ≤ K := by dsimp [K,A]; positivity
  refine ⟨δ,hδ,K*((k+1:ℝ)*B),by positivity,?_⟩
  intro t ht htδ
  let R := orthogonalFlow S hS t
  let F (j : ℕ) (x : E n) := ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) j x‖
  have hFC (j : ℕ) : ContinuousOn (F j) (closedUnitBall n) :=
    (continuousOn_dirichletIteratedFieldDifference R t (continuousOn_dirichletWithinRealHessian hu) j).norm
  have hSumC : ContinuousOn (fun x => ∑ j ∈ Finset.range (k+1), (F j x)^(2*r))
      (closedUnitBall n) := continuousOn_finsetSum _ (fun j _ => (hFC j).pow _)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {g : E n → ℝ} (hg : ContinuousOn g (closedUnitBall n)) :
      IntegrableOn g (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hg 1).integrable le_rfl
  have hHC := continuousOn_dirichletWithinRealHessian (contDiffOn_dirichletIteratedOrthogonalDifference R t hu k)
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x‖^(2*r) ≤
        K*∑ j ∈ Finset.range (k+1), (F j x)^(2*r) := by
    have hN := pow_le_pow_left₀ (norm_nonneg _)
      (norm_dirichlet_iterated_difference_hessian_le_tensor_differences hu S hS ht k (ball_subset_closedBall hx)) (2*r)
    rw [mul_pow] at hN
    have hSum := dirichlet_sum_nat_pow_le (Finset.range (k+1)) (fun j => F j x)
      (fun j _ => norm_nonneg _) (by omega : 1 ≤ 2*r)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hSum
    exact hN.trans ((mul_le_mul_of_nonneg_left hSum (by dsimp [A]; positivity : 0 ≤ A^(2*r))).trans_eq
      (by dsimp [K]; ring))
  have hI := setIntegral_mono_on (hInt (hHC.norm.pow (2*r))) (hInt (hSumC.const_mul K)) measurableSet_ball hPoint
  rw [integral_const_mul, integral_finsetSum (Finset.range (k+1))
    (f := fun j x => (F j x)^(2*r)) (fun j _ => hInt ((hFC j).pow (2*r)))] at hI
  refine hI.trans (mul_le_mul_of_nonneg_left ?_ hK)
  calc
    _ ≤ ∑ _j ∈ Finset.range (k+1), B := Finset.sum_le_sum (fun j hj =>
      hBound t ht htδ j (by have := Finset.mem_range.mp hj; omega))
    _ = (k+1:ℝ)*B := by simp

end KEBall
