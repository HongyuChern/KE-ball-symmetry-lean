import KEBall.DirichletAllOrderHessianEstimate
import KEBall.DirichletBilinearNorm

/-! Arbitrarily high finite even powers of actual spatial Hessian differences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff
namespace KEBall
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2*n)) ℝ

theorem dirichlet_sum_nat_pow_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {p : ℕ} (hp : 1 ≤ p) :
    (∑ i ∈ s, a i)^p ≤ (s.card : ℝ)^(p-1) * ∑ i ∈ s, (a i)^p := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := a) (by exact_mod_cast hp : (1:ℝ) ≤ p) ha
  have he : (p:ℝ)-1 = ((p-1:ℕ):ℝ) := by rw [Nat.cast_sub hp, Nat.cast_one]
  simpa only [he, Real.rpow_natCast] using h

theorem norm_dirichlet_bilinear_nat_pow_le_entries {n p : ℕ}
    (hp : 1 ≤ p) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖H‖^p ≤ ((2*n:ℝ)^2)^(p-1) * ∑ i, ∑ j, |H (e[n] i) (e[n] j)|^p := by
  have h := dirichlet_sum_nat_pow_le (Finset.univ : Finset (Fin (2*n) × Fin (2*n)))
    (fun z => |H (e[n] z.1) (e[n] z.2)|) (fun _ _ => abs_nonneg _) hp
  simp only [Fintype.sum_prod_type, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat, ← pow_two] at h
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_dirichlet_bilinear_le_sum_entries H) p).trans h

noncomputable def dirichletComplexBilinearEntryCLM {n : ℕ} (i j : Fin (2*n)) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (e[n] j)).comp
    (ContinuousLinearMap.apply ℝ (E n →L[ℝ] ℝ) (e[n] i)))

theorem dirichletComplexBilinearEntryCLM_apply {n : ℕ} (i j : Fin (2*n))
    (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletComplexBilinearEntryCLM i j H = (H (e[n] i) (e[n] j) : ℂ) := rfl

theorem norm_dirichletComplexBilinearEntryCLM_le_one {n : ℕ} (i j : Fin (2*n)) :
    ‖dirichletComplexBilinearEntryCLM i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro H
  simpa only [dirichletComplexBilinearEntryCLM_apply, Complex.norm_real, Real.norm_eq_abs, one_mul]
    using abs_dirichlet_bilinear_entry_le_norm H i j

theorem exists_dirichlet_spatial_hessian_difference_uniform_even_power_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
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
  obtain ⟨δ, hδ, B, hB, hBound⟩ := exists_dirichlet_all_order_uniform_hessian_bound
    hn hu huS hu0 hPos hf hEq S hS q
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

end KEBall
