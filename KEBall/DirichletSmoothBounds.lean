import KEBall.DirichletDerivativeNorm
import KEBall.DirichletDilationConvergence

/-! Uniform bounds on the closed ball for the smooth approximating sequence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal Topology
open PshLines (translationPairing contDiff_translationPairing shrinkingBump shrinkingBump_rOut_le
  tendsto_shrinkingBump_rOut)

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

noncomputable def dirichletSmoothApproximation {n : ℕ} (f : E n → ℝ) (j : ℕ) (x : E n) : ℝ :=
  let φ := shrinkingBump (E := E n) (1 / 2) (by norm_num) j
  translationPairing ν[n] f (φ.normed (volume0 n)) ((1 - φ.rOut) • x)

theorem contDiff_dirichletSmoothApproximation {n : ℕ} {f : E n → ℝ} (hf : MemLp f 2 ν[n])
    (j : ℕ) : ContDiff ℝ ∞ (dirichletSmoothApproximation f j) := by
  let φ := shrinkingBump (E := E n) (1 / 2) (by norm_num) j
  have hScale : ContDiff ℝ ∞ (fun x : E n => (1 - φ.rOut) • x) :=
    (contDiff_id (𝕜 := ℝ) (E := E n)).const_smul (1 - φ.rOut)
  exact (contDiff_translationPairing (hf.locallyIntegrable (by norm_num))
    φ.hasCompactSupport_normed φ.contDiff_normed).comp hScale

private theorem integrableOn_unitBall_of_continuous {n : ℕ} {f : E n → ℝ}
    (hf : Continuous f) : Integrable f ν[n] :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
    ball_subset_closedBall

private theorem integral_norm_le_one_add_integral_sq {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : Continuous f) :
    (∫ x, ‖f x‖ ∂ν[n]) ≤ 1 + ∫ x, f x ^ 2 ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have hSq : Integrable (fun x => f x ^ 2) ν[n] :=
    integrableOn_unitBall_of_continuous (hf.pow 2)
  calc
    _ ≤ ∫ x, 1 + f x ^ 2 ∂ν[n] := by
      apply integral_mono (integrableOn_unitBall_of_continuous hf.norm)
        ((integrable_const (μ := ν[n]) (1 : ℝ)).add hSq)
      intro x
      change ‖f x‖ ≤ 1 + f x ^ 2
      rw [Real.norm_eq_abs]
      calc
        |f x| ≤ 1 + |f x| ^ 2 := by nlinarith [sq_nonneg (|f x| - 1)]
        _ = _ := by rw [sq_abs]
    _ = _ := by
      rw [integral_add (integrable_const (μ := ν[n]) (1 : ℝ)) hSq,
        integral_const, probReal_univ, one_smul]

/-- Uniform integral bounds on each coordinate derivative give a uniform
pointwise bound for the sequence on the closed ball. -/
private theorem exists_bound_of_directional_integral_bounds {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (g : ℕ → E n → ℝ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hB : ∀ k ≤ 2 * n + 1, ∀ i : Fin k → Fin (2 * n), ∃ C : ℝ, ∀ j,
      (∫ x, ‖iteratedFDeriv ℝ k (g j) x (fun s => b (i s))‖ ∂ν[n]) ≤ C) :
    ∃ C : ℝ, ∀ j, ∀ x ∈ closedUnitBall n, ‖g j x‖ ≤ C := by
  classical
  choose C hC using hB
  let M (k : ℕ) : ℝ :=
    if hk : k ≤ 2 * n + 1 then ∑ i : Fin k → Fin (2 * n), C k hk i else 0
  have hM (k : ℕ) (hk : k ≤ 2 * n + 1) (j : ℕ) :
      (∫ x, ‖iteratedFDeriv ℝ k (g j) x‖ ∂ν[n]) ≤ M k := by
    have hD : Continuous (iteratedFDeriv ℝ k (g j)) :=
      (hg j).continuous_iteratedFDeriv
        (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hI (i : Fin k → Fin (2 * n)) :
        Integrable (fun x => ‖iteratedFDeriv ℝ k (g j) x (fun s => b (i s))‖) ν[n] :=
      integrableOn_unitBall_of_continuous ((continuous_eval_const _).comp hD).norm
    calc
      _ ≤ ∫ x, ∑ i : Fin k → Fin (2 * n),
        ‖iteratedFDeriv ℝ k (g j) x (fun s => b (i s))‖ ∂ν[n] := by
          apply integral_mono (integrableOn_unitBall_of_continuous hD.norm)
            (integrable_finsetSum _ fun i _ => hI i)
          intro x
          exact ContinuousMultilinearMap.norm_le_sum_orthonormalBasis _ b
      _ = ∑ i : Fin k → Fin (2 * n),
          ∫ x, ‖iteratedFDeriv ℝ k (g j) x (fun s => b (i s))‖ ∂ν[n] :=
        integral_finsetSum _ fun i _ => hI i
      _ ≤ M k := by
        dsimp only [M]
        rw [dif_pos hk]
        exact Finset.sum_le_sum fun i _ => hC k hk i j
  let m := 2 * n
  refine ⟨(∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ k / k.factorial) * M k) +
    ((2 : ℝ) ^ (m + 1) / m.factorial) * M (m + 1), fun j x hx => ?_⟩
  refine (norm_le_integral_iteratedFDeriv_closedUnitBall hn (hg j) hx).trans ?_
  apply add_le_add
  · apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hM k (by simpa [m] using (Finset.mem_range.mp hk).le) j)
      (by positivity)
  · exact mul_le_mul_of_nonneg_left (hM _ le_rfl j) (by positivity)

private theorem exists_integral_bound_approximation {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length) :
    ∃ C : ℝ, ∀ j, (∫ x, ‖ds.foldr (fun d D y => fderiv ℝ D y d)
      (dirichletSmoothApproximation f j) x‖ ∂ν[n]) ≤ C := by
  obtain ⟨F, hF, he⟩ := hf.2 ds le_rfl
  have hI : 0 ≤ ∫ x, F x ^ 2 ∂ν[n] := integral_nonneg fun _ => sq_nonneg _
  refine ⟨1 + (2 : ℝ) ^ (2 * n) * ∫ x, F x ^ 2 ∂ν[n], fun j => ?_⟩
  let φ := shrinkingBump (E := E n) (1 / 2) (by norm_num) j
  let a := 1 - φ.rOut
  have hφ : φ.rOut ≤ (1 : ℝ) / 2 := shrinkingBump_rOut_le _ _ _
  have ha₀ : (1 : ℝ) / 2 ≤ a := by dsimp only [a]; linarith
  have ha : 0 < a := (by norm_num : (0 : ℝ) < 1 / 2).trans_le ha₀
  have hA : φ.rOut + a ≤ 1 := by dsimp only [a]; linarith
  have hBound := setIntegral_sq_iteratedLineDerivative_dilatedMollification_le φ ha hA ds
    hf hF he
  have hInv : (a ^ (2 * n))⁻¹ ≤ (2 : ℝ) ^ (2 * n) := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr ha.le) (by
      simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) ha₀) _
  have hD := (iteratedLineDerivative_contDiff
    (contDiff_dirichletSmoothApproximation hf.1 j) ds).continuous
  refine (integral_norm_le_one_add_integral_sq hn hD).trans (add_le_add_right ?_ 1)
  exact hBound.trans (mul_le_mul_of_nonneg_right hInv hI)

/-- Every finite directional derivative of the same smooth approximations
is bounded uniformly on the closed ball. -/
theorem exists_bound_iteratedLineDerivative_dirichletSmoothApproximation_of_order {n N : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : HasDirichletWeakDerivativesL2 f N) (ds : List (E n))
    (hds : ds.length + (2 * n + 1) ≤ N) :
    ∃ C : ℝ, ∀ j, ∀ x ∈ closedUnitBall n,
      ‖ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f j) x‖ ≤ C := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let g (j : ℕ) := ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f j)
  have hg (j : ℕ) : ContDiff ℝ ∞ (g j) := iteratedLineDerivative_contDiff
    (contDiff_dirichletSmoothApproximation hf.1 j) ds
  apply exists_bound_of_directional_integral_bounds hn b g hg
  intro k hk i
  let es := List.ofFn (fun s => b (i s))
  have hLen : (es ++ ds).length ≤ N := by
    simp only [es, List.length_append, List.length_ofFn]
    omega
  obtain ⟨C, hC⟩ := exists_integral_bound_approximation hn (es ++ ds)
    (hf.of_le hLen)
  refine ⟨C, fun j => ?_⟩
  simp_rw [iteratedFDeriv_eq_foldr_directions (hg j)]
  simpa only [es, List.foldr_append, g] using hC j

/-- Every finite directional derivative of the same smooth approximations
is bounded uniformly on the closed ball. -/
theorem exists_bound_iteratedLineDerivative_dirichletSmoothApproximation {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ∀ k, HasDirichletWeakDerivativesL2 f k) (ds : List (E n)) :
    ∃ C : ℝ, ∀ j, ∀ x ∈ closedUnitBall n,
      ‖ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f j) x‖ ≤ C :=
  exists_bound_iteratedLineDerivative_dirichletSmoothApproximation_of_order hn (hf _) ds le_rfl

end KEBall
