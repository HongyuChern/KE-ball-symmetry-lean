import KEBall.DirichletSmoothBounds
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Uniform convergence of every derivative of the inward mollifications. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal Topology
open PshLines (shrinkingBump)

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem tendsto_integral_norm_iteratedLineDerivative_diff {n N : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : HasDirichletWeakDerivativesL2 f N) (ds : List (E n))
    (hds : ds.length + (2 * n + 1) ≤ N) :
    Tendsto (fun p : ℕ × ℕ =>
      ∫ x, ‖(ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f p.1)) x -
        (ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f p.2)) x‖ ∂ν[n])
      (atTop ×ˢ atTop) (𝓝 0) := by
  have : NeZero n := ⟨hn.ne'⟩
  let g (j : ℕ) := ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f j)
  obtain ⟨F, hF, he⟩ := (hf.of_le (by omega : ds.length ≤ N)).2 ds le_rfl
  have hAe : ∀ᵐ x ∂ν[n], Tendsto (fun j => g j x) atTop (𝓝 (F x)) :=
    ae_tendsto_iteratedLineDerivative_dilatedDirichletTranslationPairing ds (hf.of_le (by omega : ds.length ≤ N))
      hF he (1 / 2) (by norm_num)
  obtain ⟨C, hC⟩ := exists_bound_iteratedLineDerivative_dirichletSmoothApproximation_of_order hn hf ds hds
  have hCont (j : ℕ) : Continuous (g j) :=
    (iteratedLineDerivative_contDiff (contDiff_dirichletSmoothApproximation hf.1 j) ds).continuous
  let D (p : ℕ × ℕ) (x : E n) := ‖g p.1 x - g p.2 x‖
  have hMeas : ∀ p, AEStronglyMeasurable (D p) ν[n] :=
    fun p => ((hCont p.1).sub (hCont p.2)).norm.aestronglyMeasurable
  have hDom : ∀ p, ∀ᵐ x ∂ν[n], ‖D p x‖ ≤ C + C := by
    intro p
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    change ‖‖g p.1 x - g p.2 x‖‖ ≤ _
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hC _ x (ball_subset_closedBall hx))
      (hC _ x (ball_subset_closedBall hx)))
  have hLim : ∀ᵐ x ∂ν[n], Tendsto (fun p => D p x) (atTop ×ˢ atTop) (𝓝 0) := by
    filter_upwards [hAe] with x hx
    simpa only [D, Function.comp_apply, sub_self, norm_zero] using ((hx.comp tendsto_fst).sub (hx.comp tendsto_snd)).norm
  simpa only [D, g, integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (μ := ν[n]) (F := D) (f := fun _ => (0 : ℝ)) (fun _ => C + C) (Eventually.of_forall hMeas)
    (Eventually.of_forall hDom) (integrable_const _) hLim

private theorem tendsto_integral_norm_fderiv_diff_of_components {n k : ℕ}
    {g : ℕ → E n → ℝ} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (h : ∀ i : Fin k → Fin (2 * n), Tendsto (fun p : ℕ × ℕ =>
      ∫ x, ‖iteratedFDeriv ℝ k (g p.1 - g p.2) x (fun s => b (i s))‖ ∂ν[n])
      (atTop ×ˢ atTop) (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ x, ‖iteratedFDeriv ℝ k (g p.1 - g p.2) x‖ ∂ν[n])
      (atTop ×ˢ atTop) (𝓝 0) := by
  classical
  let B (p : ℕ × ℕ) (i : Fin k → Fin (2 * n)) :=
    ∫ x, ‖iteratedFDeriv ℝ k (g p.1 - g p.2) x (fun s => b (i s))‖ ∂ν[n]
  have hB : Tendsto (fun p => ∑ i, B p i) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => h i)
  refine squeeze_zero (fun p => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_) hB
  have hD : Continuous (iteratedFDeriv ℝ k (g p.1 - g p.2)) :=
    ((hg p.1).sub (hg p.2)).continuous_iteratedFDeriv
      (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hInt {u : E n → ℝ} (hu : Continuous u) : Integrable u ν[n] :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have hI (i : Fin k → Fin (2 * n)) :
      Integrable (fun x => ‖iteratedFDeriv ℝ k (g p.1 - g p.2) x (fun s => b (i s))‖) ν[n] :=
    hInt ((continuous_eval_const _).comp hD).norm
  calc
    _ ≤ ∫ x, ∑ i : Fin k → Fin (2 * n),
        ‖iteratedFDeriv ℝ k (g p.1 - g p.2) x (fun s => b (i s))‖ ∂ν[n] :=
      integral_mono (hInt hD.norm) (integrable_finsetSum _ fun i _ => hI i)
        (fun x => ContinuousMultilinearMap.norm_le_sum_orthonormalBasis _ b)
    _ = ∑ i, B p i := integral_finsetSum _ fun i _ => hI i

private theorem iteratedLineDerivative_sub {n : ℕ} {f g : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ds : List (E n)) :
    (ds.foldr (fun d D y => fderiv ℝ D y d) (f - g)) =
      (ds.foldr (fun d D y => fderiv ℝ D y d) f) -
        (ds.foldr (fun d D y => fderiv ℝ D y d) g) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.foldr_cons, ih]
      funext x
      rw [fderiv_sub ((iteratedLineDerivative_contDiff hf ds).differentiable (by simp) x)
        ((iteratedLineDerivative_contDiff hg ds).differentiable (by simp) x),
        sub_apply, Pi.sub_apply]

/-- On the closed ball every derivative of the same mollification sequence
is uniformly Cauchy. -/
theorem uniformCauchySeqOn_iteratedLineDerivative_dirichletSmoothApproximation_of_order
    {n N : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : HasDirichletWeakDerivativesL2 f N) (ds : List (E n))
    (hds : ds.length + 2 * (2 * n + 1) ≤ N) :
    UniformCauchySeqOn (fun j => ds.foldr (fun d D y => fderiv ℝ D y d)
      (dirichletSmoothApproximation f j)) atTop (closedUnitBall n) := by
  classical
  let F := dirichletSmoothApproximation f
  let g (j : ℕ) := ds.foldr (fun d D y => fderiv ℝ D y d) (F j)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have hF (j : ℕ) : ContDiff ℝ ∞ (F j) := contDiff_dirichletSmoothApproximation hf.1 j
  have hg (j : ℕ) : ContDiff ℝ ∞ (g j) := iteratedLineDerivative_contDiff (hF j) ds
  let L (k : ℕ) (p : ℕ × ℕ) := ∫ x, ‖iteratedFDeriv ℝ k (g p.1 - g p.2) x‖ ∂ν[n]
  have hL (k : ℕ) (hk : k ≤ 2 * n + 1) : Tendsto (L k) (atTop ×ˢ atTop) (𝓝 0) := by
    apply tendsto_integral_norm_fderiv_diff_of_components hg b
    intro i
    let es := List.ofFn (fun s => b (i s))
    have he (p : ℕ × ℕ) (x : E n) :
        iteratedFDeriv ℝ k (g p.1 - g p.2) x (fun s => b (i s)) =
          (es ++ ds).foldr (fun d D y => fderiv ℝ D y d) (F p.1) x -
          (es ++ ds).foldr (fun d D y => fderiv ℝ D y d) (F p.2) x := by
      have hs : ContDiff ℝ ∞ (g p.1 - g p.2) := (hg p.1).sub (hg p.2)
      rw [iteratedFDeriv_eq_foldr_directions hs, iteratedLineDerivative_sub (hg p.1) (hg p.2)]
      simp only [Pi.sub_apply, List.foldr_append, es, g]
    simp_rw [he]
    apply tendsto_integral_norm_iteratedLineDerivative_diff hn hf (es ++ ds)
    simp only [es, List.length_append, List.length_ofFn]
    omega
  let m := 2 * n
  let B (p : ℕ × ℕ) := (∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ k / k.factorial) * L k p) +
    ((2 : ℝ) ^ (m + 1) / m.factorial) * L (m + 1) p
  have hB : Tendsto B (atTop ×ˢ atTop) (𝓝 0) := by
    have hSum := tendsto_finsetSum (Finset.range (m + 1))
      (fun k hk => (hL k (by
        have h := Finset.mem_range.mp hk
        dsimp only [m] at h
        omega)).const_mul ((2 : ℝ) ^ k / k.factorial))
    simpa only [B, mul_zero, Finset.sum_const_zero, zero_add] using
      hSum.add ((hL (m + 1) le_rfl).const_mul ((2 : ℝ) ^ (m + 1) / m.factorial))
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.uniformity_basis_dist.mem_iff.mp hU
  filter_upwards [hB.eventually (gt_mem_nhds hε)] with p hp x hx
  apply hsub
  change dist (g p.1 x) (g p.2 x) < ε
  rw [dist_eq_norm]
  exact (norm_le_integral_iteratedFDeriv_closedUnitBall hn ((hg p.1).sub (hg p.2)) hx).trans_lt hp

/-- On the closed ball every derivative of the same mollification sequence
is uniformly Cauchy. -/
theorem uniformCauchySeqOn_iteratedLineDerivative_dirichletSmoothApproximation
    {n : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : ∀ k, HasDirichletWeakDerivativesL2 f k) (ds : List (E n)) :
    UniformCauchySeqOn (fun j => ds.foldr (fun d D y => fderiv ℝ D y d)
      (dirichletSmoothApproximation f j)) atTop (closedUnitBall n) :=
  uniformCauchySeqOn_iteratedLineDerivative_dirichletSmoothApproximation_of_order hn (hf _) ds le_rfl

end KEBall
