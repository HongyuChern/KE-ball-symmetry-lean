import KEBall.DirichletPointwiseHarnack
import KEBall.DirichletAnnularComparison
import KEBall.DirichletCofactorSourceCorrection

/-!
# Pointwise weak Harnack with a bounded source

The correction is `S / (4 * n * c) * (R^2 - |x-x₀|^2)`.
Thus the loss is quadratic in the radius, with the actual real dimension
`2 * n` and the project's cofactor normalization retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem dirichlet_realHessian_add_const {n : ℕ} (q : E n → ℝ) (a : ℝ) (x : E n) :
    realHessian (fun y => q y + a) x = realHessian q x := by
  have he : fderiv ℝ (fun y => q y + a) = fderiv ℝ q := by
    funext y
    exact fderiv_add_const a
  rw [realHessian, he]
  rfl

theorem dirichletBilinearContraction_sourceQuadratic {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (A : E n →L[ℝ] E n)
    (a R : ℝ) (z x : E n) :
    dirichletBilinearContraction b A (realHessian (dirichletSourceQuadratic a R z) x) =
      -(2 * a) * ∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i) := by
  have he : dirichletSourceQuadratic a R z = (-a) • dirichletQuadraticBarrier R z := by
    ext y
    simp only [dirichletSourceQuadratic, dirichletQuadraticBarrier, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : ContDiffAt ℝ 2 (dirichletQuadraticBarrier R z) x :=
    ((contDiff_dirichletQuadraticBarrier R z).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  rw [he, dirichlet_realHessian_smul_C2 hq]
  change dirichletHessianContractionLinearMap b A
    ((-a) • realHessian (dirichletQuadraticBarrier R z) x) = _
  rw [map_smul, smul_eq_mul]
  change -a * dirichletBilinearContraction b A (realHessian (dirichletQuadraticBarrier R z) x) = _
  rw [dirichletBilinearContraction_quadraticBarrier]
  ring

theorem exists_uniform_smooth_cofactor_source_harnack {n : ℕ} (hn : 2 ≤ n)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
      (∀ x ∈ unitBall n, ∀ v : E n,
        c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (q : E n → ℝ), SmoothNear (closedUnitBall n) q → ∀ S : ℝ, 0 ≤ S →
        (∀ x ∈ unitBall n,
          dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x) ≤ S) →
        ∀ (x₀ : E n) (R : ℝ), 0 < R → closedBall x₀ R ⊆ unitBall n →
          (∀ x ∈ ball x₀ R, 0 ≤ q x) → ∀ y ∈ ball x₀ (R / 4),
            (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4), q x) ≤
              C * (q y + S / (4 * n * c) * R ^ 2) := by
  obtain ⟨C, hC, hH⟩ := exists_uniform_smooth_cofactor_pointwise_harnack hn hc hK
  refine ⟨C, hC, ?_⟩
  intro u hu huP hNorm hEll q hq S hS hL x₀ R hR hBall hPos y hy
  let a : ℝ := S / (4 * n * c)
  let s : E n → ℝ := dirichletSourceQuadratic a R x₀
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 ≤ a := div_nonneg hS (by positivity)
  have haS : 2 * a * (2 * n : ℝ) * c = S := by
    dsimp [a]
    field_simp [ne_of_gt hn0, hc.ne']
    <;> ring
  have hs : ContDiff ℝ ∞ s := contDiff_dirichletSourceQuadratic a R x₀
  have hSub : ball x₀ (R / 4) ⊆ closedBall x₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hqC : ContinuousOn q (closedBall x₀ R) := by
    intro x hx
    exact (hq.contDiffAt (ball_subset_closedBall (hBall hx))).continuousAt.continuousWithinAt
  have hqInt : IntegrableOn q (ball x₀ (R / 4)) :=
    (hqC.integrableOn_compact (isCompact_closedBall x₀ R)).mono_set hSub
  have hEst (ε : ℝ) (hε : 0 < ε) :
      (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4), q x) ≤
        C * (q y + ε + a * R ^ 2) := by
    let v : E n → ℝ := fun x => q x + ε + s x
    have hv : SmoothNear (closedUnitBall n) v := by
      obtain ⟨U, hU, hSubU, hqU⟩ := hq
      exact ⟨U, hU, hSubU, (hqU.add contDiffOn_const).add hs.contDiffOn⟩
    have hLv (x : E n) (hx : x ∈ unitBall n) :
        dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian v x) ≤ 0 := by
      have hqx : ContDiffAt ℝ 2 q x :=
        (hq.contDiffAt (ball_subset_closedBall hx)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have hsx : ContDiffAt ℝ 2 s x :=
        (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
      rw [show v = (fun z => q z + ε) + s from rfl,
        dirichlet_realHessian_add_C2 (hqx.add contDiffAt_const) hsx,
        dirichlet_realHessian_add_const]
      change dirichletHessianContractionLinearMap e[n] (dirichletCofactorOperator u x)
        (realHessian q x + realHessian s x) ≤ 0
      rw [map_add]
      change dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x) +
        dirichletBilinearContraction e[n] (dirichletCofactorOperator u x)
          (realHessian (dirichletSourceQuadratic a R x₀) x) ≤ 0
      rw [dirichletBilinearContraction_sourceQuadratic]
      have ht := mul_le_mul_of_nonneg_left
        (dirichlet_coefficient_trace_lower_bound e[n] (hEll x hx)) (by positivity : 0 ≤ 2 * a)
      have he : 2 * a * ((2 * n : ℝ) * c) = S := by nlinarith only [haS]
      rw [he] at ht
      nlinarith only [ht, hL x hx]
    have hvPos (x : E n) (hx : x ∈ ball x₀ R) : 0 < v x := by
      have hsp := (dirichletSourceQuadratic_bounds ha hR.le (ball_subset_closedBall hx)).1
      dsimp [v, s]
      linarith [hPos x hx]
    have hvInt : IntegrableOn v (ball x₀ (R / 4)) := by
      have hvC : ContinuousOn v (closedBall x₀ R) :=
        (hqC.add continuousOn_const).add hs.continuous.continuousOn
      exact (hvC.integrableOn_compact (isCompact_closedBall x₀ R)).mono_set hSub
    have hi := integral_mono_ae hqInt hvInt.abs (show
        q ≤ᵐ[volume.restrict (ball x₀ (R / 4))] fun x => |v x| from by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
      have hs0 := (dirichletSourceQuadratic_bounds ha hR.le (hSub hx)).1
      exact (by dsimp [v, s]; linarith : q x ≤ v x).trans (le_abs_self _))
    have h0 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (R ^ (2 * n))⁻¹)
    have h1 := hH u hu huP hNorm hEll v hv hLv x₀ R hR hBall hvPos y hy
    have hsY := (dirichletSourceQuadratic_bounds ha hR.le (hSub hy)).2
    have h2 : C * v y ≤ C * (q y + ε + a * R ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      dsimp [v, s]
      linarith only [hsY]
    exact h0.trans (h1.trans h2)
  have hT : Tendsto (fun ε : ℝ => C * (q y + ε + a * R ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (C * (q y + a * R ^ 2))) := by
    have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [add_zero] using ((tendsto_const_nhds.add h).add_const (a * R ^ 2)).const_mul C
  apply ge_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEst ε hε

end KEBall
