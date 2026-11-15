import KEBall.DirichletHigherAngularHessianL2
import KEBall.DirichletBilinearReconstruction

/-! General finite-exponent Fatou passage for the actual Hessian, including integrability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2*n)) ℝ

theorem tendsto_dirichlet_bilinear_of_basis_entries {n : ℕ} {ι : Type*} {l : Filter ι}
    {F : ι → E n →L[ℝ] E n →L[ℝ] ℝ} {H : E n →L[ℝ] E n →L[ℝ] ℝ}
    (h : ∀ i j : Fin (2*n), Tendsto (fun t => F t (e[n] i) (e[n] j)) l
      (𝓝 (H (e[n] i) (e[n] j)))) : Tendsto F l (𝓝 H) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => (h i j).smul_const (dirichletBilinearBasis i j)))
  change Tendsto (fun t => dirichletBilinearFromEntries (fun i j => F t (e[n] i) (e[n] j)))
    l (𝓝 (dirichletBilinearFromEntries (fun i j => H (e[n] i) (e[n] j)))) at hsum
  simpa only [dirichletBilinearFromEntries_basis] using hsum

theorem dirichlet_memLp_nat_of_integrable_norm_pow {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] {μ : Measure X} {F : X → V} {p : ℕ} (hp : 0 < p)
    (hF : AEStronglyMeasurable F μ) (hInt : Integrable (fun x => ‖F x‖^p) μ) :
    MemLp F (p : ℝ≥0∞) μ := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  have hpTop : (p : ℝ≥0∞) ≠ ⊤ := by simp
  have h := memLp_norm_rpow_iff (p := (p:ℝ≥0∞)) (q := (p:ℝ≥0∞)) hF hp0 hpTop
  rw [ENNReal.div_self hp0 hpTop] at h
  apply h.mp
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using memLp_one_iff_integrable.mpr hInt

theorem dirichlet_memLp_nat_of_ae_tendsto_power_bound {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] {μ : Measure X} {F : ℕ → X → V} {G : X → V}
    {p : ℕ} (hp : 0 < p) (hInt : ∀ m, Integrable (fun x => ‖F m x‖^p) μ)
    (hG : AEStronglyMeasurable G μ)
    (hLim : ∀ᵐ x ∂μ, Tendsto (fun m => F m x) atTop (𝓝 (G x)))
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᶠ m in atTop, (∫ x, ‖F m x‖^p ∂μ) ≤ C) :
    MemLp G (p:ℝ≥0∞) μ ∧ (∫ x, ‖G x‖^p ∂μ) ≤ C := by
  have h := dirichlet_integrable_and_integral_le_of_ae_tendsto_nonneg hC hInt
    (hG.norm.pow p) (fun _ => Eventually.of_forall (fun _ => pow_nonneg (norm_nonneg _) _))
    (Eventually.of_forall (fun _ => pow_nonneg (norm_nonneg _) _))
    (hLim.mono (fun x hx => hx.norm.pow p)) hBound
  exact ⟨dirichlet_memLp_nat_of_integrable_norm_pow hp hG h.1,h.2⟩

theorem memLp_realHessian_of_dirichlet_power_energy_limit {n p : ℕ}
    (hn : 0 < n) (hp : 0 < p)
    {w : E n → ℝ} (hw : ContDiffOn ℝ ∞ w (unitBall n))
    {v : ℕ → E n → ℝ} (hv : ∀ m, ContDiffOn ℝ 2 (v m) (closedUnitBall n))
    (hLim : ∀ x ∈ unitBall n, ∀ i j : Fin (2*n),
      Tendsto (fun m => dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) atTop
        (𝓝 (realHessian w x (e[n] i) (e[n] j))))
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᶠ m in atTop,
      (∫ x in unitBall n, ‖dirichletWithinRealHessian (v m) x‖^p ∂volume0 n) ≤ C) :
    MemLp (realHessian w) (p:ℝ≥0∞) ((volume0 n).restrict (unitBall n)) ∧
      (∫ x in unitBall n, ‖realHessian w x‖^p ∂volume0 n) ≤ C := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt (m : ℕ) : IntegrableOn (fun x => ‖dirichletWithinRealHessian (v m) x‖^p)
      (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn ((continuousOn_dirichletWithinRealHessian (hv m)).norm.pow p) 1).integrable le_rfl
  have hHC : ContinuousOn (realHessian w) (unitBall n) :=
    fun x hx => (realHessian_contDiffAt (hw.contDiffAt (isOpen_ball.mem_nhds hx))).continuousAt.continuousWithinAt
  apply dirichlet_memLp_nat_of_ae_tendsto_power_bound hp hInt
    (hHC.aestronglyMeasurable measurableSet_ball) ?_ hC hBound
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  exact tendsto_dirichlet_bilinear_of_basis_entries (hLim x hx)

end KEBall
