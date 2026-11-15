import KEBall.MoserTrudingerGibbsMassBound
import KEBall.DirichletComplexABP
import KEBall.CegrellCoercivity

/-!
# Uniform zeroth-order bounds for Gibbs solves with bounded input energy
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

theorem exponentialIntegral_le_on_energy_sublevel {n : ℕ} (hn : 0 < n)
    {α β C M : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hBound : ∀ {v : ComplexModel n → EReal} (hv : IsE1 (complexUnitBall n) v),
      finiteEnergyFunctional β hv ≤ (C : EReal))
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u)
    (hE : (energy hu).toReal ≤ M) :
    exponentialIntegral α u ≤ ENNReal.ofReal (Real.exp (β * (C + (α / β) ^ (n + 1) * M / (n + 1)))) := by
  let c := α / β
  have hc : 0 < c := div_pos hα hβ
  have hq := hu.const_mul hc
  have hZ : exponentialIntegral β (fun x => (c : EReal) * u x) = exponentialIntegral α u := by
    rw [exponentialIntegral_const_mul, div_mul_cancel₀ _ hβ.ne']
  have hF := hBound hq
  have hZfin : exponentialIntegral α u ≠ ⊤ := by
    intro htop
    rw [finiteEnergyFunctional, hZ, if_pos htop] at hF
    exact (EReal.coe_ne_top C (top_le_iff.mp hF)).elim
  have hz : 0 < (exponentialIntegral α u).toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (exponentialIntegral_ge_one hn hu hα.le)).ne' hZfin
  rw [finiteEnergyFunctional, hZ, if_neg hZfin, EReal.coe_le_coe_iff,
    energy_const_mul hn hu hc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc.le _)] at hF
  have hLog : Real.log (exponentialIntegral α u).toReal ≤
      β * (C + c ^ (n + 1) * M / (n + 1)) := by
    rw [mul_comm β]
    apply (div_le_iff₀ hβ).mp
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (pow_nonneg hc.le (n + 1)))
      (by positivity : 0 ≤ (n + 1 : ℝ))
    linarith only [hF, h]
  rw [← ENNReal.ofReal_toReal hZfin]
  exact ENNReal.ofReal_le_ofReal ((Real.log_le_iff_le_exp hz).mp hLog)

/-- A uniform bound on the actual energy of the inputs controls the
zeroth-order size of their smooth Gibbs Dirichlet solves. -/
theorem gibbs_solve_zeroth_order_le_of_energy_bound {n : ℕ} (hn : 0 < n)
    {γ β C M : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hBound : ∀ {w : ComplexModel n → EReal} (hw : IsE1 (complexUnitBall n) w),
      finiteEnergyFunctional β hw ≤ (C : EReal))
    {u v : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hv : SmoothNear (closedUnitBall n) v)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x)
    (hE : smoothEnergy u ≤ M) :
    ∀ x ∈ closedUnitBall n, (-v x / 2) ^ (2 * n) ≤ (4 : ℝ) ^ (2 * n) *
      Real.exp (β * (C + (2 * γ / β) ^ (n + 1) * M / (n + 1))) := by
  have huE := isE0_onBall_of_smooth_real_model hu (fun x hx => (huP x hx).posSemidef) hu0
  have hvE := isE0_onBall_of_smooth_real_model hv (fun x hx => (hvP x hx).posSemidef) hv0
  have huEnergy : (energy huE.isE1).toReal ≤ M := by
    rw [energy_realModelPotential hn hu huE]
    exact hE
  have hZ₂ := exponentialIntegral_le_on_energy_sublevel hn (show 0 < 2 * γ by positivity)
    hβ hBound huE.isE1 huEnergy
  change exponentialIntegral (2 * γ) (realModelPotential u) ≤ _ at hZ₂
  rw [exponentialIntegral_realModelPotential hn hu] at hZ₂
  have hZ₂' := (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hZ₂
  have hOne := exponentialIntegral_ge_one hn huE.isE1 hγ.le
  change 1 ≤ exponentialIntegral γ (realModelPotential u) at hOne
  rw [exponentialIntegral_realModelPotential hn hu γ, ← ENNReal.ofReal_one] at hOne
  have hZ₀ : 1 ≤ normalizingIntegral γ u := ((ENNReal.ofReal_le_ofReal_iff').mp hOne).resolve_right (by norm_num)
  have hUC : ContinuousOn u (closedUnitBall n) :=
    fun x hx => (hu.contDiffAt hx).continuousAt.continuousWithinAt
  have hf : ContinuousOn (gibbsDensity γ u) (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hUC)).div_const _
  have hI : (∫ x in unitBall n, gibbsDensity γ u x ^ 2 ∂volume0 n) ≤ normalizingIntegral (2 * γ) u := by
    have hP (x : E n) : gibbsDensity γ u x ^ 2 =
        Real.exp (-(2 * γ) * u x) / normalizingIntegral γ u ^ 2 := by
      rw [gibbsDensity, div_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    simp_rw [hP]
    rw [integral_div, ← normalizingIntegral]
    apply div_le_self (integral_nonneg fun x => Real.exp_nonneg _)
    exact one_le_pow₀ hZ₀
  have hV (x : E n) (hx : x ∈ closedUnitBall n) : v x ≤ 0 := by
    rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with h | h
    · let e := complexCoordinates n
      have hB : e x ∈ complexUnitBall n := by
        change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
        rw [preimage_complexUnitBall]
        exact mem_ball_zero_iff.mpr h
      have hneg := hvE.nonpositive_unitBall hn (e x) hB
      change v (e.symm (e x)) ≤ 0 at hneg
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hneg
    · rw [hv0 x (mem_sphere_zero_iff_norm.mpr h)]
  intro x hx
  exact (dirichlet_abp hn hv hf hv0 hvP hEq hx (hV x hx)).trans
    (mul_le_mul_of_nonneg_left (hI.trans hZ₂') (by positivity))

/-- A smooth inverse iteration controlled by a larger-exponent functional
bound stays uniformly bounded in energy and in zeroth order after the first solve. -/
theorem exists_energy_and_zeroth_order_bounds_of_smoothGibbsIteration {n : ℕ} (hn : 0 < n)
    {γ β C : ℝ} (hγ : 0 < γ) (hγβ : γ < β)
    (hBound : ∀ {w : ComplexModel n → EReal} (hw : IsE1 (complexUnitBall n) w),
      finiteEnergyFunctional β hw ≤ (C : EReal))
    {u : ℕ → E n → ℝ} {U : Set (E n)} (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) U)
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x) :
    ∃ M B : ℝ, 0 < B ∧ (∀ j, smoothEnergy (u j) ≤ M) ∧
      ∀ j x, x ∈ closedUnitBall n → -B ≤ u (j + 1) x := by
  let hNear (j : ℕ) : SmoothNear (closedUnitBall n) (u j) := ⟨U, hU, hsub, hu j⟩
  have hMono : Monotone (fun j => smoothFunctional γ (u j)) :=
    monotone_nat_of_le_succ fun j => smoothFunctional_le_of_gibbs_step hn hU hsub (hu j) (hu (j + 1))
      (hu0 j) (hu0 (j + 1)) (huP j) (huP (j + 1)) hγ (hEq j)
  let d := (1 - (γ / β) ^ n) / (n + 1 : ℝ)
  have hd : 0 < d := div_pos (coercivity_coefficient_pos hn hγ hγβ) (by positivity)
  let M := max 0 ((C / (γ / β) - smoothFunctional γ (u 0)) / d)
  have hM (j : ℕ) : smoothEnergy (u j) ≤ M := by
    have hq := isE0_onBall_of_smooth_real_model (hNear j)
      (fun x hx => (huP j x hx).posSemidef) (hu0 j)
    have h := (finiteEnergyFunctional_coercive_of_bound hn hγ hγβ hBound hq.isE1).2
    rw [finiteEnergyFunctional_realModelPotential hn (hNear j) hq,
      EReal.coe_le_coe_iff, energy_realModelPotential hn (hNear j) hq] at h
    have hRe : smoothFunctional γ (u j) ≤ C / (γ / β) - d * smoothEnergy (u j) := by
      rw [smoothFunctional, signedSmoothEnergy_eq hU (hu j) hsub (huP j), neg_div]
      convert h using 1 <;> (try dsimp [d]) <;> ring
    apply le_max_of_le_right
    apply (le_div_iff₀ hd).mpr
    have hUpper := hMono (Nat.zero_le j)
    linarith only [hRe, hUpper, mul_comm d (smoothEnergy (u j))]
  let K := (4 : ℝ) ^ (2 * n) * Real.exp (β * (C + (2 * γ / β) ^ (n + 1) * M / (n + 1)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let B := 2 * (K + 1)
  refine ⟨M, B, by dsimp [B]; positivity, hM, ?_⟩
  intro j x hx
  have hPow : (-u (j + 1) x / 2) ^ (2 * n) ≤ K :=
    gibbs_solve_zeroth_order_le_of_energy_bound hn hγ (hγ.trans hγβ) hBound
      (hNear j) (hNear (j + 1)) (hu0 j) (hu0 (j + 1)) (huP j) (huP (j + 1)) (hEq j) (hM j) x hx
  by_contra! h
  have hLower : K + 1 < -u (j + 1) x / 2 := by dsimp [B] at h; linarith
  have h₀ : 1 ≤ K + 1 := by linarith
  have hPos : 0 ≤ K + 1 := by positivity
  have hContra := (le_self_pow₀ h₀ (show 2 * n ≠ 0 by omega)).trans_lt
    (pow_lt_pow_left₀ hLower hPos (show 2 * n ≠ 0 by omega))
  linarith only [hPow, hContra]

end KEBall.MoserTrudinger
