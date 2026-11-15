import KEBall.MoserTrudingerWeakGibbsPairs
import KEBall.MoserTrudingerSmoothToFiniteEnergy

/-!
# A continuous weak maximizer from smooth auxiliary Dirichlet solves
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)
local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

private theorem eq_smoothFunctional_of_smooth_model (hn : 0 < n) (γ : ℝ)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hE : IsE0 (complexUnitBall n) (u ∘ (complexCoordinates n).symm)) :
    finiteEnergyFunctional γ hE.isE1 = (smoothFunctional γ u : EReal) := by
  have hNear : SmoothNear (closedUnitBall n) u := ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  rw [finiteEnergyFunctional_realModelPotential hn hNear hE, smoothFunctional,
    signedSmoothEnergy_eq isOpen_univ hu.contDiffOn (subset_univ _) huP, neg_div]
  congr 1
  ring

private theorem finiteEnergyFunctional_le_of_real_smooth_bound (hn : 0 < n) {γ C : ℝ}
    (hγ : 0 < γ)
    (hSmooth : ∀ (u : E n → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ unitSphere n, u x = 0) → (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      smoothFunctional γ u ≤ C)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    finiteEnergyFunctional γ hu ≤ (C : EReal) := by
  apply finiteEnergyFunctional_le_of_smooth_bound hn hγ _ hu
  intro q hq hqC hqP
  let e := complexCoordinates n
  let p : E n → ℝ := q ∘ e
  have hpC : ContDiff ℝ ∞ p := hqC.comp e.toContinuousLinearEquiv.contDiff
  have hp0 (x : E n) (hx : x ∈ unitSphere n) : p x = 0 := by
    let B := (complexUnitBall n : Set (ComplexModel n))
    have hz : e x ∈ frontier B := by
      change e x ∈ frontier (ball (0 : ComplexModel n) 1)
      rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
    let : NeBot (𝓝[B] e x) := mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hz)
    exact tendsto_nhds_unique (hqC.continuous.continuousWithinAt (s := B) (x := e x)) (hq.boundary _ hz)
  have hqEq : p ∘ e.symm = q := by
    funext x
    simp only [p, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hpP (x : E n) (hx : x ∈ unitBall n) : (complexHessian p x).PosDef := by
    have hx' : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      rwa [preimage_complexUnitBall]
    rw [← complexHessian_coordinates hpC.contDiffAt, hqEq]
    exact hqP _ hx'
  have hpE : IsE0 (complexUnitBall n) (p ∘ e.symm) := hqEq.symm ▸ hq
  have hEqF : finiteEnergyFunctional γ hq.isE1 = finiteEnergyFunctional γ hpE.isE1 := by
    congr 1
    exact congrArg (fun v : ComplexModel n → ℝ => fun x => (v x : EReal)) hqEq.symm
  rw [hEqF, eq_smoothFunctional_of_smooth_model hn γ hpC hpP hpE, EReal.coe_le_coe_iff]
  exact hSmooth p hpC hp0 hpP

/-- Given smooth auxiliary Gibbs Dirichlet solvability and a functional
bound at a larger coupling, the actual finite-energy maximum has a
continuous zero-boundary representative solving the weak equation. -/
theorem exists_weakGibbs_maximizer_of_smoothGibbs (hn : 0 < n)
    {γ β C : ℝ} (hγ : 0 < γ) (hγβ : γ < β)
    (hBound : ∀ {w : ComplexModel n → EReal} (hw : IsE1 (complexUnitBall n) w),
      finiteEnergyFunctional β hw ≤ (C : EReal))
    (hSolve : SmoothGibbsDirichletSolvable n γ) :
    ∃ r : E n → ℝ, ∃ hr : IsWeakGibbsSolution n γ r,
      ∀ {w : ComplexModel n → EReal} (hw : IsE1 (complexUnitBall n) w),
        finiteEnergyFunctional γ hw ≤ finiteEnergyFunctional γ hr.memE0.isE1 := by
  let e := complexCoordinates n
  let A := {u : E n → ℝ // ContDiff ℝ ∞ u ∧ (∀ x ∈ unitSphere n, u x = 0) ∧
    (∀ x ∈ unitBall n, (complexHessian u x).PosDef)}
  let F (u : A) := smoothFunctional γ u.1
  let D := C / (γ / β)
  let d := (1 - (γ / β) ^ n) / (n + 1 : ℝ)
  have hd : 0 < d := div_pos (coercivity_coefficient_pos hn hγ hγβ) (by positivity)
  have hNear (u : A) : SmoothNear (closedUnitBall n) u.1 :=
    ⟨univ, isOpen_univ, subset_univ _, u.2.1.contDiffOn⟩
  have hE₀ (u : A) : IsE0 (complexUnitBall n) (u.1 ∘ e.symm) :=
    isE0_onBall_of_smooth_real_model (hNear u) (fun x hx => (u.2.2.2 x hx).posSemidef) u.2.2.1
  have hCoer (u : A) : F u ≤ D - d * smoothEnergy u.1 := by
    have h := (finiteEnergyFunctional_coercive_of_bound hn hγ hγβ hBound (hE₀ u).isE1).2
    rw [eq_smoothFunctional_of_smooth_model hn γ u.2.1 u.2.2.2 (hE₀ u),
      EReal.coe_le_coe_iff, energy_realModelPotential hn (hNear u) (hE₀ u)] at h
    dsimp [F, D, d]
    convert h using 1; ring
  have hEn₀ (u : A) : 0 ≤ smoothEnergy u.1 := by
    rw [← energy_realModelPotential hn (hNear u) (hE₀ u)]
    exact ENNReal.toReal_nonneg
  have hBdd : BddAbove (range F) := ⟨D, by
    rintro _ ⟨u, rfl⟩
    exact (hCoer u).trans (sub_le_self _ (mul_nonneg hd.le (hEn₀ u)))⟩
  have hS : (range F).Nonempty := by
    let u : A := ⟨radialPotential n 1, smooth_radialPotential n zero_lt_one,
      (fun _ hx => radial_boundary_zero n zero_lt_one hx), fun x _ => radial_complexHessian_posDef n zero_lt_one x⟩
    exact ⟨F u, u, rfl⟩
  let m := sSup (range F)
  have hUpper (u : A) : F u ≤ m := le_csSup hBdd ⟨u, rfl⟩
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε₀ (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε₁ (j : ℕ) : ε j ≤ 1 := (div_le_one (by positivity)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hεL : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hex (j : ℕ) : ∃ u : A, m - ε j < F u := by
    obtain ⟨_, ⟨u, rfl⟩, h⟩ := exists_lt_of_lt_csSup hS (sub_lt_self m (hε₀ j))
    exact ⟨u, h⟩
  choose x hx using hex
  have hNext (u : A) : ∃ v : A, ∀ x ∈ unitBall n,
      (complexHessian v.1 x).det.re = gibbsDensity γ u.1 x := by
    obtain ⟨v, hv, hv₀, hvP, hvEq⟩ := hSolve u.1 u.2.1 u.2.2.1 u.2.2.2
    exact ⟨⟨v, hv, hv₀, hvP⟩, hvEq⟩
  choose next hEq using hNext
  have hMono (u : A) : F u ≤ F (next u) :=
    smoothFunctional_le_of_gibbs_step hn isOpen_univ (subset_univ _)
      u.2.1.contDiffOn (next u).2.1.contDiffOn u.2.2.1 (next u).2.2.1 u.2.2.2 (next u).2.2.2 hγ (hEq u)
  let a (j : ℕ) := next (x j)
  let b (j : ℕ) := next (a j)
  have hLower (j : ℕ) : m - ε j ≤ F (x j) := (hx j).le
  have hLowerA (j : ℕ) : m - ε j ≤ F (a j) := (hLower j).trans (hMono (x j))
  have hLowerB (j : ℕ) : m - ε j ≤ F (b j) := (hLowerA j).trans (hMono (a j))
  have hml : Tendsto (fun j => m - ε j) atTop (𝓝 m) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := m)).sub hεL
  have haF : Tendsto (fun j => F (a j)) atTop (𝓝 m) :=
    hml.squeeze tendsto_const_nhds hLowerA (fun j => hUpper (a j))
  have hbF : Tendsto (fun j => F (b j)) atTop (𝓝 m) :=
    hml.squeeze tendsto_const_nhds hLowerB (fun j => hUpper (b j))
  let M := max 0 ((D - m + 1) / d)
  have hEn (j : ℕ) (u : A) (hLo : m - ε j ≤ F u) : smoothEnergy u.1 ≤ M := by
    apply le_max_of_le_right
    apply (le_div_iff₀ hd).mpr
    linarith only [hCoer u, hLo, hε₁ j, mul_comm d (smoothEnergy u.1)]
  let K := (4 : ℝ) ^ (2 * n) * Real.exp (β * (C + (2 * γ / β) ^ (n + 1) * M / (n + 1)))
  let B := 2 * (K + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hNextB (u : A) (hMu : smoothEnergy u.1 ≤ M) :
      ∀ᵐ x ∂ν[n], (next u).1 x ∈ Icc (-B) 0 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    constructor
    · have hPow : (-(next u).1 x / 2) ^ (2 * n) ≤ K :=
        gibbs_solve_zeroth_order_le_of_energy_bound hn hγ (hγ.trans hγβ) hBound
          (hNear u) (hNear (next u)) u.2.2.1 (next u).2.2.1 u.2.2.2 (next u).2.2.2 (hEq u) hMu
          x (ball_subset_closedBall hx)
      by_contra! h
      have hLower' : K + 1 < -(next u).1 x / 2 := by dsimp [B] at h; linarith
      have h₀ : 1 ≤ K + 1 := by linarith
      have hPos : 0 ≤ K + 1 := by positivity
      have hContra := (le_self_pow₀ h₀ (show 2 * n ≠ 0 by omega)).trans_lt
        (pow_lt_pow_left₀ hLower' hPos (show 2 * n ≠ 0 by omega))
      linarith only [hPow, hContra]
    · have he : e x ∈ complexUnitBall n := by
        change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
        rwa [preimage_complexUnitBall]
      have h := (hE₀ (next u)).nonpositive_unitBall hn (e x) he
      change (next u).1 (e.symm (e x)) ≤ 0 at h
      simpa only [e.symm_apply_apply] using h
  obtain ⟨r, hr, hR⟩ := exists_weakGibbsSolution_ge_of_smoothGibbsPairs hn hγ
    (u := fun j => (a j).1) (v := fun j => (b j).1)
    (fun j => (a j).2.1) (fun j => (b j).2.1)
    (fun j => (a j).2.2.1) (fun j => (b j).2.2.1)
    (fun j => (a j).2.2.2) (fun j => (b j).2.2.2)
    (fun j => hEq (a j)) (fun j => hEn j (a j) (hLowerA j))
    (fun j => hNextB (x j) (hEn j (x j) (hLower j))) (fun j => hNextB (a j) (hEn j (a j) (hLowerA j)))
    haF hbF
  refine ⟨r, hr, fun hw => ?_⟩
  exact (finiteEnergyFunctional_le_of_real_smooth_bound hn hγ
    (fun u hu hu0 huP => hUpper ⟨u, hu, hu0, huP⟩) hw).trans hR

end KEBall.MoserTrudinger
