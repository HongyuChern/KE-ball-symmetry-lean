import KEBall.LowerSlope

/-!
# The final Euler equation along actual rays

This module solves the real first-order Euler identity used in the last
paragraph of the v4 rigidity proof. All ray derivatives are obtained from
the actual Frechet derivative; the identity itself remains an explicit
intermediate hypothesis for the holomorphic-gradient step to establish.
No statement that every solution is radial is assumed or asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped ContDiff Topology

namespace KEBall

/-- A smooth function with the actual Euler derivative `Rf = 2f-2C` and
constant unit-sphere value is affine in the squared Euclidean norm. -/
theorem eq_affine_norm_sq_of_euler {n : ℕ} {f : E n → ℝ} {C : ℝ}
    (hf : SmoothNear (closedUnitBall n) f)
    (hboundary : ∀ y ∈ unitSphere n, f y = 1)
    (hEuler : ∀ y ∈ unitBall n, fderiv ℝ f y y = 2 * f y - 2 * C) :
    ∀ x ∈ closedUnitBall n, f x = C + (1 - C) * ‖x‖ ^ 2 := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have h0 := hEuler 0 (by simp [unitBall])
    simp only [map_zero] at h0
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    linarith
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
  let R : ℝ := 1 / ‖x‖
  have hR : 1 ≤ R := by
    exact (le_div_iff₀ hnorm).mpr (by simpa using hxnorm)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlineClosed {t : ℝ} (ht : t ∈ Icc 1 R) : t • x ∈ closedUnitBall n := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have htnorm : t * ‖x‖ ≤ 1 := (le_div_iff₀ hnorm).mp ht.2
    simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos] using htnorm
  have hlineBall {t : ℝ} (ht : t ∈ Ico 1 R) : t • x ∈ unitBall n := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have htnorm : t * ‖x‖ < 1 := (lt_div_iff₀ hnorm).mp ht.2
    simpa [unitBall, Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos] using htnorm
  let ψ : ℝ → ℝ := fun t => f (t • x)
  let F : ℝ → ℝ := fun t => (ψ t - C) / t ^ 2
  have hψcont : ContinuousOn ψ (Icc 1 R) := by
    intro t ht
    have hline : ContinuousAt (fun r : ℝ => r • x) t := by fun_prop
    have hcomp : ContinuousAt (fun r : ℝ => f (r • x)) t :=
      (hf.contDiffAt (hlineClosed ht)).continuousAt.comp (f := fun r : ℝ => r • x) (x := t) hline
    exact hcomp.continuousWithinAt
  have hFcont : ContinuousOn F (Icc 1 R) :=
    (hψcont.sub continuousOn_const).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hFderiv : ∀ t ∈ Ico 1 R, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have htx := hlineBall ht
    have htxclosed : t • x ∈ closedUnitBall n := Metric.ball_subset_closedBall htx
    have hγ : HasDerivAt (fun r : ℝ => r • x) x t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x
    have hψ : HasDerivAt ψ (fderiv ℝ f (t • x) x) t :=
      ((hf.contDiffAt htxclosed).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ
    have hE := hEuler (t • x) htx
    rw [map_smul, smul_eq_mul] at hE
    have hEd := congrArg (fun r : ℝ => t * r) hE
    have hF' := (hψ.sub_const C).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 (ne_of_gt htpos))
    refine (hF'.congr_deriv ?_).hasDerivWithinAt
    change (fderiv ℝ f (t • x) x * t ^ 2 - (f (t • x) - C) * (2 * t ^ 1 * 1)) /
      (t ^ 2) ^ 2 = 0
    simp only [pow_one, mul_one]
    apply (div_eq_zero_iff).mpr
    left
    nlinarith
  have hconst := constant_of_has_deriv_right_zero hFcont hFderiv R ⟨hR, le_rfl⟩
  have hRsphere : R • x ∈ unitSphere n := by
    have hnormR : ‖R • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
      dsimp [R]
      exact div_mul_cancel₀ 1 (ne_of_gt hnorm)
    simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hnormR
  change (f (R • x) - C) / R ^ 2 = (f (1 • x) - C) / 1 ^ 2 at hconst
  rw [hboundary _ hRsphere, one_smul, one_pow, div_one] at hconst
  dsimp [R] at hconst
  field_simp [ne_of_gt hnorm] at hconst
  linarith

/-- The actual Euler identity appearing after the holomorphic-gradient
argument determines the potential itself on the full closed ball. -/
theorem eq_radial_of_euler_identity {n : ℕ} {u : E n → ℝ} {a : ℝ}
    (hu : SmoothNear (closedUnitBall n) u)
    (hboundary : ∀ x ∈ unitSphere n, u x = 0) (ha : 0 < a) (hak : a < (n + 1 : ℝ))
    (hEuler : ∀ x ∈ unitBall n,
      fderiv ℝ u x x = 2 * ((n + 1 : ℝ) - ((n + 1 : ℝ) - a) * expWeight u x)) :
    EqOn u (radialPotential n (a / ((n + 1 : ℝ) - a))) (closedUnitBall n) := by
  let κ : ℝ := (n + 1 : ℝ)
  have hkpos : 0 < κ := by dsimp [κ]; positivity
  have hk : κ ≠ 0 := ne_of_gt hkpos
  let C : ℝ := (κ - a) / κ
  let v : E n → ℝ := fun x => Real.exp (κ⁻¹ * u x)
  have hvSmooth : SmoothNear (closedUnitBall n) v := by
    obtain ⟨U, hU, hKU, huU⟩ := hu
    exact ⟨U, hU, hKU, (contDiffOn_const.mul huU).exp⟩
  have hvBoundary : ∀ x ∈ unitSphere n, v x = 1 := by
    intro x hx
    simp [v, hboundary x hx]
  have hvEuler : ∀ x ∈ unitBall n, fderiv ℝ v x x = 2 * v x - 2 * C := by
    intro x hx
    have huAt := (hu.contDiffAt (Metric.ball_subset_closedBall hx)).differentiableAt (by simp)
    have hd := (huAt.hasFDerivAt.const_mul κ⁻¹).exp
    change HasFDerivAt v (v x • (κ⁻¹ • fderiv ℝ u x)) x at hd
    have hp : v x * expWeight u x = 1 := by
      dsimp [v, expWeight, κ]
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul]
    rw [hEuler x hx]
    change v x * (κ⁻¹ * (2 * (κ - (κ - a) * expWeight u x))) =
      2 * v x - 2 * ((κ - a) / κ)
    field_simp [hk]
    have hp' := congrArg (fun r : ℝ => (κ - a) * r) hp
    nlinarith
  have hvformula := eq_affine_norm_sq_of_euler hvSmooth hvBoundary hvEuler
  have hka : 0 < κ - a := sub_pos.mpr hak
  have hb : 0 < a / (κ - a) := div_pos ha hka
  have harg (x : E n) : (1 + (a / (κ - a)) * ‖x‖ ^ 2) / (1 + a / (κ - a)) =
      C + (1 - C) * ‖x‖ ^ 2 := by
    dsimp [C]
    field_simp [hk, ne_of_gt hka]
    ring
  intro x hx
  have hlog := congrArg Real.log (hvformula x hx)
  rw [show v x = Real.exp (κ⁻¹ * u x) from rfl, Real.log_exp] at hlog
  change u x = κ * Real.log ((1 + (a / (κ - a)) * ‖x‖ ^ 2) / (1 + a / (κ - a)))
  rw [harg, ← hlog]
  field_simp [hk]

/-- A germ equality is sufficient to identify the actual complex Hessians. -/
theorem complexHessian_congr_of_eventuallyEq {n : ℕ} {u v : E n → ℝ} {x : E n}
    (heq : u =ᶠ[𝓝 x] v) : complexHessian u x = complexHessian v x := by
  have hc : (fun y => (u y : ℂ)) =ᶠ[𝓝 x] (fun y => (v y : ℂ)) :=
    heq.mono fun _ hy => congrArg Complex.ofReal hy
  ext i j
  have hbar : partialBar j (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
      partialBar j (fun y => (v y : ℂ)) := by
    filter_upwards [hc.eventually_nhds] with y hy
    exact LogDetAux.dz_congr_of_eventuallyEq hy _ _
  exact LogDetAux.dz_congr_of_eventuallyEq hbar _ _

/-- The coefficient is determined by the actual closed-ball restriction of
a solution, independently of the choice of smooth extension. -/
theorem IsSolution.coefficient_eq_of_eqOn {n : ℕ} {μ ν : ℝ} {u v : E n → ℝ}
    (hu : IsSolution n μ u) (hv : IsSolution n ν v)
    (heq : EqOn u v (closedUnitBall n)) : μ = ν := by
  have h0 : (0 : E n) ∈ unitBall n := by simp [unitBall]
  have h0closed : (0 : E n) ∈ closedUnitBall n := Metric.ball_subset_closedBall h0
  have hnear : u =ᶠ[𝓝 (0 : E n)] v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with y hy
    exact heq (Metric.ball_subset_closedBall hy)
  have hdet := congrArg Matrix.det (complexHessian_congr_of_eventuallyEq hnear)
  rw [hu.2.2.2.1 0 h0, hv.2.2.2.1 0 h0] at hdet
  have hreal : μ * Real.exp (-u 0) = ν * Real.exp (-v 0) := by
    exact_mod_cast hdet
  rw [heq h0closed] at hreal
  exact mul_right_cancel₀ (Real.exp_ne_zero _) hreal

/-- Conditional terminal consumer for the main proof: once the actual Euler
identity has been derived, both radiality and its coefficient follow. -/
theorem IsSolution.radial_of_euler_identity {n : ℕ} {μ a : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) (ha : 0 < a) (hak : a < (n + 1 : ℝ))
    (hEuler : ∀ x ∈ unitBall n,
      fderiv ℝ u x x = 2 * ((n + 1 : ℝ) - ((n + 1 : ℝ) - a) * expWeight u x)) :
    ∃ b : ℝ, 0 < b ∧ EqOn u (radialPotential n b) (closedUnitBall n) ∧
      μ = radialCoefficient n b := by
  let b := a / ((n + 1 : ℝ) - a)
  have hb : 0 < b := div_pos ha (sub_pos.mpr hak)
  have heq : EqOn u (radialPotential n b) (closedUnitBall n) :=
    eq_radial_of_euler_identity hu.2.1 hu.2.2.2.2 ha hak hEuler
  exact ⟨b, hb, heq, hu.coefficient_eq_of_eqOn (radial_isSolution n hb) heq⟩

end KEBall
