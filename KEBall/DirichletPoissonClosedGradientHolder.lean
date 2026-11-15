import KEBall.DirichletPoissonScaledGradientHolder
import KEBall.DirichletPoissonBoundaryPower
import KEBall.DirichletUniformBoundaryHolderGluing
import KEBall.DirichletBoundaryJetPower
import KEBall.DirichletBoundaryQuotientTrace
import KEBall.BoundaryHessian

/-! A common closed-ball Holder bound for genuine first derivatives of a
zero-boundary Poisson family. The hypotheses contain no real Hessian bound.
Uncompiled continuation draft. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open InnerProductSpace Metric Set
open scoped ContDiff Laplacian NNReal

noncomputable section
namespace KEBall

theorem exists_uniform_closedBall_poisson_gradient_holder {n : ℕ} (hn : 2 ≤ n)
    {J : Type*} (u : J → E n → ℝ) {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (hGrad : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G)
    (hLap : ∀ j x, x ∈ unitBall n → |Δ (u j) x| ≤ L) :
    ∃ θ M : ℝ≥0, 0 < θ ∧ θ < 1 ∧
      ∀ j, HolderOnWith M θ (fderiv ℝ (u j)) (closedUnitBall n) := by
  have hn0 : 0 < n := by omega
  letI : NeZero n := ⟨hn0.ne'⟩
  obtain ⟨α, D, hα, hα1, hD, hPower⟩ :=
    exists_uniform_poisson_boundary_quotient_power hn hG hL
  obtain ⟨C₀, hC₀, hLocal⟩ := exists_local_poisson_scaled_gradient_holder_constant (V := E n)
  let C : ℝ := D * (256 : ℝ) ^ α
  let H : ℝ := 2 * C₀ * (G + L)
  let K : ℝ := (C + 2 * G) * (2 : ℝ) ^ α
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let a : J → E n → ℝ := fun j p => -fderiv ℝ (u j) p p
  have huNear (j : J) : SmoothNear (closedUnitBall n) (u j) :=
    ⟨univ, isOpen_univ, subset_univ _, (hu j).contDiffOn⟩
  have hLip (j : J) : LipschitzOnWith (⟨G, hG⟩ : ℝ≥0) (u j) (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _
      (convex_closedBall (0 : E n) 1)
    · exact fun x _ => (hu j).differentiable (by simp) x
    · intro x hx
      exact_mod_cast hGrad j x hx
  have hQuot (j : J) (x : E n) (hx : x ∈ unitBall n) :
      |u j x / dirichletBoundaryDistanceProxy x| ≤ 2 * G :=
    abs_dirichlet_boundary_quotient_le_of_lipschitz hn0 (hLip j) (hu0 j) hx
  have hABound (j : J) (p : E n) (hp : p ∈ unitSphere n) : |a j p| ≤ G := by
    dsimp only [a]
    rw [abs_neg, ← Real.norm_eq_abs]
    exact ((fderiv ℝ (u j) p).le_opNorm p).trans (by
      rw [mem_sphere_zero_iff_norm.mp hp, mul_one]
      exact hGrad j p (sphere_subset_closedBall hp))
  have hQb (j : J) (p : E n) (hp : p ∈ unitSphere n) :
      fderiv ℝ (u j) p = a j p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p := by
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_dirichletBoundaryDistanceProxy, ContinuousLinearMap.neg_apply, innerSL_apply_apply]
    rw [sphere_fderiv_normal (huNear j) (hu0 j) hp]
    dsimp only [a, boundarySlope]
    ring
  have hOsc (j : J) (p : E n) (hp : p ∈ unitSphere n) (r : ℝ)
      (hr : 0 < r) (hr1 : r ≤ 1) :
      dirichletBoundaryOscillation
        (fun x => u j x / dirichletBoundaryDistanceProxy x) p r ≤ C * r ^ α := by
    simpa only [div_one, C] using
      hPower (u j) (hu j) (hu0 j) (hGrad j) (hLap j) p hp 1 zero_lt_one le_rfl r hr hr1
  have hTrace (j : J) (p : E n) (hp : p ∈ unitSphere n) (r : ℝ)
      (hr : 0 < r) (hr1 : r ≤ 1) (x : E n) (hx : x ∈ dirichletBoundaryCap p r) :
      |u j x / dirichletBoundaryDistanceProxy x - a j p| ≤ C * r ^ α := by
    have h := abs_dirichlet_quotient_add_normal_le_oscillation hp
      ((hu j).differentiable (by simp) p).hasFDerivAt (hu0 j p hp) (hQuot j) hr hx
    have h' : |u j x / dirichletBoundaryDistanceProxy x - a j p| ≤
        dirichletBoundaryOscillation
          (fun y => u j y / dirichletBoundaryDistanceProxy y) p r := by
      simpa only [a, sub_neg_eq_add] using h
    exact h'.trans (hOsc j p hp r hr hr1)
  have hABdy (j : J) (p : E n) (hp : p ∈ unitSphere n)
      (q : E n) (hq : q ∈ unitSphere n) : |a j p - a j q| ≤ K * dist p q ^ α := by
    have hLoc (p : E n) (hp : p ∈ unitSphere n) (q : E n) (hq : q ∈ unitSphere n)
        (hd : dist p q ≤ 1 / 2) : |a j p - a j q| ≤ C * (2 * dist p q) ^ α := by
      have h := abs_dirichlet_boundary_normal_sub_le_of_power
        (fun p _ => ((hu j).differentiable (by simp) p).hasFDerivAt)
        (hu0 j) hC (hQuot j) (hOsc j) hp hq hd
      simpa only [a, neg_sub_neg, abs_sub_comm] using h
    simpa only [dist_eq_norm, K] using
      (abs_dirichlet_boundary_trace_sub_le_global hG hC hα.le (hABound j) hLoc p hp q hq)
  have hScaled (j : J) (x : E n) (hx : x ∈ unitBall n) (r : ℝ)
      (hrEq : r = 1 - ‖x‖) :
      ∀ y ∈ ball x (r / 8), ∀ z ∈ ball x (r / 8),
        ‖fderiv ℝ (u j) y - fderiv ℝ (u j) z‖ ≤
          (H / r ^ (1 / 2 : ℝ)) * ‖y - z‖ ^ (1 / 2 : ℝ) := by
    have hr : 0 < r := by rw [hrEq]; exact sub_pos.mpr (mem_ball_zero_iff.mp hx)
    have hr1 : r ≤ 1 := by rw [hrEq]; linarith [norm_nonneg x]
    have hSub : closedBall x (r / 4) ⊆ unitBall n :=
      closedBall_subset_dirichlet_unitBall_of_margin (by rw [hrEq] at *; linarith)
    intro y hy z hz
    have hy' : y ∈ ball x ((r / 4) / 2) := by convert hy using 1 <;> ring
    have hz' : z ∈ ball x ((r / 4) / 2) := by convert hz using 1 <;> ring
    have h := hLocal (u j) (hu j) x (r / 4) G L (by positivity) (by linarith)
      hG hL (fun w hw => hGrad j w (ball_subset_closedBall (hSub hw)))
      (fun w hw => by simpa only [Real.norm_eq_abs] using hLap j w (hSub hw)) y hy' z hz'
    have hSqrt : Real.sqrt (r / 4) = Real.sqrt r / 2 := by
      rw [Real.sqrt_div hr.le]
      norm_num
    rw [hSqrt, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow] at h
    convert h using 1 <;> dsimp [H] <;> ring
  let η : ℝ := α * (1 / 2) / 2
  let C₁ : ℝ := 16 * (C * (2 : ℝ) ^ (1 + α)) +
    (H + G) / (8 : ℝ) ^ (1 / 2 : ℝ) + G
  have hη : 0 < η := by dsimp [η]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hApproach (j : J) (x : E n) (hx : x ∈ closedUnitBall n)
      (hs : 1 - ‖x‖ ≤ 1 / 2) (p : E n) (hp : p ∈ unitSphere n)
      (hd : dist x p = 1 - ‖x‖) :
      ‖fderiv ℝ (u j) x - fderiv ℝ (u j) p‖ ≤ C₁ * (1 - ‖x‖) ^ η :=
    norm_dirichlet_extended_jet_sub_nearest_le hG hC hH hα hα1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (fun x _ => (hu j).differentiable (by simp) x) (fun _ _ => rfl)
      (hQb j) (hABound j) (hTrace j)
      (fun x hx r hr _ => hScaled j x hx r hr) hx hs hp hd
  have hBoundary (j : J) (p : E n) (hp : p ∈ unitSphere n)
      (q : E n) (hq : q ∈ unitSphere n) :
      ‖fderiv ℝ (u j) p - fderiv ℝ (u j) q‖ ≤ (K + 2 * G) * dist p q ^ α := by
    rw [hQb j p hp, hQb j q hq]
    exact norm_dirichlet_normal_jet_sub_le_of_holder_trace hG hK hα.le hα1
      (hABound j) (hABdy j) hp hq
  have hInterior (j : J) (x : E n) (hx : x ∈ unitBall n)
      (y : E n) (hy : y ∈ ball x ((1 - ‖x‖) / 8)) :
      ‖fderiv ℝ (u j) x - fderiv ℝ (u j) y‖ ≤
        (H / (1 - ‖x‖) ^ (1 / 2 : ℝ)) * dist x y ^ (1 / 2 : ℝ) := by
    have hr : 0 < (1 - ‖x‖) / 8 := by
      have := mem_ball_zero_iff.mp hx
      positivity
    simpa only [dist_eq_norm] using
      hScaled j x hx _ rfl x (mem_ball_self hr) y hy
  obtain ⟨θ, _, hθ, hθ1, M, hFinal⟩ :=
    exists_uniform_dirichlet_closedBall_holder_of_boundary_power hn0
      (fun j => fderiv ℝ (u j)) hG hC₁ hH (by positivity : 0 ≤ K + 2 * G)
      hα hα1 (by norm_num : (0 : ℝ) < 1 / 2) hη hGrad hBoundary hApproach hInterior
  exact ⟨θ, M, hθ, hθ1, hFinal⟩

end KEBall
