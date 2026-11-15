import Drafts.KEBall.ExponentialGradientCR
import Drafts.KEBall.CRDirichlet
import KEBall.RayODE

/-!
Stage09 SOURCE_DRAFT_UNCOMPILED.
Two actual CR Dirichlet problems: V-cz and Zu-(n+1)+(n+1-t0)E.
The resulting Euler identity is passed to the retained ray ODE proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

theorem IsSolution.exponentialGradient_eq_linear_closedBall {n : ℕ} (hn : 2 ≤ n)
    {μ c : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (hb : ∀ x ∈ unitSphere n, ∀ i : Fin n,
      exponentialGradient u x i = (c : ℂ) * complexCoord x i) :
    ∀ x ∈ closedUnitBall n, ∀ i : Fin n,
      exponentialGradient u x i = (c : ℂ) * complexCoord x i := by
  intro x hx i
  let f : E n → ℂ := fun y => exponentialGradient u y i - (c : ℂ) * complexCoord y i
  have hs : ContDiffOn ℝ ∞ f (closedUnitBall n) :=
    (hu.exponentialGradient_contDiffOn_closedBall i).sub
      (contDiffOn_const.mul (smooth_complexCoord i).contDiffOn)
  have hCR (y : E n) (hy : y ∈ unitBall n) (j : Fin n) : partialBar j f y = 0 := by
    have hV := (((hu.exponentialGradient_contDiffOn_closedBall i).mono
      Metric.ball_subset_closedBall).contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
    have hz := (smooth_complexCoord i).differentiable (by simp) y
    have hcz : DifferentiableAt ℝ (fun z => (c : ℂ) * complexCoord z i) y :=
      (differentiableAt_const (c : ℂ)).mul hz
    change dz (realDirection j) (-imagDirection j)
      (fun z => exponentialGradient u z i - (c : ℂ) * complexCoord z i) y = 0
    rw [LogDetAux.dz_sub_differentiableAt hV hcz,
      ComplexMaximumAux.dz_const_mul_differentiableAt hz]
    change partialBar j (fun z => exponentialGradient u z i) y -
      (c : ℂ) * partialBar j (fun z => complexCoord z i) y = 0
    rw [hu.partialBar_exponentialGradient_eq_zero hn hy, partialBar_complexCoord]
    ring
  have hzero := hu.CR_zero_boundary (by omega) hs.continuousOn
    (hs.mono Metric.ball_subset_closedBall) hCR
    (by intro y hy; dsimp [f]; rw [hb y hy i]; ring) x hx
  exact sub_eq_zero.mp hzero

theorem IsSolution.exists_exponentialGradient_closedBall_data {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧ boundaryPolynomial n t₀ = μ ∧
      (∀ x ∈ unitSphere n, boundarySlope u x = t₀) ∧
      (∀ x ∈ closedUnitBall n, ∀ i : Fin n,
        exponentialGradient u x i = (-1 / ((n + 1 : ℝ) - t₀) : ℝ) * complexCoord x i) := by
  obtain ⟨t₀, ht, htk, hF, hSlope, hV⟩ := hu.exists_exponentialGradient_boundary_data hn
  exact ⟨t₀, ht, htk, hF, hSlope, hu.exponentialGradient_eq_linear_closedBall hn hV⟩

/-- The paper's Z u, with the project's actual Wirtinger derivatives. -/
noncomputable def complexEuler {n : ℕ} (u : E n → ℝ) (x : E n) : ℂ :=
  ∑ i : Fin n, partialZ i (fun y => (u y : ℂ)) x * complexCoord x i

theorem complexEuler_contDiffOn_closedBall {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) :
    ContDiffOn ℝ ∞ (complexEuler u) (closedUnitBall n) := by
  intro x hx
  have huC := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hu.contDiffAt hx)
  have hs : ContDiffAt ℝ ∞ (complexEuler u) x := by
    apply ContDiffAt.sum
    intro i _
    exact (smoothAt_dz huC (realDirection i) (imagDirection i)).mul
      (smooth_complexCoord i).contDiffAt
  exact hs.contDiffWithinAt

theorem complexEuler_on_sphere {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hb : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) : complexEuler u x = (boundarySlope u x : ℂ) := by
  have hnorm : ‖x‖ = 1 := by
    simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  unfold complexEuler
  simp_rw [sphere_partialZ hu hb hx]
  calc
    _ = (boundarySlope u x : ℂ) *
        (∑ i : Fin n, star (complexCoord x i) * complexCoord x i) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by rw [sum_star_complexCoord_mul, hnorm]; simp

theorem partialBar_complexEuler {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (j : Fin n) :
    partialBar j (complexEuler u) x =
      ∑ i : Fin n, complexHessian u x i j * complexCoord x i := by
  have huC : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hp (i : Fin n) : DifferentiableAt ℝ
      (fun y => partialZ i (fun z => (u z : ℂ)) y) x :=
    (smoothAt_dz huC (realDirection i) (imagDirection i)).differentiableAt (by simp)
  have hz (i : Fin n) := (smooth_complexCoord i).differentiable (by simp) x
  change dz (realDirection j) (-imagDirection j)
    (fun y => ∑ i : Fin n, partialZ i (fun z => (u z : ℂ)) y * complexCoord y i) x = _
  have hpz (i : Fin n) : DifferentiableAt ℝ
      (fun y => partialZ i (fun z => (u z : ℂ)) y * complexCoord y i) x :=
    (hp i).mul (hz i)
  rw [dz_sum_differentiableAt hpz]
  apply Finset.sum_congr rfl
  intro i _
  rw [dz_mul_differentiableAt (hp i) (hz i)]
  change partialBar j (partialZ i (fun y => (u y : ℂ))) x * complexCoord x i +
    partialZ i (fun y => (u y : ℂ)) x * partialBar j (fun y => complexCoord y i) x = _
  rw [partialBar_complexCoord, mul_zero, add_zero]
  change dz (realDirection j) (-imagDirection j)
    (dz (realDirection i) (imagDirection i) (fun y => (u y : ℂ))) x *
      complexCoord x i = _
  rw [dz_comm_at huC]
  rfl

theorem IsSolution.partialBar_expWeight_eq_mul_complexEuler {n : ℕ}
    {μ c : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n)
    (hV : ∀ i : Fin n, exponentialGradient u x i = (c : ℂ) * complexCoord x i)
    (j : Fin n) :
    partialBar j (fun y => (expWeight u y : ℂ)) x =
      (c : ℂ) * partialBar j (complexEuler u) x := by
  rw [← hu.exponentialGradient_dual (Metric.ball_subset_closedBall hx),
    partialBar_complexEuler (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
  simp_rw [hV]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The second Dirichlet problem fixes the holomorphic scalar Z u-E/c.
The implementation uses its denominator-free form Z u+(kappa-t0)E-kappa. -/
theorem IsSolution.complexEuler_eq_expWeight {n : ℕ} (hn : 2 ≤ n)
    {μ t₀ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (htk : t₀ < (n + 1 : ℝ))
    (hSlope : ∀ x ∈ unitSphere n, boundarySlope u x = t₀)
    (hV : ∀ x ∈ closedUnitBall n, ∀ i : Fin n,
      exponentialGradient u x i = (-1 / ((n + 1 : ℝ) - t₀) : ℝ) * complexCoord x i) :
    ∀ x ∈ closedUnitBall n,
      complexEuler u x = ((n + 1 : ℝ) - ((n + 1 : ℝ) - t₀) * expWeight u x : ℝ) := by
  let d : ℝ := (n + 1 : ℝ) - t₀
  let f : E n → ℂ := fun x => complexEuler u x -
    ((n + 1 : ℂ) - (d : ℂ) * (expWeight u x : ℂ))
  have hE : ContDiffOn ℝ ∞ (fun x => (expWeight u x : ℂ)) (closedUnitBall n) := by
    intro x hx
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiffAt_expWeight (hu.2.1.contDiffAt hx))).contDiffWithinAt
  have hZ := complexEuler_contDiffOn_closedBall hu.2.1
  have hs : ContDiffOn ℝ ∞ f (closedUnitBall n) :=
    hZ.sub (contDiffOn_const.sub (contDiffOn_const.mul hE))
  have hd : d ≠ 0 := by
    dsimp [d]
    exact ne_of_gt (sub_pos.mpr htk)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hc : (d : ℂ) * ((-1 / d : ℝ) : ℂ) = -1 := by
    push_cast
    field_simp [hdC]
  have hCR (x : E n) (hx : x ∈ unitBall n) (j : Fin n) : partialBar j f x = 0 := by
    have hZa := ((hZ.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    have hEa := ((hE.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    have hgrad := hu.partialBar_expWeight_eq_mul_complexEuler hx
      (hV x (Metric.ball_subset_closedBall hx)) j
    have hdE : DifferentiableAt ℝ
        (fun y => (d : ℂ) * (expWeight u y : ℂ)) x :=
      (differentiableAt_const (d : ℂ)).mul hEa
    have hkE : DifferentiableAt ℝ
        (fun y => (n + 1 : ℂ) - (d : ℂ) * (expWeight u y : ℂ)) x :=
      (differentiableAt_const (n + 1 : ℂ)).sub hdE
    change dz (realDirection j) (-imagDirection j)
      (fun y => complexEuler u y - ((n + 1 : ℂ) - (d : ℂ) * (expWeight u y : ℂ))) x = 0
    rw [LogDetAux.dz_sub_differentiableAt hZa hkE,
      LogDetAux.dz_sub_differentiableAt (differentiableAt_const _)
        hdE,
      ComplexMaximumAux.dz_const_mul_differentiableAt hEa]
    change partialBar j (complexEuler u) x -
      (dz (realDirection j) (-imagDirection j) (fun _ : E n => (n + 1 : ℂ)) x -
        (d : ℂ) * partialBar j (fun y => (expWeight u y : ℂ)) x) = 0
    have hconst : dz (realDirection j) (-imagDirection j)
        (fun _ : E n => (n + 1 : ℂ)) x = 0 := by simp [dz, rd]
    rw [hconst, hgrad]
    change partialBar j (complexEuler u) x -
      (0 - (d : ℂ) * (((-1 / d : ℝ) : ℂ) * partialBar j (complexEuler u) x)) = 0
    rw [← mul_assoc, hc]
    ring
  have hb (x : E n) (hx : x ∈ unitSphere n) : f x = 0 := by
    have hEx : expWeight u x = 1 := by simp [expWeight, hu.2.2.2.2 x hx]
    dsimp [f]
    rw [complexEuler_on_sphere hu.2.1 hu.2.2.2.2 hx, hSlope x hx, hEx]
    dsimp [d]
    push_cast
    ring
  have hz := hu.CR_zero_boundary (by omega) hs.continuousOn
    (hs.mono Metric.ball_subset_closedBall) hCR hb
  intro x hx
  have h := sub_eq_zero.mp (hz x hx)
  simpa [d] using h

/-- Original solutions satisfy the actual Euler identity required by RayODE. -/
theorem IsSolution.exists_euler_identity {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧
      ∀ x ∈ unitBall n, fderiv ℝ u x x =
        2 * ((n + 1 : ℝ) - ((n + 1 : ℝ) - t₀) * expWeight u x) := by
  obtain ⟨t₀, ht, htk, _, hSlope, hV⟩ := hu.exists_exponentialGradient_closedBall_data hn
  have hZ := hu.complexEuler_eq_expWeight hn htk hSlope hV
  refine ⟨t₀, ht, htk, ?_⟩
  intro x hx
  rw [fderiv_eq_wirtinger
    ((hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)).differentiableAt (by simp))]
  change 2 * (complexEuler u x).re = _
  rw [hZ x (Metric.ball_subset_closedBall hx), Complex.ofReal_re]

theorem IsSolution.radial_classification {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    ∃ b : ℝ, 0 < b ∧ EqOn u (radialPotential n b) (closedUnitBall n) ∧
      μ = radialCoefficient n b := by
  obtain ⟨t₀, ht, htk, hEuler⟩ := hu.exists_euler_identity hn
  exact hu.radial_of_euler_identity ht htk hEuler

#print axioms IsSolution.exponentialGradient_eq_linear_closedBall
#print axioms IsSolution.exists_euler_identity
#print axioms IsSolution.radial_classification

end KEBall
