import KEBall.DirichletHessianL2Limit
import KEBall.DirichletHessianUniformBounds
import KEBall.DirichletCompactness
import KEBall.DirichletSobolevClassical

/-! Compactness of the complex Hessian for uniformly elliptic Dirichlet sequences. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff MatrixOrder Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- A unit-direction bound for the real Hessian bounds all complex Hessian entries. -/
theorem norm_complexHessian_le_of_unit_bound {n : ℕ}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ v : E n, ‖v‖ = 1 → |realHessian u x v v| ≤ D) :
    ‖complexHessian u x‖ ≤ D := by
  apply (Matrix.norm_le_iff hD).mpr
  intro i j
  have hH := norm_realHessian_le_of_unit_test hu hD h
  have hEntry (v w : E n) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ‖realHessian u x v w‖ ≤ D := by
    exact ((realHessian u x v).le_opNorm w).trans (by
      rw [hw, mul_one]
      exact ((realHessian u x).le_opNorm v).trans (by rwa [hv, mul_one]))
  have hr (k : Fin n) : ‖realDirection k‖ = 1 := by simp [realDirection]
  have hi (k : Fin n) : ‖imagDirection k‖ = 1 := by simp [imagDirection]
  rw [complexHessian_real_entry_C2 (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    norm_mul, norm_inv, show ‖(4 : ℂ)‖ = 4 from by norm_num]
  have h₁ := hEntry _ _ (hr i) (hr j)
  have h₂ := hEntry _ _ (hi i) (hi j)
  have h₃ := hEntry _ _ (hr i) (hi j)
  have h₄ := hEntry _ _ (hi i) (hr j)
  have hTriangle :
      ‖(realHessian u x (realDirection i) (realDirection j) : ℂ) +
        (realHessian u x (imagDirection i) (imagDirection j) : ℂ) +
        Complex.I * ((realHessian u x (realDirection i) (imagDirection j) : ℂ) -
          (realHessian u x (imagDirection i) (realDirection j) : ℂ))‖ ≤ D + D + (D + D) := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_add_le _ _).trans (by simpa only [Complex.norm_real] using add_le_add h₁ h₂)
    · rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_sub_le _ _).trans (by simpa only [Complex.norm_real] using add_le_add h₃ h₄)
  exact (mul_le_mul_of_nonneg_left hTriangle (by norm_num)).trans_eq (by ring)

/-- Uniform convergence of the density and gradient, together with the
uniform second derivative bound, forces strong (L^2) convergence of
the complex Hessians along the entire sequence. -/
theorem exists_complexHessian_L2_limit_of_dirichlet_data {n : ℕ} (hn : 0 < n)
    {u f : ℕ → E n → ℝ} {p : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hu : ∀ j, SmoothNear (closedUnitBall n) (u j))
    (hf : ∀ j, SmoothNear (closedUnitBall n) (f j))
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).det.re = f j x)
    (hG : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) G atTop (closedUnitBall n))
    (hF : TendstoUniformlyOn f p atTop (closedUnitBall n))
    {a D : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hLower : ∀ j x, x ∈ unitBall n → a ^ n ≤ f j x)
    (hBound : ∀ j x, x ∈ closedUnitBall n → ∀ v : E n, ‖v‖ = 1 →
      |realHessian (u j) x v v| ≤ D) :
    ∃ H : DirichletBallL2 n (DirichletHessianCoordinates n),
      (∃ Q : ℕ → DirichletBallL2 n (DirichletHessianCoordinates n), Tendsto Q atTop (𝓝 H) ∧
        ∀ j, Q j =ᵐ[ν[n]] fun x => dirichletHessianCoordinates (complexHessian (u j) x)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ x ∂ν[n], Tendsto (fun j => dirichletHessianCoordinates (complexHessian (u (φ j)) x))
          atTop (𝓝 (H x)) := by
  obtain ⟨M, hM, hOp⟩ := exists_norm_dirichletCofactorOperator_bound (n := n) D
  obtain ⟨K, hK, hTrace⟩ := exists_abs_trace_inverse_sub_bound (n := n) (C := D) (pow_pos ha n)
  let c := (D / 2)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have hH (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) : ‖complexHessian (u j) x‖ ≤ D :=
    norm_complexHessian_le_of_unit_bound ((hu j).contDiffAt hx) hD.le (hBound j x hx)
  have hInv (j : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian (u j) x)⁻¹ := by
    change (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian (u j) x)⁻¹
    apply smul_one_le_inverse_of_eigenvalues_le (huP j x hx) (show 0 < D / 2 by positivity)
    intro i
    exact (complexHessian_eigenvalues_bounds_of_dirichlet_det (hu j) (hf j) (huP j) (hEq j)
      ha hD (hLower j) (fun y hy v hv => (le_abs_self _).trans (hBound j y hy v hv))
      (ball_subset_closedBall hx) i).2
  have hPair (ε : ℝ) (hε : 0 < ε) (j k : ℕ)
      (hGrad : ∀ x ∈ unitSphere n, ‖fderiv ℝ (u k) x - fderiv ℝ (u j) x‖ ≤ ε)
      (hDensity : ∀ x ∈ unitBall n, |f k x - f j x| ≤ ε) :
      (∫ x in unitBall n, ∑ i, ∑ l, ‖(complexHessian (u j) x - complexHessian (u k) x) i l‖ ^ 2 ∂volume0 n) ≤
        ((4 * n : ℝ) * M * ε + ε * K) / (a ^ n * c ^ 2) := by
    obtain ⟨U, hU, hSub, hUC⟩ := hu j
    obtain ⟨V, hV, hSub', hVC⟩ := hu k
    have h := integral_sq_complexHessian_sub_le_of_density_and_gradient_bound hn
      (hU.inter hV) (subset_inter hSub hSub') (hUC.mono inter_subset_left) (hVC.mono inter_subset_right)
      (huP j) (huP k) (d := a ^ n) hc.le hM hε.le
      (fun x hx => (hLower j x hx).trans_eq (hEq j x hx).symm)
      (fun x hx => ⟨hInv j x hx, hInv k x hx⟩)
      (fun x hx => ⟨hOp _ x (hH j x (sphere_subset_closedBall hx)),
        hOp _ x (hH k x (sphere_subset_closedBall hx))⟩)
      hGrad (fun x hx => by rw [hEq j x hx, hEq k x hx]; exact hDensity x hx)
      (fun x hx => hTrace _ _ (hH j x (ball_subset_closedBall hx))
        (hH k x (ball_subset_closedBall hx)) ((hLower k x hx).trans_eq (hEq k x hx).symm))
    rw [mul_comm (a ^ n * c ^ 2)] at h
    apply (le_div_iff₀ (by positivity : 0 < a ^ n * c ^ 2)).mpr
    have he :
        (∫ x in unitBall n, ∑ i, ∑ l, ‖(complexHessian (u j) x - complexHessian (u k) x) i l‖ ^ 2 ∂volume0 n) =
          (∫ x in unitBall n, ∑ i, ∑ l, ‖(complexHessian (u k) x - complexHessian (u j) x) i l‖ ^ 2 ∂volume0 n) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x _
      simp only [Matrix.sub_apply, norm_sub_rev]
    rw [he]
    exact h
  apply exists_complexHessian_L2_limit_of_pairwise_integral_bound hn
  · intro j i k
    obtain ⟨U, hU, hSub, hUC⟩ := hu j
    exact (complexHessian_contDiffOn hU hUC i k).continuousOn.mono hSub
  intro δ hδ
  let C : ℝ := (4 * n : ℝ) * M + K
  let ε : ℝ := (δ * (a ^ n * c ^ 2)) / (C + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hDen : 0 < a ^ n * c ^ 2 := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hT : ∀ᶠ j in atTop,
      (∀ x ∈ closedUnitBall n, dist (p x) (f j x) < ε / 2) ∧
      ∀ x ∈ closedUnitBall n, dist (G x) (fderiv ℝ (u j) x) < ε / 2 :=
    ((Metric.tendstoUniformlyOn_iff.mp hF) _ (half_pos hε)).and
      ((Metric.tendstoUniformlyOn_iff.mp hG) _ (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hT
  refine ⟨N, fun j hj k hk => ?_⟩
  have hG' (x : E n) (hx : x ∈ unitSphere n) : ‖fderiv ℝ (u k) x - fderiv ℝ (u j) x‖ ≤ ε := by
    have h := dist_triangle (fderiv ℝ (u k) x) (G x) (fderiv ℝ (u j) x)
    rw [dist_comm (fderiv ℝ (u k) x) (G x)] at h
    rw [← dist_eq_norm]
    linarith only [h, (hN k hk).2 x (sphere_subset_closedBall hx),
      (hN j hj).2 x (sphere_subset_closedBall hx)]
  have hF' (x : E n) (hx : x ∈ unitBall n) : |f k x - f j x| ≤ ε := by
    have h := dist_triangle (f k x) (p x) (f j x)
    rw [dist_comm (f k x) (p x)] at h
    rw [← Real.dist_eq]
    linarith only [h, (hN k hk).1 x (ball_subset_closedBall hx),
      (hN j hj).1 x (ball_subset_closedBall hx)]
  apply (hPair ε hε j k hG' hF').trans_lt
  apply (div_lt_iff₀ hDen).mpr
  have he : ε * (C + 1) = δ * (a ^ n * c ^ 2) :=
    div_mul_cancel₀ _ (by positivity)
  have hεC : (4 * n : ℝ) * M * ε + ε * K = ε * C := by dsimp [C]; ring
  rw [hεC, ← he]
  exact mul_lt_mul_of_pos_left (lt_add_one C) hε

end KEBall
