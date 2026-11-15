import KEBall.DirichletZeroBoundaryStability
import KEBall.DirichletHessianCompactness

/-! Uniform density stability for the smooth Dirichlet problem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff MatrixOrder Matrix.Norms.Elementwise

namespace KEBall

private theorem exists_norm_matrix_inverse_le {n : ℕ} {d C : ℝ} (hd : 0 < d) :
    ∃ K ≥ (0 : ℝ), ∀ B : Matrix (Fin n) (Fin n) ℂ,
      ‖B‖ ≤ C → d ≤ B.det.re → ‖B⁻¹‖ ≤ K := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let T : Set M := closedBall 0 C ∩ {B | d ≤ B.det.re}
  have hT : IsCompact T := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const
    (Complex.continuous_re.comp continuous_id.matrix_det))
  have hInv : ContinuousOn (Inv.inv : M → M) T := by
    intro B hB
    have hD : B.det ≠ 0 := by
      intro h
      have he : d ≤ B.det.re := hB.2
      rw [h, Complex.zero_re] at he
      exact (not_le_of_gt hd) he
    exact (continuousAt_matrix_inv B (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hD)).continuousWithinAt
  obtain ⟨K, hK⟩ := hT.exists_bound_of_continuousOn hInv
  exact ⟨max K 0, le_max_right _ _, fun B hB hD =>
    (hK B ⟨mem_closedBall_zero_iff.mpr hB, hD⟩).trans (le_max_left _ _)⟩

/-- Uniform positive lower and upper density bounds and an upper real Hessian
bound give a single (L^2) Lipschitz constant for the complex Hessians of
smooth zero-boundary solutions. -/
theorem exists_integral_sq_complexHessian_sub_le_of_dirichlet_data {n : ℕ} (hn : 0 < n)
    {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    ∃ C ≥ (0 : ℝ), ∀ {u v f g : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) v →
      SmoothNear (closedUnitBall n) f → SmoothNear (closedUnitBall n) g →
      (∀ x ∈ unitSphere n, u x = 0) → (∀ x ∈ unitSphere n, v x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, (complexHessian v x).det.re = g x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ unitBall n, a ^ n ≤ g x ∧ g x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian v x w w| ≤ D) →
      (∫ x in unitBall n, ∑ i, ∑ j, ‖(complexHessian v x - complexHessian u x) i j‖ ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n, (g x - f x) ^ 2 ∂volume0 n := by
  obtain ⟨K, hK, hNorm⟩ := exists_norm_matrix_inverse_le (n := n) (C := D) (pow_pos ha n)
  let c : ℝ := (D / 2)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  let C : ℝ := (K * (n : ℝ) ^ 2) ^ 2 / (a ^ n * c ^ 2) ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u v f g hu hv hf hg hu0 hv0 huP hvP huEq hvEq hfB hgB huD hvD
  have huDen (x : E n) (hx : x ∈ unitBall n) :
      a ^ n ≤ (complexHessian u x).det.re ∧ (complexHessian u x).det.re ≤ b ^ n := by
    rw [huEq x hx]
    exact hfB x hx
  have hvDen (x : E n) (hx : x ∈ unitBall n) :
      a ^ n ≤ (complexHessian v x).det.re ∧ (complexHessian v x).det.re ≤ b ^ n := by
    rw [hvEq x hx]
    exact hgB x hx
  have hsU := (Cegrell.quadratic_and_boundarySlope_bounds hn hu
    (fun x hx => (huP x hx).posSemidef) hu0 ha hb huDen).2
  have hsV := (Cegrell.quadratic_and_boundarySlope_bounds hn hv
    (fun x hx => (hvP x hx).posSemidef) hv0 ha hb hvDen).2
  have hInv {w p : E n → ℝ} (hw : SmoothNear (closedUnitBall n) w)
      (hp : SmoothNear (closedUnitBall n) p)
      (hwP : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
      (hEq : ∀ x ∈ unitBall n, (complexHessian w x).det.re = p x)
      (hLower : ∀ x ∈ unitBall n, a ^ n ≤ p x)
      (hBound : ∀ x ∈ closedUnitBall n, ∀ z : E n, ‖z‖ = 1 → |realHessian w x z z| ≤ D)
      (x : E n) (hx : x ∈ unitBall n) :
      (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian w x)⁻¹ := by
    change (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian w x)⁻¹
    apply smul_one_le_inverse_of_eigenvalues_le (hwP x hx) (show 0 < D / 2 by positivity)
    intro i
    exact (complexHessian_eigenvalues_bounds_of_dirichlet_det hw hp hwP hEq
      ha hD hLower (fun y hy z hz => (le_abs_self _).trans (hBound y hy z hz))
      (ball_subset_closedBall hx) i).2
  have hdet (x : E n) (hx : x ∈ unitSphere n) :
      (complexHessian u x).det ≠ 0 ∧ (complexHessian v x).det ≠ 0 :=
    ⟨((Matrix.isUnit_iff_isUnit_det _).mp (dirichlet_posDef_on_closedBall hu hf huP huEq ha
      (fun y hy => (hfB y hy).1) (sphere_subset_closedBall hx)).isUnit).ne_zero,
      ((Matrix.isUnit_iff_isUnit_det _).mp (dirichlet_posDef_on_closedBall hv hg hvP hvEq ha
      (fun y hy => (hgB y hy).1) (sphere_subset_closedBall hx)).isUnit).ne_zero⟩
  obtain ⟨U, hU, hSubU, huU⟩ := hu
  obtain ⟨V, hV, hSubV, hvV⟩ := hv
  have h := integral_sq_complexHessian_sub_le_of_zero_boundary hn
    (hU.inter hV) (subset_inter hSubU hSubV) (huU.mono inter_subset_left) (hvV.mono inter_subset_right)
    huP hvP hu0 hv0 (fun x hx => ⟨ha.trans_le (hsU x hx).1, ha.trans_le (hsV x hx).1⟩)
    hdet hc (pow_pos ha n) hK (fun x hx => (huDen x hx).1)
    (fun x hx => ⟨hInv ⟨U, hU, hSubU, huU⟩ hf huP huEq (fun y hy => (hfB y hy).1) huD x hx,
      hInv ⟨V, hV, hSubV, hvV⟩ hg hvP hvEq (fun y hy => (hgB y hy).1) hvD x hx⟩)
    (fun x hx => hNorm _
      (norm_complexHessian_le_of_unit_bound (hvV.contDiffAt (hV.mem_nhds (hSubV (ball_subset_closedBall hx))))
        hD.le (hvD x (ball_subset_closedBall hx))) (hvDen x hx).1)
  have he :
      (∫ x in unitBall n, ((complexHessian v x).det.re - (complexHessian u x).det.re) ^ 2 ∂volume0 n) =
        ∫ x in unitBall n, (g x - f x) ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    simp only [huEq x hx, hvEq x hx]
  rw [he, mul_comm ((a ^ n * c ^ 2) ^ 2)] at h
  have hDen : 0 < (a ^ n * c ^ 2) ^ 2 := by positivity
  exact ((le_div_iff₀ hDen).mpr h).trans_eq (by dsimp only [C]; rw [div_mul_eq_mul_div])

end KEBall
