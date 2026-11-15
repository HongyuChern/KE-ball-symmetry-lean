import KEBall.DirichletNormalFiniteLpJets

/-! Compactness supplies the uniform inverse normal slope used by finite Lp recovery. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem continuousOn_hermitianRankOneDetSlope {n m : ℕ} {K : Set (E n)}
    {A : E n → Matrix (Fin m) (Fin m) ℂ} {z : E n → Fin m → ℂ}
    (hA : ContinuousOn A K) (hz : ContinuousOn z K) :
    ContinuousOn (fun x => hermitianRankOneDetSlope (A x) (z x)) K := by
  apply (contDiffOn_hermitianRankOneDetSlope (r := 0) _ _).continuousOn
  · intro i j
    exact contDiffOn_zero.mpr ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hA))
  · intro i
    exact contDiffOn_zero.mpr ((continuous_apply i).comp_continuousOn hz)

theorem exists_uniform_inverse_hermitianRankOneDetSlope {n m : ℕ} {K : Set (E n)}
    (hK : IsCompact K) {A : E n → Matrix (Fin m) (Fin m) ℂ} {z : E n → Fin m → ℂ}
    (hA : ContinuousOn A K) (hz : ContinuousOn z K)
    (hPos : ∀ x ∈ K, (A x).PosDef) (hZ : ∀ x ∈ K, z x ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖(hermitianRankOneDetSlope (A x) (z x))⁻¹‖ ≤ C := by
  have hS := continuousOn_hermitianRankOneDetSlope hA hz
  have hInv : ContinuousOn (fun x => (hermitianRankOneDetSlope (A x) (z x))⁻¹) K :=
    hS.inv₀ (fun x hx => (hermitianRankOneDetSlope_pos (hPos x hx) (hZ x hx)).ne')
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hInv
  exact ⟨max C 0,le_max_right _ _,fun x hx => (hC x hx).trans (le_max_left _ _)⟩

theorem exists_positive_realHessian_rankOne_reference {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) {B D : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {t : E n → ℝ}
    (ht : ContinuousOn t K)
    (hEq : ∀ x ∈ K, B x = D x+t x • (innerSL ℝ x).smulRight (innerSL ℝ x))
    (hPos : ∀ x ∈ K, (complexHessianOfRealBilinear (B x)).PosDef) :
    ∃ c : ℝ, ∀ x ∈ K, (complexHessianOfRealBilinear
      (D x+c • (innerSL ℝ x).smulRight (innerSL ℝ x))).PosDef := by
  obtain ⟨c,hc⟩ := hK.exists_bound_of_continuousOn ht
  refine ⟨c,fun x hx => ?_⟩
  have hct : 0 ≤ c-t x := sub_nonneg.mpr ((le_abs_self (t x)).trans (by simpa using hc x hx))
  have hEq' : D x+c • (innerSL ℝ x).smulRight (innerSL ℝ x) =
      B x+(c-t x) • (innerSL ℝ x).smulRight (innerSL ℝ x) := by
    rw [hEq x hx]
    rw [add_assoc,← add_smul]
    congr 2
    ring
  rw [hEq',complexHessianOfRealBilinear_add_rankOne]
  apply (hPos x hx).add_posSemidef
  apply (Matrix.posSemidef_vecMulVec_star_self (complexCoord x)).smul
  exact Complex.zero_le_real.mpr (div_nonneg hct (by norm_num))

end KEBall
