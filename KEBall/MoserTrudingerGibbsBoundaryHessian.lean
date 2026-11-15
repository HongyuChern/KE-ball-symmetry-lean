import KEBall.MoserTrudingerGibbsDensityBounds
import KEBall.DirichletBoundaryHessian

/-! The boundary Hessian bound retains the previous iterate's gradient explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology
namespace KEBall.MoserTrudinger

private theorem boundary_hessian_polynomial_bound {n : ℕ} (hn : 0<n)
    {γ a b : ℝ} (hγ : 0≤γ) (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ G : ℝ, 0≤G →
      2*b+4*b*((3*(γ*G)+1)/n)+
        (2*b+4*(b^n/a^(n-1)+(b*((3*(γ*G)+1)/n))^2/(4*a))) ≤ C*(1+G^2) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  let d := (3*γ+1)/(n : ℝ)
  let A := 4*b+4*b^n/a^(n-1)
  let C := A+8*b*d+2*(b*d)^2/a
  have hd : 0<d := by dsimp [d]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro G hG
  let c := (3*(γ*G)+1)/(n : ℝ)
  have hc0 : 0≤c := by dsimp [c]; positivity
  have hc : c≤d*(1+G) := by
    calc
      c ≤ ((3*γ+1)*(1+G))/(n : ℝ) := by
        apply div_le_div_of_nonneg_right _ hnR.le
        nlinarith only [hγ,hG]
      _ = d*(1+G) := by dsimp [d]; ring
  have hGlin : 1+G≤2*(1+G^2) := by nlinarith only [sq_nonneg (G-1)]
  have hGsq : (1+G)^2≤2*(1+G^2) := by nlinarith only [sq_nonneg (G-1)]
  have hcLin : 4*b*c≤(8*b*d)*(1+G^2) := by
    calc
      4*b*c ≤ 4*b*(d*(1+G)) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 4*b*(d*(2*(1+G^2))) := by gcongr
      _ = (8*b*d)*(1+G^2) := by ring
  have hcSq : (b*c)^2/a≤(2*(b*d)^2/a)*(1+G^2) := by
    have hs := pow_le_pow_left₀ (mul_nonneg hb.le hc0)
      (mul_le_mul_of_nonneg_left hc hb.le) 2
    have hs' : (b*c)^2≤(b*d)^2*(1+G)^2 := hs.trans_eq (by ring)
    calc
      (b*c)^2/a ≤ ((b*d)^2*(1+G)^2)/a := div_le_div_of_nonneg_right hs' ha.le
      _ ≤ ((b*d)^2*(2*(1+G^2)))/a := by gcongr
      _ = (2*(b*d)^2/a)*(1+G^2) := by ring
  have hAC : A≤A*(1+G^2) := by nlinarith only [mul_nonneg hA.le (sq_nonneg G)]
  have he : 2*b+4*b*c+(2*b+4*(b^n/a^(n-1)+(b*c)^2/(4*a)))=
      A+4*b*c+(b*c)^2/a := by dsimp [A]; ring
  change 2*b+4*b*c+(2*b+4*(b^n/a^(n-1)+(b*c)^2/(4*a)))≤C*(1+G^2)
  rw [he]
  dsimp only [C]
  nlinarith only [hAC,hcLin,hcSq]

/-- The constant is independent of the two potentials and of the gradient bound.
The previous potential's gradient occurs only in the explicit quadratic factor. -/
theorem exists_uniform_boundary_hessian_bound_of_gibbs_density {n : ℕ} (hn : 0<n)
    {γ a b : ℝ} (hγ : 0≤γ) (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ (u q : E n → ℝ),
      SmoothNear (closedUnitBall n) u → ContDiff ℝ ∞ q →
      (∀ x∈unitSphere n, u x=0) →
      (∀ x∈unitBall n, (complexHessian u x).PosDef) →
      (∀ x∈unitBall n, (complexHessian u x).det.re=gibbsDensity γ q x) →
      (∀ x∈unitBall n, a^n≤gibbsDensity γ q x ∧ gibbsDensity γ q x≤b^n) →
      ∀ G : ℝ, 0≤G → (∀ x∈unitBall n, ‖fderiv ℝ q x‖≤G) →
      ∀ x∈unitSphere n, ∀ v : E n, ‖v‖=1 →
        |realHessian u x v v|≤C*(1+G^2) := by
  obtain ⟨C,hC,hPoly⟩ := boundary_hessian_polynomial_bound hn hγ ha hb
  refine ⟨C,hC,?_⟩
  intro u q hu hq hu0 huP hEq hDensity G hG hGrad x hx v hv
  have hf : SmoothNear (closedUnitBall n) (gibbsDensity γ q) :=
    ⟨univ,isOpen_univ,subset_univ _,(((contDiff_const.mul hq).exp).div_const _).contDiffOn⟩
  have hLog (y : E n) (hy : y∈unitBall n) :
      ‖fderiv ℝ (fun z => Real.log (gibbsDensity γ q z)) y‖≤γ*G := by
    rw [fderiv_log_gibbsDensity hn γ hq,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (hGrad y hy) hγ
  exact (abs_realHessian_self_le_on_sphere_of_dirichlet_det hn hu hf hu0 huP hEq
    ha hb (mul_nonneg hγ hG) hDensity hLog hx hv).trans (hPoly G hG)

end KEBall.MoserTrudinger
