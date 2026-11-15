import KEBall.MoserTrudingerGibbsLogTrace
import KEBall.MoserTrudingerGibbsBoundaryHessian
import KEBall.DirichletCofactorMaximum
import KEBall.DirichletUniformEllipticity

/-! The actual global trace estimate with explicit quadratic dependence on the previous gradient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter Metric Set Matrix
open scoped ContDiff BigOperators ComplexOrder Matrix Matrix.Norms.Elementwise Topology
namespace KEBall

theorem trace_complexHessian_le_of_realHessian_bound {n : ℕ}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x) {D : ℝ}
    (hD : ∀ v : E n, ‖v‖=1 → realHessian u x v v≤D) :
    (complexHessian u x).trace.re≤(n : ℝ)*D/2 := by
  have hEntry (i : Fin n) : (complexHessian u x i i).re≤D/2 := by
    have hr := hD (realDirection i) (by simp [realDirection])
    have hi := hD (imagDirection i) (by simp [imagDirection])
    rw [complexHessian_real_entry hu,realHessian_symm hu (realDirection i) (imagDirection i),sub_self]
    simp only [Complex.ofReal_zero,mul_zero,add_zero,Complex.mul_re,Complex.add_re,
      Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero,zero_mul,sub_zero]
    norm_num [Complex.inv_re]
    linarith only [hr,hi]
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum]
  calc
    _ ≤ ∑ _ : Fin n, D/2 := Finset.sum_le_sum fun i _ => hEntry i
    _ = (n : ℝ)*D/2 := by simp; ring

namespace MoserTrudinger

theorem trace_complexHessian_le_boundary_of_gibbs {n : ℕ} (hn : 0<n)
    {γ B C : ℝ} (hγ : 0≤γ) (hC : 0<C) {u q : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (hu0 : ∀ y∈unitSphere n, u y=0) (hq0 : ∀ y∈unitSphere n, q y=0)
    (huP : ∀ y∈closedUnitBall n, (complexHessian u y).PosDef)
    (hqP : ∀ y∈unitBall n, (complexHessian q y).PosSemidef)
    (hEq : ∀ y∈unitBall n, (complexHessian u y).det.re=gibbsDensity γ q y)
    (hqLow : ∀ y∈closedUnitBall n, -B≤q y)
    (hBoundary : ∀ y∈unitSphere n, (complexHessian u y).trace.re≤C) :
    ∀ x∈closedUnitBall n, (complexHessian u x).trace.re≤Real.exp (γ*B)*C := by
  letI : NeZero n := ⟨hn.ne'⟩
  let T : E n → ℝ := fun y => (complexHessian u y).trace.re
  have hT : ContDiff ℝ ∞ T := contDiff_complexHessian_trace_real hu
  have hTp (x : E n) (hx : x∈closedUnitBall n) : 0<T x :=
    dirichlet_posDef_trace_re_pos (huP x hx)
  let U : Set (E n) := {x | 0<T x}
  have hU : IsOpen U := isOpen_lt continuous_const hT.continuous
  have hSub : closedUnitBall n⊆U := hTp
  have hLog : ContDiffOn ℝ ∞ (fun y => Real.log (T y)) U :=
    hT.contDiffOn.log (fun x hx => (show 0<T x from hx).ne')
  have hw : SmoothNear (closedUnitBall n) (fun y => Real.log (T y)+γ*q y) :=
    ⟨U,hU,hSub,hLog.add (contDiffOn_const.mul hq.contDiffOn)⟩
  have hMax := le_boundary_bound_of_complexLaplacian_nonneg hn
    (u := u) ⟨univ,isOpen_univ,subset_univ _,hu.contDiffOn⟩ hu0
    (fun y hy => huP y (ball_subset_closedBall hy)) hw
    (fun y hy => complexLaplacian_log_trace_gibbs_nonneg hn hγ hu hq
      (fun z hz => huP z (ball_subset_closedBall hz)) hqP hEq hy)
    (C := Real.log C) (fun y hy => by
      rw [hq0 y hy,mul_zero,add_zero]
      exact Real.log_le_log (hTp y (sphere_subset_closedBall hy)) (hBoundary y hy))
  intro x hx
  have hLow := mul_le_mul_of_nonneg_left (hqLow x hx) hγ
  have hLogBound : Real.log (T x)≤Real.log C+γ*B := by
    have h := hMax x hx
    linarith only [h,hLow]
  have h := Real.exp_le_exp.mpr hLogBound
  rw [Real.exp_log (hTp x hx),Real.exp_add,Real.exp_log hC,mul_comm C] at h
  exact h

theorem exists_uniform_trace_bound_of_gibbs_density {n : ℕ} (hn : 0<n)
    {γ a b B : ℝ} (hγ : 0≤γ) (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ (u q : E n → ℝ),
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ q →
      (∀ x∈unitSphere n, u x=0) → (∀ x∈unitSphere n, q x=0) →
      (∀ x∈unitBall n, (complexHessian u x).PosDef) →
      (∀ x∈unitBall n, (complexHessian q x).PosSemidef) →
      (∀ x∈unitBall n, (complexHessian u x).det.re=gibbsDensity γ q x) →
      (∀ x∈unitBall n, a^n≤gibbsDensity γ q x ∧ gibbsDensity γ q x≤b^n) →
      (∀ x∈closedUnitBall n, -B≤q x) →
      ∀ G : ℝ, 0≤G → (∀ x∈unitBall n, ‖fderiv ℝ q x‖≤G) →
      ∀ x∈closedUnitBall n, (complexHessian u x).trace.re≤C*(1+G^2) := by
  obtain ⟨D,hD,hBoundary⟩ := exists_uniform_boundary_hessian_bound_of_gibbs_density hn hγ ha hb
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  refine ⟨Real.exp (γ*B)*((n : ℝ)*D/2),by positivity,?_⟩
  intro u q hu hq hu0 hq0 huP hqP hEq hDensity hqLow G hG hGrad x hx
  have huN : SmoothNear (closedUnitBall n) u := ⟨univ,isOpen_univ,subset_univ _,hu.contDiffOn⟩
  have hf : SmoothNear (closedUnitBall n) (gibbsDensity γ q) :=
    ⟨univ,isOpen_univ,subset_univ _,(((contDiff_const.mul hq).exp).div_const _).contDiffOn⟩
  have hPos (y : E n) (hy : y∈closedUnitBall n) :=
    dirichlet_posDef_on_closedBall huN hf huP hEq ha (fun z hz => (hDensity z hz).1) hy
  have hBound (y : E n) (hy : y∈unitSphere n) :
      (complexHessian u y).trace.re≤(n : ℝ)*(D*(1+G^2))/2 := by
    apply trace_complexHessian_le_of_realHessian_bound hu.contDiffAt
    intro v hv
    exact (le_abs_self _).trans (hBoundary u q huN hq hu0 huP hEq hDensity G hG hGrad y hy v hv)
  have h := trace_complexHessian_le_boundary_of_gibbs hn hγ (by positivity)
    hu hq hu0 hq0 hPos hqP hEq hqLow hBound x hx
  exact h.trans_eq (by ring)

end MoserTrudinger
end KEBall
