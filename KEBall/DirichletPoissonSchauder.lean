import KEBall.DirichletSchauderEstimateMajorant
import KEBall.DirichletSchauderHessianGauge
import DifferentialGeometry.Analysis.Schauder.Cutoff.Elliptic.Existence

/-! The actual real Hessian of a compactly supported smooth function is
controlled by its supremum and its actual Poisson source. The common
constant is chosen before the function and does not use a Hessian bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open Metric Set
open scoped ContDiff Laplacian NNReal

noncomputable section
namespace KEBall
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean

theorem exists_uniform_compactSupport_poisson_hessian_holder {n : ℕ} (hn : 0 < n)
    (α K L A : ℝ≥0) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ (u : E n → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ x, ‖u x‖ ≤ A) → (∀ x, ‖Δ u x‖ ≤ L) → HolderWith K α (Δ u) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C) ∧
        HolderWith C α (fderiv ℝ (fderiv ℝ u)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let C : ℝ≥0 := heatSupSchauderConst 1 (BoundedContinuousFunction.const (E n) (A : ℝ)) +
    heatDuhamelConstSchauderConst (V := E n) α K L 1
  refine ⟨C, ?_⟩
  intro u hu hc hA hL hK
  have hu1 : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hu2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hu1.fderiv_right (by simp)
  let u0 := compactSupportBoundedContinuousFunction u hu.continuous hc
  let u1 := compactSupportBoundedContinuousFunction (fderiv ℝ u)
    hu1.continuous (hc.fderiv ℝ)
  let u2 := compactSupportBoundedContinuousFunction (fderiv ℝ (fderiv ℝ u))
    hu2.continuous ((hc.fderiv ℝ).fderiv ℝ)
  have hEq : (coreLap u2 : E n → ℝ) = Δ u := by
    funext x
    rw [coreLap_apply, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  have h0 : ‖u0‖₊ ≤ A := (BoundedContinuousFunction.norm_le A.coe_nonneg).mpr hA
  have h2 : ‖coreLap u2‖ ≤ L := (BoundedContinuousFunction.norm_le L.coe_nonneg).mpr
    (fun x => by simpa only [hEq] using hL x)
  have hH : HolderWith K α (coreLap u2 : E n → ℝ) := hEq.symm ▸ hK
  have hS := laplacian_schauder_estimate hα hα1 u0 u1 u2
    (fun x => (hu.differentiable (by simp) x).hasFDerivAt)
    (fun x => (hu1.differentiable (by simp) x).hasFDerivAt) h2 hH
  have hC : laplacianSchauderConst α K L u0 ≤ C :=
    add_le_add (dirichlet_heatSupSchauderConst_le_const h0) le_rfl
  have hGauge : eContDiffHolderGaugeOn 2 α univ u ≤ C :=
    hS.trans (by exact_mod_cast hC)
  refine ⟨fun x => dirichlet_hessian_norm_le_of_schauder_gauge hGauge (mem_univ x), ?_⟩
  exact holderOnWith_univ.mp (dirichlet_hessian_holderOnWith_of_schauder_gauge hGauge)

end KEBall
