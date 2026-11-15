import KEBall.MoserTrudingerGibbsProjectedHolder
import KEBall.DirichletLaplacianTrace

/-! Transfer the actual projected-Hessian estimate to the actual Euclidean
Poisson source, retaining the factor four in the complex trace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff Laplacian

noncomputable section
namespace KEBall

def dirichletPoissonTraceLinearMap {n : ℕ} :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun B := ∑ i : Fin n, (B (realDirection i) (realDirection i) +
    B (imagDirection i) (imagDirection i))
  map_add' B D := by
    simp only [_root_.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c B := by
    simp only [_root_.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_add, Finset.mul_sum]

def dirichletPoissonTraceCLM {n : ℕ} :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  dirichletPoissonTraceLinearMap.toContinuousLinearMap

theorem dirichletPoissonTraceCLM_projected {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) :
    dirichletPoissonTraceCLM (complexProjectedHessian u x) = Δ u x := by
  have hTrace (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
      dirichletPoissonTraceCLM B = 4 * (complexHessianOfRealBilinear B).trace.re := by
    change (∑ i : Fin n, (B (realDirection i) (realDirection i) +
      B (imagDirection i) (imagDirection i))) = _
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [complexHessianOfRealBilinear, Complex.mul_re, Complex.inv_re]
    <;> ring
  rw [hTrace, complexHessianOfRealBilinear_projected hu,
    euclideanLaplacian_eq_four_complexHessian_trace_re hu]

theorem abs_laplacian_sub_le_projected_hessian_norm {n : ℕ}
    {u : E n → ℝ} {x y : E n} (hx : ContDiffAt ℝ ∞ u x) (hy : ContDiffAt ℝ ∞ u y) :
    |Δ u x - Δ u y| ≤ ‖(@dirichletPoissonTraceCLM n)‖ *
      ‖complexProjectedHessian u x - complexProjectedHessian u y‖ := by
  have h := (@dirichletPoissonTraceCLM n).le_opNorm
    (complexProjectedHessian u x - complexProjectedHessian u y)
  rwa [map_sub, dirichletPoissonTraceCLM_projected hx,
    dirichletPoissonTraceCLM_projected hy, Real.norm_eq_abs] at h

namespace MoserTrudinger

theorem exists_uniform_laplacian_holder_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ α K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ K ∧
      ∀ j (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          |Δ (u (j + 2)) x - Δ (u (j + 2)) y| ≤
            (K * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  obtain ⟨α, K, hα0, hα1, hK, hHolder⟩ :=
    exists_uniform_projected_holder_of_bounded_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  refine ⟨α, ‖(@dirichletPoissonTraceCLM n)‖ * K, hα0, hα1, by positivity, ?_⟩
  intro j x₀ R hR hR1 hBall x hx y hy
  calc
    _ ≤ ‖(@dirichletPoissonTraceCLM n)‖ *
        ‖complexProjectedHessian (u (j + 2)) x - complexProjectedHessian (u (j + 2)) y‖ :=
      abs_laplacian_sub_le_projected_hessian_norm (hu (j + 2)).contDiffAt (hu (j + 2)).contDiffAt
    _ ≤ ‖(@dirichletPoissonTraceCLM n)‖ *
        ((K * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α) :=
      mul_le_mul_of_nonneg_left (hHolder j x₀ R hR hR1 hBall x hx y hy) (norm_nonneg _)
    _ = _ := by ring

end MoserTrudinger
end KEBall
