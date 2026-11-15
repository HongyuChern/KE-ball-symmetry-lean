import KEBall.DirichletHigherAngularHessianL2
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! Algebraic coefficient extraction from values in a real linear subspace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Polynomial
namespace KEBall

 theorem dirichlet_coefficient_mem_of_polynomial_values_mem
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : Submodule ℝ V) (s : Finset ℕ) (a : ℕ → V)
    (h : ∀ t : ℝ, (∑ i ∈ s, t ^ i • a i) ∈ P)
    (j : ℕ) (hj : j ∈ s) : a j ∈ P := by
  classical
  by_contra hn
  obtain ⟨φ, hφ, hP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  let q : Polynomial ℝ := ∑ i ∈ s, Polynomial.monomial i (φ (a i))
  have hzero (t : ℝ) : φ (∑ i ∈ s, t ^ i • a i) = 0 := by
    apply (Submodule.mem_bot ℝ).mp
    rw [← hP]
    exact Submodule.mem_map.mpr ⟨_, h t, rfl⟩
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    simpa [q, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum,
      map_smul, mul_comm] using hzero t
  apply hφ
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff j) hq
  simpa [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hj] using hc

noncomputable def dirichletScalarPolynomialEval {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) : Polynomial A →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℝ A t)
    (fun a => (Algebra.commutes t a).symm)

theorem dirichletScalarPolynomialEval_eq_sum {A : Type*} [Ring A] [Algebra ℝ A]
    (p : Polynomial A) (t : ℝ) :
    dirichletScalarPolynomialEval t p = ∑ i ∈ p.support, t ^ i • p.coeff i := by
  rw [dirichletScalarPolynomialEval, Polynomial.eval₂RingHom'_apply,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (t ^ i) (p.coeff i)).symm

theorem dirichlet_polynomial_coeff_mem_of_scalar_eval_mem
    {A : Type*} [Ring A] [Algebra ℝ A]
    (P : Submodule ℝ A) (p : Polynomial A)
    (h : ∀ t : ℝ, dirichletScalarPolynomialEval t p ∈ P) (j : ℕ) : p.coeff j ∈ P := by
  by_cases hj : j ∈ p.support
  · exact dirichlet_coefficient_mem_of_polynomial_values_mem P p.support p.coeff
      (fun t => by simpa only [dirichletScalarPolynomialEval_eq_sum] using h t) j hj
  · rw [Polynomial.notMem_support_iff.mp hj]
    exact P.zero_mem

end KEBall
