import KEBall.DiscPolynomialCalculus
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Polynomial solutions of the disc Poisson problem

Multiplication by the quadratic defining function followed by the
Laplacian is an endomorphism of each finite-degree polynomial space.
The maximum principle gives injectivity and hence surjectivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric MvPolynomial Set
open scoped BigOperators ContDiff Laplacian

namespace KEBall.DiscPolynomial

local notation "Poly" => MvPolynomial (Fin 2) ℝ

private noncomputable def boundaryPolynomial : Poly := X 0 ^ 2 + X 1 ^ 2 - 1

private theorem boundaryPolynomial_evaluate (x : E 1) :
    evaluate boundaryPolynomial x = ‖x‖ ^ 2 - 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [evaluate, boundaryPolynomial, Real.norm_eq_abs, sq_abs]

private theorem boundaryPolynomial_degree : boundaryPolynomial.totalDegree ≤ 2 := by
  unfold boundaryPolynomial
  refine (totalDegree_sub _ _).trans ?_
  apply max_le
  · exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_X_pow (R := ℝ) (0 : Fin 2) 2).le)
      ((totalDegree_X_pow (R := ℝ) (1 : Fin 2) 2).le))
  · simp

private noncomputable def polynomialDirichlet (m : ℕ) :
    restrictTotalDegree (Fin 2) ℝ m →ₗ[ℝ] restrictTotalDegree (Fin 2) ℝ m :=
  (polynomialLaplacian.comp (LinearMap.mulLeft ℝ boundaryPolynomial)).restrict (by
    intro p hp
    have h : (boundaryPolynomial * p).totalDegree ≤ 2 + m :=
      (totalDegree_mul _ _).trans (add_le_add boundaryPolynomial_degree
        ((mem_restrictTotalDegree _ _ _).mp hp))
    apply (mem_restrictTotalDegree _ _ _).mpr
    change (polynomialLaplacian (boundaryPolynomial * p)).totalDegree ≤ m
    exact (totalDegree_laplacian_le _).trans (by omega))

private theorem polynomialDirichlet_injective (m : ℕ) : Function.Injective (polynomialDirichlet m) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  apply Subtype.ext
  change (p : Poly) = 0
  let u := evaluate (boundaryPolynomial * (p : Poly))
  have hu : ContDiff ℝ ∞ u := contDiff_evaluate _
  have hΔ (x : E 1) : Δ u x = 0 := by
    have hz : polynomialLaplacian (boundaryPolynomial * (p : Poly)) = 0 :=
      congrArg Subtype.val hp
    change Δ (evaluate (boundaryPolynomial * (p : Poly))) x = 0
    rw [← evaluate_polynomialLaplacian, hz]
    simp [evaluate]
  have hB (x : E 1) (hx : x ∈ unitSphere 1) : u x = 0 := by
    have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change evaluate (boundaryPolynomial * (p : Poly)) x = 0
    rw [show evaluate (boundaryPolynomial * (p : Poly)) x =
      evaluate boundaryPolynomial x * evaluate p x from eval_mul,
      boundaryPolynomial_evaluate, hnorm]
    ring
  have h₀ (x : E 1) (hx : x ∈ closedUnitBall 1) : u x = 0 := by
    have hle := disc_nonpositive_of_laplacian_nonneg hu
      (fun x _ => (hΔ x).ge) (fun x hx => (hB x hx).le) x hx
    have hge := disc_nonpositive_of_laplacian_nonneg (u := -u) hu.neg
      (fun x _ => by rw [InnerProductSpace.laplacian_neg, Pi.neg_apply, hΔ, neg_zero])
      (fun x hx => by simp [hB x hx]) x hx
    exact le_antisymm hle (by simpa using hge)
  apply MvPolynomial.funext_set (fun _ => Icc (-(1 : ℝ) / 3) (1 / 3))
    (fun _ => Icc_infinite (by norm_num))
  intro y hy
  let x : E 1 := WithLp.toLp 2 y
  have hcoord (i : Fin 2) : |y i| ≤ 1 / 3 := by
    have h : y i ∈ Icc (-(1 : ℝ) / 3) (1 / 3) := hy i (mem_univ i)
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hnorm : ‖x‖ ^ 2 < 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    change |y 0| ^ 2 + |y 1| ^ 2 < 1
    have h₁ := pow_le_pow_left₀ (abs_nonneg _) (hcoord 0) 2
    have h₂ := pow_le_pow_left₀ (abs_nonneg _) (hcoord 1) 2
    linarith
  have hx : x ∈ closedUnitBall 1 := by
    apply mem_closedBall_zero_iff.mpr
    nlinarith [norm_nonneg x]
  have h := h₀ x hx
  change evaluate (boundaryPolynomial * (p : Poly)) x = 0 at h
  rw [show evaluate (boundaryPolynomial * (p : Poly)) x =
    evaluate boundaryPolynomial x * evaluate p x from eval_mul,
    boundaryPolynomial_evaluate] at h
  have he : evaluate p x = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hnorm.ne)
  change MvPolynomial.eval y (p : Poly) = MvPolynomial.eval y 0
  rw [map_zero]
  exact he

/-- Every polynomial density has an exact polynomial zero-boundary Poisson solution. -/
theorem exists_polynomial_zeroDirichlet (f : Poly) :
    ∃ p : Poly, (∀ x ∈ unitSphere 1, evaluate p x = 0) ∧
      (∀ x : E 1, Δ (evaluate p) x = evaluate f x) := by
  let m := f.totalDegree
  let q : restrictTotalDegree (Fin 2) ℝ m := ⟨f, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective.mp (polynomialDirichlet_injective m)) q
  refine ⟨boundaryPolynomial * (p : Poly), ?_, ?_⟩
  · intro x hx
    have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    rw [show evaluate (boundaryPolynomial * (p : Poly)) x =
      evaluate boundaryPolynomial x * evaluate p x from eval_mul,
      boundaryPolynomial_evaluate, hnorm]
    ring
  · intro x
    rw [← evaluate_polynomialLaplacian]
    exact congrArg (fun r : restrictTotalDegree (Fin 2) ℝ m => evaluate r x) hp

private noncomputable def evalOnClosure :
    Poly →ₐ[ℝ] C(↥(closedUnitBall 1), ℝ) :=
  MvPolynomial.aeval fun i =>
    ⟨fun x => x.1 i, (EuclideanSpace.proj i : E 1 →L[ℝ] ℝ).continuous.comp continuous_subtype_val⟩

private theorem evalOnClosure_apply (p : Poly) (x : ↥(closedUnitBall 1)) :
    evalOnClosure p x = evaluate p x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [evalOnClosure, aeval_C]
    simp [evaluate]
  | add p q hp hq =>
    rw [map_add]
    simp [hp, hq, evaluate, map_add]
  | mul_X p i hp =>
    rw [map_mul]
    have hX : evalOnClosure (X i) x = x.1 i := by simp [evalOnClosure]
    simp [hp, hX, evaluate, map_mul]

/-- Polynomial densities approximate every continuous density uniformly on the closed disc. -/
theorem exists_polynomial_uniformApprox {f : E 1 → ℝ}
    (hf : ContinuousOn f (closedUnitBall 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Poly, ∀ x ∈ closedUnitBall 1, |evaluate p x - f x| < ε := by
  let K := ↥(closedUnitBall 1)
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F : C(K, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩
  have hsep : evalOnClosure.range.SeparatesPoints := by
    intro x y hxy
    have h : ∃ i : Fin 2, x.1 i ≠ y.1 i := by
      by_contra! he
      apply hxy
      apply Subtype.ext
      ext i
      exact he i
    obtain ⟨i, hi⟩ := h
    refine ⟨_, ⟨evalOnClosure (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
    simpa [evalOnClosure] using hi
  have hTop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ hsep
  have hF : F ∈ closure (evalOnClosure.range : Set C(K, ℝ)) := by
    change F ∈ evalOnClosure.range.topologicalClosure
    rw [hTop]
    trivial
  obtain ⟨g, hg, hgε⟩ := Metric.mem_closure_iff.mp hF ε hε
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, fun x hx => ?_⟩
  have h := (ContinuousMap.norm_coe_le_norm (evalOnClosure p - F) ⟨x, hx⟩).trans_lt
    (by simpa [dist_comm, dist_eq_norm] using hgε)
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, evalOnClosure_apply] at h
  change |evaluate p x - f x| < ε at h
  exact h

end KEBall.DiscPolynomial
