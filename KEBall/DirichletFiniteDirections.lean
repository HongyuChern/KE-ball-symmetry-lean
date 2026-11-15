import KEBall.Domain
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Convex.Topology

/-!
# Finite positive directional frames for real elliptic operators

The algebra below keeps actual real rank-one operators.  In particular it
does not replace the Hessian by an unrelated family of scalar functions.
-/

set_option autoImplicit false

open InnerProductSpace
open scoped BigOperators

noncomputable section

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The two signs of a pair of directions separate the diagonal and mixed
parts, with all factors displayed. -/
theorem dirichlet_rankOne_pair (x y : V) (a b : ℝ) :
    (a + b) • rankOne ℝ (x + y) (x + y) +
      (a - b) • rankOne ℝ (x - y) (x - y) =
      (2 * a) • rankOne ℝ x x + (2 * a) • rankOne ℝ y y +
        (2 * b) • rankOne ℝ x y + (2 * b) • rankOne ℝ y x := by
  ext z
  change (a + b) • (inner ℝ (x + y) z • (x + y)) +
    (a - b) • (inner ℝ (x - y) z • (x - y)) =
    (2 * a) • (inner ℝ x z • x) + (2 * a) • (inner ℝ y z • y) +
      (2 * b) • (inner ℝ y z • x) + (2 * b) • (inner ℝ x z • y)
  simp only [ContinuousLinearMap.add_apply, smul_apply, rankOne_apply,
    inner_add_left, inner_sub_left, add_smul, sub_smul, smul_add, smul_sub, smul_smul]
  module

theorem dirichlet_rankOne_basis_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i : ι, rankOne ℝ (b i) (b i)) = ContinuousLinearMap.id ℝ V := by
  ext z
  simp only [_root_.sum_apply, rankOne_apply, ContinuousLinearMap.id_apply]
  exact b.sum_repr' z

/-- The operator expansion in the fixed orthonormal basis; symmetry is
not required for this identity. -/
theorem dirichlet_operator_basis_expansion {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (T : V →L[ℝ] V) :
    T = ∑ i : ι, ∑ j : ι, (inner ℝ (b i) (T (b j))) • rankOne ℝ (b i) (b j) := by
  ext z
  simp only [_root_.sum_apply, smul_apply, rankOne_apply, smul_smul]
  calc
    T z = ∑ j : ι, inner ℝ (b j) z • T (b j) := by
      simpa only [map_sum, map_smul] using congrArg T (b.sum_repr' z).symm
    _ = ∑ j : ι, ∑ i : ι, (inner ℝ (b j) z * inner ℝ (b i) (T (b j))) • b i := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Finset.smul_sum, smul_smul] using
        congrArg (fun w : V => inner ℝ (b j) z • w) (b.sum_repr' (T (b j))).symm
    _ = ∑ i : ι, ∑ j : ι, (inner ℝ (b i) (T (b j)) * inner ℝ (b j) z) • b i := by
      rw [Finset.sum_comm]
      simp only [mul_comm]

/-- A fixed family of sums and differences represents a symmetric
perturbation of a scalar positive operator.  The coefficients will be
strictly positive whenever the perturbation is sufficiently small. -/
theorem dirichlet_rankOne_fixed_pair_frame {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (δ : ℝ) :
    (∑ i : ι, ∑ j : ι,
      ((δ + inner ℝ (b i) (T (b j)) / 4) • rankOne ℝ (b i + b j) (b i + b j) +
      (δ - inner ℝ (b i) (T (b j)) / 4) • rankOne ℝ (b i - b j) (b i - b j))) =
        T + (4 * (Fintype.card ι : ℝ) * δ) • ContinuousLinearMap.id ℝ V := by
  have hDiag : (∑ i : ι, ∑ j : ι, (2 * δ) • rankOne ℝ (b i) (b i)) =
      ((Fintype.card ι : ℝ) * (2 * δ)) • ContinuousLinearMap.id ℝ V := by
    calc
      _ = ∑ i : ι, (∑ _j : ι, (2 * δ)) • rankOne ℝ (b i) (b i) := by
        simp only [Finset.sum_smul]
      _ = ∑ i : ι, ((Fintype.card ι : ℝ) * (2 * δ)) • rankOne ℝ (b i) (b i) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = _ := by rw [← Finset.smul_sum, dirichlet_rankOne_basis_sum]
  have hDiag' : (∑ i : ι, ∑ j : ι, (2 * δ) • rankOne ℝ (b j) (b j)) =
      ((Fintype.card ι : ℝ) * (2 * δ)) • ContinuousLinearMap.id ℝ V := by
    rw [Finset.sum_comm]
    exact hDiag
  have hCross : (∑ i : ι, ∑ j : ι,
      (2 * (inner ℝ (b i) (T (b j)) / 4)) • rankOne ℝ (b i) (b j)) = (1 / 2 : ℝ) • T := by
    have h := congrArg (fun S : V →L[ℝ] V => (1 / 2 : ℝ) • S)
      (dirichlet_operator_basis_expansion b T).symm
    simpa only [Finset.smul_sum, smul_smul, show ∀ t : ℝ, 2 * (t / 4) = 1 / 2 * t by
      intro t; ring] using h
  have hSym (i j : ι) : inner ℝ (b i) (T (b j)) = inner ℝ (b j) (T (b i)) := by
    exact (hT (b i) (b j)).symm.trans (real_inner_comm _ _)
  have hCross' : (∑ i : ι, ∑ j : ι,
      (2 * (inner ℝ (b i) (T (b j)) / 4)) • rankOne ℝ (b j) (b i)) = (1 / 2 : ℝ) • T := by
    rw [Finset.sum_comm]
    simpa only [hSym] using hCross
  simp_rw [dirichlet_rankOne_pair, Finset.sum_add_distrib]
  rw [hDiag, hDiag', hCross, hCross']
  module

theorem abs_dirichlet_basis_coefficient_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (T : V →L[ℝ] V) (i j : ι) :
    |inner ℝ (b i) (T (b j))| ≤ ‖T‖ := by
  calc
    _ ≤ ‖b i‖ * ‖T (b j)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖b i‖ * (‖T‖ * ‖b j‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by simp only [b.norm_eq_one, mul_one, one_mul]

/-- The coefficients of the fixed pair frame have a uniform positive
lower bound on an operator-norm neighborhood. -/
theorem dirichlet_pair_coefficients_bounds {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (T : V →L[ℝ] V) {δ : ℝ}
    (hT : ‖T‖ ≤ 2 * δ) (i j : ι) :
    δ / 2 ≤ δ + inner ℝ (b i) (T (b j)) / 4 ∧
    δ + inner ℝ (b i) (T (b j)) / 4 ≤ 3 * δ / 2 ∧
    δ / 2 ≤ δ - inner ℝ (b i) (T (b j)) / 4 ∧
    δ - inner ℝ (b i) (T (b j)) / 4 ≤ 3 * δ / 2 := by
  have h := abs_le.mp ((abs_dirichlet_basis_coefficient_le b T i j).trans hT)
  constructor
  · linarith only [h.1]
  constructor
  · linarith only [h.2]
  constructor
  · linarith only [h.2]
  · linarith only [h.1]

/-- One finite collection of directions works for every symmetric
operator in a neighborhood of the same positive center.  The spectral
directions are chosen once from the center, not from the varying operator. -/
theorem exists_dirichlet_local_positive_frame [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (C : V →L[ℝ] V) (hCS : C.toLinearMap.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hC : (C - (4 * (Fintype.card ι : ℝ) * δ) • ContinuousLinearMap.id ℝ V).IsPositive) :
    ∃ (m : ℕ) (u : Fin m → V), ∀ (T : V →L[ℝ] V), T.toLinearMap.IsSymmetric →
      ‖T - C‖ ≤ 2 * δ →
      T = (∑ k : Fin m, rankOne ℝ (u k) (u k)) +
        ∑ i : ι, ∑ j : ι,
          ((δ + inner ℝ (b i) ((T - C) (b j)) / 4) • rankOne ℝ (b i + b j) (b i + b j) +
          (δ - inner ℝ (b i) ((T - C) (b j)) / 4) • rankOne ℝ (b i - b j) (b i - b j)) := by
  obtain ⟨m, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hC
  refine ⟨m, u, fun T hT _ => ?_⟩
  have hDiff : (T - C).toLinearMap.IsSymmetric := hT.sub hCS
  rw [← hu, dirichlet_rankOne_fixed_pair_frame b (T - C) hDiff]
  abel

end KEBall
