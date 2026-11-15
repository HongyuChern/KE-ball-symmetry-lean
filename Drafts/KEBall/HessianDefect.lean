import Drafts.KEBall.Hessian20Bridge
import Drafts.KEBall.BochnerTransport

/-!
# The real covariant-Hessian defect and its actual Bochner consumer

Stage02 source draft, not kernel checked. The norm defined here is an explicit
sum in the retained real metric's orthonormal basis, not a renamed complex
norm. The equality with twice the paper's inverse-metric contraction is NOT
asserted in this file. Ricci is likewise retained as the actual real tensor.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- A reusable finite-matrix identity, with no symmetry hypothesis. -/
theorem sum_sq_sub_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) :
    (∑ i, ∑ j, (A i j - if i = j then 1 else 0) ^ 2) =
      (∑ i, ∑ j, (A i j) ^ 2) - 2 * (∑ i, A i i) + Fintype.card ι := by
  classical
  have hrow (i : ι) :
      (∑ j, (A i j - if i = j then 1 else 0) ^ 2) =
        (∑ j, (A i j) ^ 2) - 2 * A i i + 1 := by
    calc
      _ = ∑ j, ((A i j) ^ 2 - 2 * A i j * (if i = j then 1 else 0) +
          (if i = j then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [hij] <;> ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          mul_ite, Finset.mul_sum]
  simp_rw [hrow]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

noncomputable def hessianDefect {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (u : E n → ℝ) (x v w : E n) : ℝ :=
  D.hessian u x v w - g.inner x v w

/-- This is the REAL Hilbert-Schmidt norm squared. Its equivalence with the
complex inverse-matrix tensor norm is a separate, still open Lean obligation. -/
noncomputable def hessianDefectNormSq {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, ∑ j, (hessianDefect D u x
    (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2

theorem hessianDefectNormSq_nonneg {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (u : E n → ℝ) (x : E n) :
    0 ≤ hessianDefectNormSq D u x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact sq_nonneg _

/-- Anti-J-invariance follows from the actual potential-Hessian identity. -/
theorem hessianDefect_J_J {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    hessianDefect D u x (J v) (J w) = -hessianDefect D u x v w := by
  have h := potential_hessian_J_pair D hU hu hg hx v w
  have hgJ : g.inner x (J v) (J w) = g.inner x v w := by
    rw [hg x hx, hg x hx,
      realMetricForm_J_J (hu.contDiffAt (hU.mem_nhds hx))]
  simp only [hessianDefect, hgJ]
  linarith

/-- The trace is kept explicit, so this is also valid for arbitrary scalar
functions. No assumption of the form 'the desired norm identity holds' enters. -/
theorem hessianDefectNormSq_eq_real_norm_sub_trace {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (u : E n → ℝ) (x : E n) :
    hessianDefectNormSq D u x =
      (∑ i, ∑ j, (D.hessian u x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) -
      2 * D.laplacian u x + 2 * (n : ℝ) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (2 * n)) : E n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb (i j) :
      g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x j) =
        if i = j then 1 else 0 := by
    exact (g.orthonormalBasis x).inner_eq_ite i j
  have hd : Module.finrank ℝ (TangentSpace (𝓡 (2 * n)) x) = 2 * n := by
    change Module.finrank ℝ (E n) = 2 * n
    simp [E]
  unfold hessianDefectNormSq hessianDefect
  simp_rw [hb]
  rw [sum_sq_sub_identity]
  simp only [PoincareMT.LeviCivitaData.laplacian, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_ofNat, hd]

/-- One actual metric and connection carry Stage01 Bochner, the exact (2,0)
Hessian identification, and the real norm split. This stops before the Ricci
identification and before the complex norm contraction; it is not the final
complex Bochner formula or Proposition 3.1. -/
theorem IsSolution.exists_local_bochner_hessian20 {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ Y : E n → E n, DifferentiableAt ℝ Y x →
        ∀ v : E n, D.connection (fun y => J (Y y)) x v =
          J (D.connection Y x v)) ∧
      (∀ x ∈ V, ∀ i j : Fin n,
        covariantHessian20 u x i j = complexify20 (D.hessian u x) i j) ∧
      (∀ x ∈ V, ∀ v w : E n,
        hessianDefect D u x (J v) (J w) = -hessianDefect D u x v w) ∧
      (∀ x ∈ V,
        2 * complexLaplacian u (gradientNormSq u) x =
          2 * (n : ℝ) + hessianDefectNormSq D u x +
            D.ricci x (D.gradient u x) (D.gradient u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, _, _, hLap, _, hB⟩ :=
    hu.exists_local_bochner_transport hp
  have huV := hu.contDiffOn_ball.mono hVB
  refine ⟨g, D, V, hV, hpV, hVB, hg, ?_, ?_, ?_, ?_⟩
  · intro x hx Y hY v
    exact connection_J_field D hV huV hg hx hY v
  · intro x hx i j
    exact covariantHessian20_eq_hessian_complexification D hV huV hg hx
      (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx))) i j
  · intro x hx v w
    exact hessianDefect_J_J D hV huV hg hx v w
  · intro x hx
    have hnorm := hessianDefectNormSq_eq_real_norm_sub_trace D u x
    rw [hLap x hx] at hnorm
    have hbochner := hB x hx
    linarith

end KEBall
