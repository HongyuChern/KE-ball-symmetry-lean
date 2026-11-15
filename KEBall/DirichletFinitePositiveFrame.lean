import KEBall.DirichletFiniteDirections

/-!
# Compact families of real uniformly elliptic operators

This module constructs the finite directional families needed for Hessian
oscillation estimates.  Operator symmetry, the coercivity constant, and the
operator-norm bound are all explicit.
-/

set_option autoImplicit false

open InnerProductSpace Metric Set
open scoped BigOperators

noncomputable section

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def dirichletEllipticOperatorSet (a b : ℝ) : Set (V →L[ℝ] V) :=
  {T | T.toLinearMap.IsSymmetric ∧
    (∀ v : V, a * ‖v‖ ^ 2 ≤ inner ℝ (T v) v) ∧ ‖T‖ ≤ b}

theorem isClosed_dirichletEllipticOperatorSet (a b : ℝ) :
    IsClosed (dirichletEllipticOperatorSet (V := V) a b) := by
  have hS : IsClosed {T : V →L[ℝ] V | T.toLinearMap.IsSymmetric} := by
    change IsClosed {T : V →L[ℝ] V | ∀ x y : V, inner ℝ (T x) y = inner ℝ x (T y)}
    simp only [setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hL : IsClosed {T : V →L[ℝ] V | ∀ v : V, a * ‖v‖ ^ 2 ≤ inner ℝ (T v) v} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (by fun_prop)
  have hU : IsClosed {T : V →L[ℝ] V | ‖T‖ ≤ b} := isClosed_le continuous_norm continuous_const
  exact hS.inter (hL.inter hU)

theorem isCompact_dirichletEllipticOperatorSet [FiniteDimensional ℝ V] (a b : ℝ) :
    IsCompact (dirichletEllipticOperatorSet (V := V) a b) := by
  apply (isCompact_closedBall (0 : V →L[ℝ] V) b).of_isClosed_subset
    (isClosed_dirichletEllipticOperatorSet a b)
  intro T hT
  exact mem_closedBall_zero_iff.mpr hT.2.2

/-- The centers of the finite cover remain in the same elliptic family. -/
theorem exists_finite_dirichletElliptic_cover [FiniteDimensional ℝ V]
    (a b : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : Finset (dirichletEllipticOperatorSet (V := V) a b),
      ∀ T ∈ dirichletEllipticOperatorSet (V := V) a b,
        ∃ C ∈ s, ‖T - (C : V →L[ℝ] V)‖ < ρ := by
  classical
  let K := dirichletEllipticOperatorSet (V := V) a b
  obtain ⟨s, hs⟩ := (isCompact_dirichletEllipticOperatorSet (V := V) a b).elim_finite_subcover
    (fun C : K => ball (C : V →L[ℝ] V) ρ) (fun _ => isOpen_ball) (by
      intro T hT
      exact mem_iUnion.mpr ⟨⟨T, hT⟩, mem_ball_self hρ⟩)
  refine ⟨s, fun T hT => ?_⟩
  obtain ⟨C, hCs, hTC⟩ := mem_iUnion₂.mp (hs hT)
  exact ⟨C, hCs, mem_ball_iff_norm.mp hTC⟩

/-- Reindex the local spectral and pair directions by one finite type.
The same directions work throughout the operator-norm neighborhood. -/
theorem exists_dirichlet_local_bounded_frame [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (C : V →L[ℝ] V) (hCS : C.toLinearMap.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hC : (C - (4 * (Fintype.card ι : ℝ) * δ) • ContinuousLinearMap.id ℝ V).IsPositive) :
    ∃ (m : ℕ) (v : Fin m → V), ∀ (T : V →L[ℝ] V), T.toLinearMap.IsSymmetric →
      ‖T - C‖ ≤ 2 * δ → ∃ a : Fin m → ℝ,
        (∀ k, 0 ≤ a k ∧ a k ≤ max 1 (3 * δ / 2)) ∧
        T = ∑ k : Fin m, a k • rankOne ℝ (v k) (v k) := by
  classical
  obtain ⟨m, u, hu⟩ := exists_dirichlet_local_positive_frame b C hCS hδ hC
  let J := Fin m ⊕ ((ι × ι) × Bool)
  let v : J → V := Sum.elim u (fun p =>
    match p.2 with
    | true => b p.1.1 + b p.1.2
    | false => b p.1.1 - b p.1.2)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, fun k => v (e.symm k), fun T hT hNear => ?_⟩
  let a : J → ℝ := Sum.elim (fun _ => 1) (fun p =>
    match p.2 with
    | true => δ + inner ℝ (b p.1.1) ((T - C) (b p.1.2)) / 4
    | false => δ - inner ℝ (b p.1.1) ((T - C) (b p.1.2)) / 4)
  have ha : ∀ k : J, 0 ≤ a k ∧ a k ≤ max 1 (3 * δ / 2) := by
    rintro (k | ⟨⟨i, j⟩, s⟩)
    · exact ⟨zero_le_one, le_max_left _ _⟩
    · have h := dirichlet_pair_coefficients_bounds b (T - C) hNear i j
      cases s
      · exact ⟨(by positivity : 0 ≤ δ / 2).trans h.2.2.1, h.2.2.2.trans (le_max_right _ _)⟩
      · exact ⟨(by positivity : 0 ≤ δ / 2).trans h.1, h.2.1.trans (le_max_right _ _)⟩
  have hRep : T = ∑ k : J, a k • rankOne ℝ (v k) (v k) := by
    simpa only [J, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
      a, v, Sum.elim_inl, Sum.elim_inr, one_smul] using hu T hT hNear
  refine ⟨fun k => a (e.symm k), fun k => ha (e.symm k), ?_⟩
  exact hRep.trans (Fintype.sum_equiv e _ _ (fun k => by simp))

/-- A compact elliptic family has one finite nonnegative directional
representation with a common upper coefficient bound. -/
theorem exists_dirichlet_bounded_frame [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [Nonempty ι] (b : OrthonormalBasis ι ℝ V)
    {a B : ℝ} (ha : 0 < a) :
    ∃ (m : ℕ) (v : Fin m → V) (K : ℝ), 0 < K ∧
      ∀ T ∈ dirichletEllipticOperatorSet (V := V) a B,
        ∃ c : Fin m → ℝ, (∀ k, 0 ≤ c k ∧ c k ≤ K) ∧
          T = ∑ k : Fin m, c k • rankOne ℝ (v k) (v k) := by
  classical
  let δ : ℝ := a / (8 * (Fintype.card ι : ℝ))
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδ : 0 < δ := div_pos ha (by positivity)
  have hScale : 4 * (Fintype.card ι : ℝ) * δ = a / 2 := by
    dsimp [δ]
    field_simp
    <;> ring
  have hPos (C : dirichletEllipticOperatorSet (V := V) a B) :
      (C.1 - (4 * (Fintype.card ι : ℝ) * δ) • ContinuousLinearMap.id ℝ V).IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).mpr
    constructor
    · intro x y
      change inner ℝ (C.1 x - (4 * (Fintype.card ι : ℝ) * δ) • x) y =
        inner ℝ x (C.1 y - (4 * (Fintype.card ι : ℝ) * δ) • y)
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      exact congrArg (fun t : ℝ => t - (4 * (Fintype.card ι : ℝ) * δ) * inner ℝ x y)
        (C.2.1 x y)
    · intro x
      change 0 ≤ inner ℝ (C.1 x - (4 * (Fintype.card ι : ℝ) * δ) • x) x
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hScale]
      have h := C.2.2.1 x
      nlinarith only [h, mul_nonneg ha.le (sq_nonneg ‖x‖)]
  obtain ⟨s, hs⟩ := exists_finite_dirichletElliptic_cover (V := V) a B (by positivity : 0 < 2 * δ)
  let J := ↥s
  have hLocal (j : J) := exists_dirichlet_local_bounded_frame b j.1.1 j.1.2.1 hδ (hPos j.1)
  choose m v hRep using hLocal
  let D := (j : J) × Fin (m j)
  let e : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  let vD (p : D) : V := v p.1 p.2
  let K : ℝ := max 1 (3 * δ / 2)
  refine ⟨Fintype.card D, fun k => vD (e.symm k), K, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro T hT
  obtain ⟨C, hCs, hNear⟩ := hs T hT
  let j : J := ⟨C, hCs⟩
  obtain ⟨c, hc, hTc⟩ := hRep j T hT.1 hNear.le
  let cD : (j : J) → Fin (m j) → ℝ := Pi.single j c
  have hcD : ∀ p : D, 0 ≤ cD p.1 p.2 ∧ cD p.1 p.2 ≤ K := by
    rintro ⟨k, i⟩
    by_cases hkj : k = j
    · subst k
      simpa [cD, K] using hc i
    · simp only [cD, Pi.single_eq_of_ne hkj, Pi.zero_apply]
      exact ⟨le_rfl, zero_le_one.trans (le_max_left _ _)⟩
  have hTD : T = ∑ p : D, cD p.1 p.2 • rankOne ℝ (vD p) (vD p) := by
    rw [Fintype.sum_sigma]
    symm
    calc
      _ = ∑ i : Fin (m j), c i • rankOne ℝ (v j i) (v j i) := by
        rw [Finset.sum_eq_single j]
        · simp [cD, vD]
        · intro k _ hkj
          simp [cD, vD, Pi.single_eq_of_ne hkj]
        · simp
      _ = T := hTc.symm
  refine ⟨fun k => cD (e.symm k).1 (e.symm k).2, fun k => hcD (e.symm k), ?_⟩
  exact hTD.trans (Fintype.sum_equiv e _ _ (fun k =>
    (congrArg (fun p : D => cD p.1 p.2 • rankOne ℝ (vD p) (vD p))
      (e.symm_apply_apply k)).symm))

/-- A uniformly positive finite frame for the entire elliptic family.
Every fixed basis direction and every pairwise basis sum is included, so
the directional quadratics determine the whole symmetric Hessian.  The
directions and both positive coefficient bounds are chosen before the
varying operator. -/
theorem exists_dirichlet_uniform_positive_frame [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [Nonempty ι] (b : OrthonormalBasis ι ℝ V)
    {a B : ℝ} (ha : 0 < a) :
    ∃ (m : ℕ) (v : Fin m → V) (c C : ℝ), 0 < c ∧ 0 < C ∧
      (∀ i : ι, ∃ k : Fin m, v k = b i) ∧
      (∀ i j : ι, ∃ k : Fin m, v k = b i + b j) ∧
      ∀ T ∈ dirichletEllipticOperatorSet (V := V) a B,
        ∃ β : Fin m → ℝ, (∀ k, c ≤ β k ∧ β k ≤ C) ∧
          T = ∑ k : Fin m, β k • rankOne ℝ (v k) (v k) := by
  classical
  obtain ⟨m, v, K, hK, hRep⟩ := exists_dirichlet_bounded_frame b
    (B := B + a) (by positivity : 0 < a / 2)
  let J := Fin m ⊕ (ι ⊕ (ι × ι))
  let vJ : J → V := Sum.elim v (Sum.elim b (fun p => b p.1 + b p.2))
  let S : V →L[ℝ] V := ∑ j : J, rankOne ℝ (vJ j) (vJ j)
  have hS : S.IsPositive := ContinuousLinearMap.isPositive_sum Finset.univ
    (fun j _ => isPositive_rankOne_self (vJ j))
  let ε : ℝ := a / (4 * (‖S‖ + 1))
  have hε : 0 < ε := div_pos ha (by positivity)
  have hεN : ε * ‖S‖ ≤ a / 4 := by
    calc
      ε * ‖S‖ ≤ ε * (‖S‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = a / 4 := by
        dsimp [ε]
        field_simp
        <;> ring
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, fun k => vJ (e.symm k), ε, K + ε, hε, add_pos hK hε, ?_, ?_, ?_⟩
  · intro i
    exact ⟨e (Sum.inr (Sum.inl i)), by simp [vJ]⟩
  · intro i j
    exact ⟨e (Sum.inr (Sum.inr (i, j))), by simp [vJ]⟩
  · intro T hT
    have hShift : T - ε • S ∈ dirichletEllipticOperatorSet (V := V) (a / 2) (B + a) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y
        change inner ℝ (T x - ε • S x) y = inner ℝ x (T y - ε • S y)
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
        rw [show inner ℝ (T x) y = inner ℝ x (T y) from hT.1 x y,
          show inner ℝ (S x) y = inner ℝ x (S y) from hS.isSymmetric x y]
      · intro x
        change (a / 2) * ‖x‖ ^ 2 ≤ inner ℝ (T x - ε • S x) x
        rw [inner_sub_left, real_inner_smul_left]
        have hSN : inner ℝ (S x) x ≤ ‖S‖ * ‖x‖ ^ 2 := by
          calc
            _ ≤ ‖S x‖ * ‖x‖ := real_inner_le_norm _ _
            _ ≤ (‖S‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (S.le_opNorm x) (norm_nonneg _)
            _ = _ := by ring
        have hεSX : ε * inner ℝ (S x) x ≤ (a / 4) * ‖x‖ ^ 2 := by
          calc
            _ ≤ ε * (‖S‖ * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hSN hε.le
            _ = (ε * ‖S‖) * ‖x‖ ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hεN (sq_nonneg _)
        have hTx := hT.2.1 x
        nlinarith only [hTx, hεSX, mul_nonneg ha.le (sq_nonneg ‖x‖)]
      · calc
          ‖T - ε • S‖ ≤ ‖T‖ + ‖ε • S‖ := norm_sub_le _ _
          _ = ‖T‖ + ε * ‖S‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
          _ ≤ B + a / 4 := add_le_add hT.2.2 hεN
          _ ≤ B + a := by linarith only [ha]
    obtain ⟨c, hc, hTc⟩ := hRep (T - ε • S) hShift
    let cJ : J → ℝ := Sum.elim c (fun _ => 0)
    have hcJ : ∀ j : J, 0 ≤ cJ j ∧ cJ j ≤ K := by
      rintro (k | i)
      · exact hc k
      · exact ⟨le_rfl, hK.le⟩
    have hTJ : T - ε • S = ∑ j : J, cJ j • rankOne ℝ (vJ j) (vJ j) := by
      simpa only [J, cJ, vJ, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        zero_smul, Finset.sum_const_zero, add_zero] using hTc
    let β : J → ℝ := fun j => cJ j + ε
    have hβ : ∀ j : J, ε ≤ β j ∧ β j ≤ K + ε := by
      intro j
      obtain ⟨hj₀, hjK⟩ := hcJ j
      constructor <;> dsimp [β] <;> linarith
    have hRepJ : T = ∑ j : J, β j • rankOne ℝ (vJ j) (vJ j) := by
      simp only [β, add_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
      rw [← hTJ]
      change T = (T - ε • S) + ε • S
      abel
    refine ⟨fun k => β (e.symm k), fun k => hβ (e.symm k), ?_⟩
    exact hRepJ.trans (Fintype.sum_equiv e _ _ (fun k =>
      (congrArg (fun j : J => β j • rankOne ℝ (vJ j) (vJ j))
        (e.symm_apply_apply k)).symm))

end KEBall
