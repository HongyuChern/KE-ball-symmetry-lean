import KEBall.DirichletMultilinearFiniteLpJets
import KEBall.DirichletMatrixCoordinateJets
import KEBall.DirichletInteriorAngularWordEquation

/-! The original proper-partition cofactor source in the actual finite Lp jet algebra. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace KEBall

private theorem dirichletPartition_eq_oneBlock_of_full_size {m : ℕ}
    (c : OrderedFinpartition (m + 1)) (j : Fin c.length) (hj : c.partSize j = m + 1) :
    c = oneBlockPartition m := by
  have he : Function.Surjective (c.emb j) := by
    have h := (c.emb_strictMono j).injective
    exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨h, by simp [hj]⟩).2
  have hJ (i : Fin c.length) : i = j := by
    by_contra hne
    obtain ⟨z, hz⟩ := he (c.emb i ⟨0, c.partSize_pos i⟩)
    exact (c.emb_ne_emb_of_ne hne) hz.symm
  have hLen : c.length = 1 := by
    have hle : c.length ≤ 1 := by
      have := Fintype.card_le_of_injective (fun _ : Fin c.length => (0 : Fin 1))
        (fun a b _ => (hJ a).trans (hJ b).symm)
      simpa using this
    exact le_antisymm hle (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt j.isLt))
  clear he hJ
  rcases c with ⟨len, size, hSize, emb, hEmb, hParts, hDisj, hCover⟩
  change len = 1 at hLen
  subst len
  have hj₀ : j = 0 := Subsingleton.elim _ _
  subst j
  obtain rfl : size = fun _ => m + 1 := funext fun i => by
    rw [show i = 0 from Subsingleton.elim _ _]
    exact hj
  have hId (i : Fin 1) : emb i = id := by
    let e : Fin (m + 1) →o Fin (m + 1) := ⟨emb i, (hEmb i).monotone⟩
    exact congrArg DFunLike.coe (OrderHom.eq_id_of_injective e (hEmb i).injective)
  have hb : emb = fun _ => id := funext hId
  subst emb
  rfl

/-- Every block of a partition other than the single-block partition
has strictly smaller size than the order of differentiation. -/
private theorem dirichletPartition_size_le_of_proper {m : ℕ}
    (c : OrderedFinpartition (m + 1)) (hc : c ≠ oneBlockPartition m) (j : Fin c.length) :
    c.partSize j ≤ m := by
  have hle := c.partSize_le j
  have hne : c.partSize j ≠ m + 1 := fun h => hc (dirichletPartition_eq_oneBlock_of_full_size c j h)
  omega


theorem contDiff_dirichlet_det_real {n : ℕ} :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.det.re) := by
  rw [← contDiffOn_univ]
  apply Complex.reCLM.contDiff.comp_contDiffOn
  exact contDiffOn_det_of_contDiffOn_entries (A := id) fun i j =>
    (contDiff_pi.mp (contDiff_pi.mp (contDiff_id (𝕜 := ℝ)
      (E := Matrix (Fin n) (Fin n) ℂ)) i) j).contDiffOn

theorem hasDirichletFiniteLpJets_dirichletAngularDetLowerTerms {n m k : ℕ}
    (R : Fin (m+1) → DirichletUnitaryField n)
    (A : (E n → ℝ) → E n → Matrix (Fin n) (Fin n) ℂ)
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    {u : E n → ℝ} (hAS : ContDiffOn ℝ ∞ (A u) U) (hAC : ContinuousOn (A u) K)
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A u x i j))
    (hLow : ∀ j ≤ m, ∀ R' : Fin j → DirichletUnitaryField n, ∀ a b,
      HasDirichletComplexFiniteLpJets U μ k (fun x => A (dirichletAngularWord R' u) x a b)) :
    HasDirichletFiniteLpJets U μ k (dirichletAngularDetLowerTerms R A u) := by
  classical
  let b := Module.finBasis ℝ (Matrix (Fin n) (Fin n) ℂ)
  have hCompact : IsCompact ((A u) '' K) := hK.image_of_continuousOn hAC
  have hRange : MapsTo (A u) U ((A u) '' K) := fun x hx => ⟨x,hUK hx,rfl⟩
  unfold dirichletAngularDetLowerTerms
  apply HasDirichletFiniteLpJets.finsetSum hU hμ
  intro c hc
  have hProper := (Finset.mem_erase.mp hc).1
  refine hasDirichletFiniteLpJets_iteratedFDeriv_comp_apply b hU hμ hAS
    (hasDirichletFiniteLpJets_matrix_real_coord b hU hμ hA) hCompact hRange
    contDiff_dirichlet_det_real ?_
  intro i j
  exact hasDirichletFiniteLpJets_matrix_real_coord b hU hμ
    (hLow (c.partSize i) (dirichletPartition_size_le_of_proper c hProper i)
      (R ∘ c.emb i)) j

end KEBall
