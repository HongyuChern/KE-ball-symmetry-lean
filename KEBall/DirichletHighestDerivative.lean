import KEBall.DirichletMixedAngularEquation
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-! The linear highest-order term in the derivative of a composition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ContDiff Topology

namespace KEBall

/-- The ordered partition with a single block containing every direction. -/
def oneBlockPartition (m : ℕ) : OrderedFinpartition (m + 1) where
  length := 1
  partSize _ := m + 1
  partSize_pos _ := Nat.succ_pos _
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint _ _ _ _ h := (h (Subsingleton.elim _ _)).elim
  cover x := ⟨0, x, rfl⟩

private theorem OrderedFinpartition.eq_oneBlockPartition_of_partSize {m : ℕ}
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
private theorem OrderedFinpartition.partSize_le_of_ne_oneBlock {m : ℕ}
    (c : OrderedFinpartition (m + 1)) (hc : c ≠ oneBlockPartition m) (j : Fin c.length) :
    c.partSize j ≤ m := by
  have hle := c.partSize_le j
  have hne : c.partSize j ≠ m + 1 := fun h => hc (OrderedFinpartition.eq_oneBlockPartition_of_partSize c j h)
  omega

/-- The top derivative in the chain rule appears once and is multiplied by
the first derivative of the outer function. -/
theorem iteratedFDeriv_comp_succ_eq_linear_add_lower {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : Y → Z} {f : X → Y} (hg : ContDiff ℝ ∞ g)
    {x : X} (hf : ContDiffAt ℝ ∞ f x) (m : ℕ) (v : Fin (m + 1) → X) :
    iteratedFDeriv ℝ (m + 1) (g ∘ f) x v =
      fderiv ℝ g (f x) (iteratedFDeriv ℝ (m + 1) f x v) +
        ∑ c ∈ (Finset.univ.erase (oneBlockPartition m)),
          iteratedFDeriv ℝ c.length g (f x)
            (fun j => iteratedFDeriv ℝ (c.partSize j) f x (v ∘ c.emb j)) := by
  classical
  have hOrd : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl (m + 1)
  obtain ⟨U, hU, hUF⟩ := (hf.of_le hOrd).contDiffOn (m := (m + 1 : ℕ))
    le_rfl (by simp)
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  have hUF := hUF.mono hVU
  have hFu := hUF.ftaylorSeriesWithin hV.uniqueDiffOn
  have hGu := (hg.of_le hOrd).contDiffOn.ftaylorSeriesWithin
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set Y))
  have h := (hGu.comp hFu (mapsTo_univ _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := m + 1) le_rfl hV.uniqueDiffOn hxV
  have hEq := congrFun (congrArg DFunLike.coe h) v
  simp only [ftaylorSeriesWithin, iteratedFDerivWithin_univ,
    iteratedFDerivWithin_of_isOpen _ hV hxV, FormalMultilinearSeries.taylorComp,
    sum_apply, FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply] at hEq
  rw [← hEq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (oneBlockPartition m))]
  congr 1
  change iteratedFDeriv ℝ 1 g (f x)
    (fun _ => iteratedFDeriv ℝ (m + 1) f x (v ∘ id)) =
      fderiv ℝ g (f x) (iteratedFDeriv ℝ (m + 1) f x v)
  rw [iteratedFDeriv_one_apply]
  rfl

/-- For each proper block, applying the corresponding derivative of the
outer function to the lower-order derivatives preserves their common
spatial regularity. -/
theorem contDiffOn_iteratedFDeriv_comp_lower_terms {X Y Z P : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : Y → Z} (hg : ContDiff ℝ ∞ g)
    {A : X → Y} {S : Set X} {r : ℕ∞ω} (hr : r ≤ ∞) (hA : ContDiffOn ℝ r A S)
    {m : ℕ} (D : (j : ℕ) → X → (Fin j → P) → Y)
    (hD : ∀ j ≤ m, ∀ v, ContDiffOn ℝ r (fun x => D j x v) S)
    (v : Fin (m + 1) → P) :
    ContDiffOn ℝ r (fun x =>
      ∑ c ∈ Finset.univ.erase (oneBlockPartition m),
        iteratedFDeriv ℝ c.length g (A x)
          (fun j => D (c.partSize j) x (v ∘ c.emb j))) S := by
  classical
  have hOrder (j : ℕ) : (∞ : ℕ∞ω) + j ≤ ∞ := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact (add_le_add_right ih (1 : ℕ∞ω)).trans (show (∞ : ℕ∞ω) + 1 ≤ ∞ by rw [ENat.coe_top_add_one])
  have hOuter (j : ℕ) : ContDiffOn ℝ r (fun x => iteratedFDeriv ℝ j g (A x)) S :=
    ((hg.iteratedFDeriv_right (m := ∞) (hOrder j)).of_le hr).comp_contDiffOn hA
  refine ContDiffOn.sum fun c hc => ?_
  have hProper := (Finset.mem_erase.mp hc).1
  have hArgs : ContDiffOn ℝ r
      (fun x (j : Fin c.length) => D (c.partSize j) x (v ∘ c.emb j)) S :=
    contDiffOn_pi.mpr fun j => hD _ (OrderedFinpartition.partSize_le_of_ne_oneBlock c hProper j) _
  let I : (Y [×c.length]→L[ℝ] Z) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Y) Z) := ContinuousLinearMap.id ℝ _
  let ev := fun p : (Y [×c.length]→L[ℝ] Z) × (Fin c.length → Y) => p.1 p.2
  have hev : ContDiff ℝ r ev :=
    (contDiff_omega_iff_analyticOnNhd.mpr I.analyticOnNhd_uncurry_of_multilinear).of_le le_top
  exact hev.comp_contDiffOn ((hOuter c.length).prodMk hArgs)

end KEBall
