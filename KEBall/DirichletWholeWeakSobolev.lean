import KEBall.DirichletWholeFourthDerivative

/-! Distributional L² regularity at every finite order on the whole space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

noncomputable abbrev euclideanTestLineDerivative {n : ℕ} (d : E n) (ψ : 𝓓E[n]) : 𝓓E[n] :=
  TestFunction.lineDerivCLM ℝ d ψ

noncomputable def euclideanWeakDerivativeTest {n : ℕ} (f : E n → ℝ) :
    List (E n) → 𝓓E[n] → ℝ
  | [], ψ => ∫ x, ψ x * f x ∂volume0 n
  | d :: ds, ψ => -euclideanWeakDerivativeTest f ds (euclideanTestLineDerivative d ψ)

private theorem euclideanTestLineDerivative_comm {n : ℕ} (d e : E n) (ψ : 𝓓E[n]) :
    euclideanTestLineDerivative e (euclideanTestLineDerivative d ψ) =
      euclideanTestLineDerivative d (euclideanTestLineDerivative e ψ) := by
  apply TestFunction.ext
  intro x
  rw [show euclideanTestLineDerivative e (euclideanTestLineDerivative d ψ) x =
    fderiv ℝ (euclideanTestLineDerivative d ψ : E n → ℝ) x e from euclideanTest_lineDeriv_apply _ _ _,
    show euclideanTestLineDerivative d (euclideanTestLineDerivative e ψ) x =
    fderiv ℝ (euclideanTestLineDerivative e ψ : E n → ℝ) x d from euclideanTest_lineDeriv_apply _ _ _,
    show (euclideanTestLineDerivative d ψ : E n → ℝ) =
      (fun y => fderiv ℝ (ψ : E n → ℝ) y d) from funext (euclideanTest_lineDeriv_apply ψ d),
    show (euclideanTestLineDerivative e ψ : E n → ℝ) =
      (fun y => fderiv ℝ (ψ : E n → ℝ) y e) from funext (euclideanTest_lineDeriv_apply ψ e)]
  have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const d),
    fderiv_clm_apply hd (differentiableAt_const e)]
  simpa using (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast) |>.eq e d

theorem euclideanWeakDerivativeTest_perm {n : ℕ} (f : E n → ℝ)
    {ds es : List (E n)} (h : ds.Perm es) (ψ : 𝓓E[n]) :
    euclideanWeakDerivativeTest f ds ψ = euclideanWeakDerivativeTest f es ψ := by
  induction h generalizing ψ with
  | nil => rfl
  | cons d h ih => simp only [euclideanWeakDerivativeTest, ih]
  | swap d e ds => simp only [euclideanWeakDerivativeTest]; rw [euclideanTestLineDerivative_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ ψ).trans (ih₂ ψ)

/-- The scalar function and all its tested weak derivatives through order k
are represented by square-integrable functions on the whole space. -/
def HasEuclideanWeakDerivativesL2 {n : ℕ} (f : E n → ℝ) (k : ℕ) : Prop :=
  MemLp f 2 (volume0 n) ∧ ∀ ds : List (E n), ds.length ≤ k →
    ∃ F : E n → ℝ, MemLp F 2 (volume0 n) ∧ ∀ ψ : 𝓓E[n],
      euclideanWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂(volume0 n)

theorem euclideanWeakDerivativeTest_append_singleton {n : ℕ}
    {f F : E n → ℝ} (d : E n)
    (h : ∀ ψ : 𝓓E[n], euclideanWeakDerivativeTest f [d] ψ = ∫ x, ψ x * F x ∂(volume0 n))
    (ds : List (E n)) (ψ : 𝓓E[n]) :
    euclideanWeakDerivativeTest f (ds ++ [d]) ψ = euclideanWeakDerivativeTest F ds ψ := by
  induction ds generalizing ψ with
  | nil => exact h ψ
  | cons e es ih =>
      simp only [List.cons_append, euclideanWeakDerivativeTest, ih]

theorem HasEuclideanWeakDerivativesL2.zero_order {n : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 (volume0 n)) : HasEuclideanWeakDerivativesL2 f 0 := by
  refine ⟨hf, fun ds h => ?_⟩
  have he : ds = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
  subst ds
  exact ⟨f, hf, fun _ => rfl⟩

/-- A one-step characterization useful for differentiating an equation. -/
theorem hasEuclideanWeakDerivativesL2_succ_iff {n : ℕ} {f : E n → ℝ} {k : ℕ} :
    HasEuclideanWeakDerivativesL2 f (k + 1) ↔
      MemLp f 2 (volume0 n) ∧ ∀ d : E n, ∃ F : E n → ℝ,
        HasEuclideanWeakDerivativesL2 F k ∧
        ∀ ψ : 𝓓E[n], (∫ x, ψ x * F x ∂(volume0 n)) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂(volume0 n)) := by
  constructor
  · intro hf
    refine ⟨hf.1, fun d => ?_⟩
    obtain ⟨F, hF, heF⟩ := hf.2 [d] (by simp)
    refine ⟨F, ⟨hF, fun ds hs => ?_⟩, fun ψ => (heF ψ).symm⟩
    obtain ⟨R, hR, heR⟩ := hf.2 (ds ++ [d]) (by simpa using Nat.succ_le_succ hs)
    exact ⟨R, hR, fun ψ =>
      (euclideanWeakDerivativeTest_append_singleton d heF ds ψ).symm.trans (heR ψ)⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun ds hs => ?_⟩
    cases ds with
    | nil => exact ⟨f, hf, fun _ => rfl⟩
    | cons d ds =>
        obtain ⟨F, hF, heF⟩ := h d
        have hF' (ψ : 𝓓E[n]) : euclideanWeakDerivativeTest f [d] ψ =
            ∫ x, ψ x * F x ∂(volume0 n) := (heF ψ).symm
        obtain ⟨R, hR, heR⟩ := hF.2 ds (by simpa using hs)
        refine ⟨R, hR, fun ψ => ?_⟩
        have hp : (d :: ds).Perm (ds ++ [d]) := by
          simpa only [List.singleton_append] using List.perm_append_comm (l₁ := [d]) (l₂ := ds)
        rw [euclideanWeakDerivativeTest_perm f hp,
          euclideanWeakDerivativeTest_append_singleton d hF', heR]

/-- The specified representative of a first weak derivative loses one
order of L² regularity. -/
theorem HasEuclideanWeakDerivativesL2.of_directionalWeakDerivative {n : ℕ}
    {f F : E n → ℝ} {k : ℕ} (hf : HasEuclideanWeakDerivativesL2 f (k + 1))
    (hF : MemLp F 2 (volume0 n)) (d : E n)
    (he : ∀ ψ : 𝓓E[n], (∫ x, ψ x * F x ∂(volume0 n)) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂(volume0 n))) :
    HasEuclideanWeakDerivativesL2 F k := by
  refine ⟨hF, fun ds hs => ?_⟩
  have he' (ψ : 𝓓E[n]) : euclideanWeakDerivativeTest f [d] ψ =
      ∫ x, ψ x * F x ∂(volume0 n) := (he ψ).symm
  obtain ⟨R, hR, heR⟩ := hf.2 (ds ++ [d]) (by simpa using Nat.succ_le_succ hs)
  exact ⟨R, hR, fun ψ =>
    (euclideanWeakDerivativeTest_append_singleton d he' ds ψ).symm.trans (heR ψ)⟩

/-- A specified list of derivatives lowers the weak order by the length
of the list. -/
theorem HasEuclideanWeakDerivativesL2.exists_weakDerivativeTestL2 {n : ℕ}
    {f : E n → ℝ} (ds : List (E n)) (k : ℕ)
    (hf : HasEuclideanWeakDerivativesL2 f (k + ds.length)) :
    ∃ F : E n → ℝ, HasEuclideanWeakDerivativesL2 F k ∧ ∀ ψ : 𝓓E[n],
      euclideanWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂(volume0 n) := by
  induction ds generalizing f with
  | nil => exact ⟨f, hf, fun _ => rfl⟩
  | cons d ds ih =>
      have hf' : HasEuclideanWeakDerivativesL2 f ((k + ds.length) + 1) := hf
      obtain ⟨G, hG, heG⟩ := (hasEuclideanWeakDerivativesL2_succ_iff.mp hf').2 d
      obtain ⟨F, hF, heF⟩ := ih hG
      have he (ψ : 𝓓E[n]) : euclideanWeakDerivativeTest f [d] ψ =
          ∫ x, ψ x * G x ∂(volume0 n) := (heG ψ).symm
      have hp : (d :: ds).Perm (ds ++ [d]) := by
        simpa only [List.singleton_append] using List.perm_append_comm (l₁ := [d]) (l₂ := ds)
      exact ⟨F, hF, fun ψ => (euclideanWeakDerivativeTest_perm f hp ψ).trans
        ((euclideanWeakDerivativeTest_append_singleton d he ds ψ).trans (heF ψ))⟩

theorem HasEuclideanWeakDerivativesL2.congr {n : ℕ} {f g : E n → ℝ} {k : ℕ}
    (hf : HasEuclideanWeakDerivativesL2 f k) (he : f =ᵐ[(volume0 n)] g) :
    HasEuclideanWeakDerivativesL2 g k := by
  have hD (ds : List (E n)) (ψ : 𝓓E[n]) :
      euclideanWeakDerivativeTest f ds ψ = euclideanWeakDerivativeTest g ds ψ := by
    induction ds generalizing ψ with
    | nil =>
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [hx]
    | cons d ds ih => simp only [euclideanWeakDerivativeTest, ih]
  refine ⟨MemLp.ae_eq he hf.1, fun ds hs => ?_⟩
  obtain ⟨F, hF, heF⟩ := hf.2 ds hs
  exact ⟨F, hF, fun ψ => (hD ds ψ).symm.trans (heF ψ)⟩

theorem euclideanWeakDerivativeTest_add_function {n : ℕ}
    {f g : E n → ℝ} (hf : MemLp f 2 (volume0 n)) (hg : MemLp g 2 (volume0 n))
    (ds : List (E n)) (ψ : 𝓓E[n]) :
    euclideanWeakDerivativeTest (f + g) ds ψ =
      euclideanWeakDerivativeTest f ds ψ + euclideanWeakDerivativeTest g ds ψ := by
  have hI (φ : 𝓓E[n]) {p : E n → ℝ} (hp : MemLp p 2 (volume0 n)) :
      Integrable (fun x => φ x * p x) (volume0 n) :=
    integrable_euclideanTest_mul φ hp
  induction ds generalizing ψ with
  | nil => simp only [euclideanWeakDerivativeTest, Pi.add_apply, mul_add,
      integral_add (hI ψ hf) (hI ψ hg)]
  | cons d ds ih => simp only [euclideanWeakDerivativeTest, ih, neg_add]

theorem euclideanWeakDerivativeTest_finsetSum {n : ℕ} {ι : Type*}
    (s : Finset ι) {f : ι → E n → ℝ} (h : ∀ i ∈ s, MemLp (f i) 2 (volume0 n))
    (ds : List (E n)) (ψ : 𝓓E[n]) :
    euclideanWeakDerivativeTest (fun x => ∑ i ∈ s, f i x) ds ψ =
      ∑ i ∈ s, euclideanWeakDerivativeTest (f i) ds ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      induction ds generalizing ψ with
      | nil => simp [euclideanWeakDerivativeTest]
      | cons d ds ih => simp only [euclideanWeakDerivativeTest, ih, neg_zero]
  | insert i s hi ih =>
      have hs : ∀ j ∈ s, MemLp (f j) 2 (volume0 n) := fun j hj => h j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      change euclideanWeakDerivativeTest (f i + fun x => ∑ j ∈ s, f j x) ds ψ = _
      rw [euclideanWeakDerivativeTest_add_function (h i (Finset.mem_insert_self i s))
        (memLp_finsetSum s hs), ih hs]

theorem euclideanWeakDerivativeTest_congr_tested {n : ℕ} {f g : E n → ℝ}
    (he : ∀ ψ : 𝓓E[n], (∫ x, ψ x * f x ∂(volume0 n)) = ∫ x, ψ x * g x ∂(volume0 n))
    (ds : List (E n)) (ψ : 𝓓E[n]) :
    euclideanWeakDerivativeTest f ds ψ = euclideanWeakDerivativeTest g ds ψ := by
  induction ds generalizing ψ with
  | nil => exact he ψ
  | cons d ds ih => simp only [euclideanWeakDerivativeTest, ih]

theorem HasEuclideanWeakDerivativesL2.add {n : ℕ} {f g : E n → ℝ} {k : ℕ}
    (hf : HasEuclideanWeakDerivativesL2 f k) (hg : HasEuclideanWeakDerivativesL2 g k) :
    HasEuclideanWeakDerivativesL2 (f + g) k := by
  have hI (ψ : 𝓓E[n]) {p : E n → ℝ} (hp : MemLp p 2 (volume0 n)) :
      Integrable (fun x => ψ x * p x) (volume0 n) :=
    integrable_euclideanTest_mul ψ hp
  refine ⟨hf.1.add hg.1, fun ds hs => ?_⟩
  obtain ⟨F, hF, heF⟩ := hf.2 ds hs
  obtain ⟨G, hG, heG⟩ := hg.2 ds hs
  refine ⟨F + G, hF.add hG, fun ψ => ?_⟩
  rw [euclideanWeakDerivativeTest_add_function hf.1 hg.1, heF, heG]
  simp only [Pi.add_apply, mul_add, integral_add (hI ψ hF) (hI ψ hG)]

/-- A smooth multiplier with bounded directional derivatives preserves
weak regularity through every fixed finite order. -/
theorem HasEuclideanWeakDerivativesL2.mul_smooth {n : ℕ} {k : ℕ}
    {f c : E n → ℝ} (hf : HasEuclideanWeakDerivativesL2 f k) (hc : ContDiff ℝ ∞ c)
    (hBound : ∀ ds : List (E n),
      MemLp (ds.foldr (fun d c x => fderiv ℝ c x d) c) ⊤ (volume0 n)) :
    HasEuclideanWeakDerivativesL2 (fun x => c x * f x) k := by
  have h₀ : MemLp c ⊤ (volume0 n) := hBound []
  induction k generalizing f c with
  | zero => exact HasEuclideanWeakDerivativesL2.zero_order (hf.1.mul' h₀)
  | succ k ih =>
      obtain ⟨hF, h⟩ := hasEuclideanWeakDerivativesL2_succ_iff.mp hf
      refine hasEuclideanWeakDerivativesL2_succ_iff.mpr ⟨hF.mul' h₀, fun d => ?_⟩
      obtain ⟨F, hFk, heF⟩ := h d
      have hLower : HasEuclideanWeakDerivativesL2 f k :=
        ⟨hf.1, fun ds hs => hf.2 ds (hs.trans (Nat.le_succ _))⟩
      let D (x : E n) := fderiv ℝ c x d
      have hD : ContDiff ℝ ∞ D := (hc.fderiv_right (by simp)).clm_apply contDiff_const
      have hD₁ : MemLp D ⊤ (volume0 n) := hBound [d]
      have hDBound (ds : List (E n)) :
          MemLp (ds.foldr (fun e c x => fderiv ℝ c x e) D) ⊤ (volume0 n) := by
        simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil, D] using hBound (ds ++ [d])
      have heF' (ψ : 𝓓E[n]) : (∫ x, ψ x * F x ∂volume0 n) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂volume0 n) := by
        simpa only [euclideanTestLineDerivative, euclideanTest_lineDeriv_apply] using heF ψ
      refine ⟨_, (ih hFk hc hBound h₀).add (ih hLower hD hDBound hD₁), fun ψ => ?_⟩
      simpa only [euclideanTestLineDerivative, euclideanTest_lineDeriv_apply, Pi.add_apply, D] using
        (euclideanWeakDerivative_mul d hF hFk.1 hc h₀ hD₁ heF').2 ψ

theorem HasEuclideanWeakDerivativesL2.finsetSum {n : ℕ} {ι : Type*}
    (s : Finset ι) {f : ι → E n → ℝ} {k : ℕ}
    (h : ∀ i ∈ s, HasEuclideanWeakDerivativesL2 (f i) k) :
    HasEuclideanWeakDerivativesL2 (fun x => ∑ i ∈ s, f i x) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero (ds : List (E n)) (ψ : 𝓓E[n]) :
          euclideanWeakDerivativeTest (0 : E n → ℝ) ds ψ = 0 := by
        induction ds generalizing ψ with
        | nil => simp [euclideanWeakDerivativeTest]
        | cons d ds ih => simp only [euclideanWeakDerivativeTest, ih, neg_zero]
      simp only [Finset.sum_empty]
      change HasEuclideanWeakDerivativesL2 (0 : E n → ℝ) k
      exact ⟨MemLp.zero, fun ds _ => ⟨0, MemLp.zero, fun ψ => by simp [hzero]⟩⟩
  | insert i s hi ih =>
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi, Pi.add_def] using
        (h i (Finset.mem_insert_self i s)).add hs


end KEBall
