import KEBall.DirichletDistributionalDerivatives

/-! L² weak derivatives through arbitrary finite orders on the Dirichlet ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- The scalar function and all its tested weak derivatives through order k
are represented by square-integrable functions on the ball. -/
def HasDirichletWeakDerivativesL2 {n : ℕ} (f : E n → ℝ) (k : ℕ) : Prop :=
  MemLp f 2 ν[n] ∧ ∀ ds : List (E n), ds.length ≤ k →
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂ν[n]

theorem HasDirichletWeakDerivativesL2.of_le {n k m : ℕ} {f : E n → ℝ}
    (hf : HasDirichletWeakDerivativesL2 f m) (hkm : k ≤ m) :
    HasDirichletWeakDerivativesL2 f k :=
  ⟨hf.1, fun ds hds => hf.2 ds (hds.trans hkm)⟩

theorem dirichletWeakDerivativeTest_append_singleton {n : ℕ}
    {f F : E n → ℝ} (d : E n)
    (h : ∀ ψ : 𝓓B[n], dirichletWeakDerivativeTest f [d] ψ = ∫ x, ψ x * F x ∂ν[n])
    (ds : List (E n)) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest f (ds ++ [d]) ψ = dirichletWeakDerivativeTest F ds ψ := by
  induction ds generalizing ψ with
  | nil => exact h ψ
  | cons e es ih =>
      simp only [List.cons_append, dirichletWeakDerivativeTest, ih]

theorem HasDirichletWeakDerivativesL2.zero_order {n : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 ν[n]) : HasDirichletWeakDerivativesL2 f 0 := by
  refine ⟨hf, fun ds h => ?_⟩
  have he : ds = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
  subst ds
  exact ⟨f, hf, fun _ => rfl⟩

/-- A one-step characterization useful for differentiating an equation. -/
theorem hasDirichletWeakDerivativesL2_succ_iff {n : ℕ} {f : E n → ℝ} {k : ℕ} :
    HasDirichletWeakDerivativesL2 f (k + 1) ↔
      MemLp f 2 ν[n] ∧ ∀ d : E n, ∃ F : E n → ℝ,
        HasDirichletWeakDerivativesL2 F k ∧
        ∀ ψ : 𝓓B[n], (∫ x, ψ x * F x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]) := by
  constructor
  · intro hf
    refine ⟨hf.1, fun d => ?_⟩
    obtain ⟨F, hF, heF⟩ := hf.2 [d] (by simp)
    refine ⟨F, ⟨hF, fun ds hs => ?_⟩, fun ψ => (heF ψ).symm⟩
    obtain ⟨R, hR, heR⟩ := hf.2 (ds ++ [d]) (by simpa using Nat.succ_le_succ hs)
    exact ⟨R, hR, fun ψ =>
      (dirichletWeakDerivativeTest_append_singleton d heF ds ψ).symm.trans (heR ψ)⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun ds hs => ?_⟩
    cases ds with
    | nil => exact ⟨f, hf, fun _ => rfl⟩
    | cons d ds =>
        obtain ⟨F, hF, heF⟩ := h d
        have hF' (ψ : 𝓓B[n]) : dirichletWeakDerivativeTest f [d] ψ =
            ∫ x, ψ x * F x ∂ν[n] := (heF ψ).symm
        obtain ⟨R, hR, heR⟩ := hF.2 ds (by simpa using hs)
        refine ⟨R, hR, fun ψ => ?_⟩
        have hp : (d :: ds).Perm (ds ++ [d]) := by
          simpa only [List.singleton_append] using List.perm_append_comm (l₁ := [d]) (l₂ := ds)
        rw [dirichletWeakDerivativeTest_perm f hp,
          dirichletWeakDerivativeTest_append_singleton d hF', heR]

/-- The specified representative of a first weak derivative loses one
order of L² regularity. -/
theorem HasDirichletWeakDerivativesL2.of_directionalWeakDerivative {n : ℕ}
    {f F : E n → ℝ} {k : ℕ} (hf : HasDirichletWeakDerivativesL2 f (k + 1))
    (hF : MemLp F 2 ν[n]) (d : E n)
    (he : ∀ ψ : 𝓓B[n], (∫ x, ψ x * F x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n])) :
    HasDirichletWeakDerivativesL2 F k := by
  refine ⟨hF, fun ds hs => ?_⟩
  have he' (ψ : 𝓓B[n]) : dirichletWeakDerivativeTest f [d] ψ =
      ∫ x, ψ x * F x ∂ν[n] := (he ψ).symm
  obtain ⟨R, hR, heR⟩ := hf.2 (ds ++ [d]) (by simpa using Nat.succ_le_succ hs)
  exact ⟨R, hR, fun ψ =>
    (dirichletWeakDerivativeTest_append_singleton d he' ds ψ).symm.trans (heR ψ)⟩

/-- A specified list of derivatives lowers the weak order by the length
of the list. -/
theorem HasDirichletWeakDerivativesL2.exists_weakDerivativeTestL2 {n : ℕ}
    {f : E n → ℝ} (ds : List (E n)) (k : ℕ)
    (hf : HasDirichletWeakDerivativesL2 f (k + ds.length)) :
    ∃ F : E n → ℝ, HasDirichletWeakDerivativesL2 F k ∧ ∀ ψ : 𝓓B[n],
      dirichletWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂ν[n] := by
  induction ds generalizing f with
  | nil => exact ⟨f, hf, fun _ => rfl⟩
  | cons d ds ih =>
      have hf' : HasDirichletWeakDerivativesL2 f ((k + ds.length) + 1) := hf
      obtain ⟨G, hG, heG⟩ := (hasDirichletWeakDerivativesL2_succ_iff.mp hf').2 d
      obtain ⟨F, hF, heF⟩ := ih hG
      have he (ψ : 𝓓B[n]) : dirichletWeakDerivativeTest f [d] ψ =
          ∫ x, ψ x * G x ∂ν[n] := (heG ψ).symm
      have hp : (d :: ds).Perm (ds ++ [d]) := by
        simpa only [List.singleton_append] using List.perm_append_comm (l₁ := [d]) (l₂ := ds)
      exact ⟨F, hF, fun ψ => (dirichletWeakDerivativeTest_perm f hp ψ).trans
        ((dirichletWeakDerivativeTest_append_singleton d he ds ψ).trans (heF ψ))⟩

theorem HasDirichletWeakDerivativesL2.congr {n : ℕ} {f g : E n → ℝ} {k : ℕ}
    (hf : HasDirichletWeakDerivativesL2 f k) (he : f =ᵐ[ν[n]] g) :
    HasDirichletWeakDerivativesL2 g k := by
  have hD (ds : List (E n)) (ψ : 𝓓B[n]) :
      dirichletWeakDerivativeTest f ds ψ = dirichletWeakDerivativeTest g ds ψ := by
    induction ds generalizing ψ with
    | nil =>
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [hx]
    | cons d ds ih => simp only [dirichletWeakDerivativeTest, ih]
  refine ⟨MemLp.ae_eq he hf.1, fun ds hs => ?_⟩
  obtain ⟨F, hF, heF⟩ := hf.2 ds hs
  exact ⟨F, hF, fun ψ => (hD ds ψ).symm.trans (heF ψ)⟩

theorem dirichletWeakDerivativeTest_add_function {n : ℕ} (hn : 0 < n)
    {f g : E n → ℝ} (hf : MemLp f 2 ν[n]) (hg : MemLp g 2 ν[n])
    (ds : List (E n)) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest (f + g) ds ψ =
      dirichletWeakDerivativeTest f ds ψ + dirichletWeakDerivativeTest g ds ψ := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hI (φ : 𝓓B[n]) {p : E n → ℝ} (hp : MemLp p 2 ν[n]) :
      Integrable (fun x => φ x * p x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hp).integrable (by norm_num)
  induction ds generalizing ψ with
  | nil => simp only [dirichletWeakDerivativeTest, Pi.add_apply, mul_add,
      integral_add (hI ψ hf) (hI ψ hg)]
  | cons d ds ih => simp only [dirichletWeakDerivativeTest, ih, neg_add]

theorem dirichletWeakDerivativeTest_finsetSum {n : ℕ} {ι : Type*} (hn : 0 < n)
    (s : Finset ι) {f : ι → E n → ℝ} (h : ∀ i ∈ s, MemLp (f i) 2 ν[n])
    (ds : List (E n)) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest (fun x => ∑ i ∈ s, f i x) ds ψ =
      ∑ i ∈ s, dirichletWeakDerivativeTest (f i) ds ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      induction ds generalizing ψ with
      | nil => simp [dirichletWeakDerivativeTest]
      | cons d ds ih => simp only [dirichletWeakDerivativeTest, ih, neg_zero]
  | insert i s hi ih =>
      have hs : ∀ j ∈ s, MemLp (f j) 2 ν[n] := fun j hj => h j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      change dirichletWeakDerivativeTest (f i + fun x => ∑ j ∈ s, f j x) ds ψ = _
      rw [dirichletWeakDerivativeTest_add_function hn (h i (Finset.mem_insert_self i s))
        (memLp_finsetSum s hs), ih hs]

theorem dirichletWeakDerivativeTest_congr_tested {n : ℕ} {f g : E n → ℝ}
    (he : ∀ ψ : 𝓓B[n], (∫ x, ψ x * f x ∂ν[n]) = ∫ x, ψ x * g x ∂ν[n])
    (ds : List (E n)) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest f ds ψ = dirichletWeakDerivativeTest g ds ψ := by
  induction ds generalizing ψ with
  | nil => exact he ψ
  | cons d ds ih => simp only [dirichletWeakDerivativeTest, ih]

theorem HasDirichletWeakDerivativesL2.add {n : ℕ} (hn : 0 < n) {f g : E n → ℝ} {k : ℕ}
    (hf : HasDirichletWeakDerivativesL2 f k) (hg : HasDirichletWeakDerivativesL2 g k) :
    HasDirichletWeakDerivativesL2 (f + g) k := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hI (ψ : 𝓓B[n]) {p : E n → ℝ} (hp : MemLp p 2 ν[n]) :
      Integrable (fun x => ψ x * p x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hp).integrable (by norm_num)
  refine ⟨hf.1.add hg.1, fun ds hs => ?_⟩
  obtain ⟨F, hF, heF⟩ := hf.2 ds hs
  obtain ⟨G, hG, heG⟩ := hg.2 ds hs
  refine ⟨F + G, hF.add hG, fun ψ => ?_⟩
  rw [dirichletWeakDerivativeTest_add_function hn hf.1 hg.1, heF, heG]
  simp only [Pi.add_apply, mul_add, integral_add (hI ψ hF) (hI ψ hG)]

/-- Multiplication by a smooth function preserves all finite orders of
weak L² regularity on the ball. -/
theorem HasDirichletWeakDerivativesL2.mul_smooth {n : ℕ} (hn : 0 < n) {k : ℕ}
    {f c : E n → ℝ} (hf : HasDirichletWeakDerivativesL2 f k) (hc : ContDiff ℝ ∞ c) :
    HasDirichletWeakDerivativesL2 (fun x => c x * f x) k := by
  induction k generalizing f c with
  | zero =>
      exact HasDirichletWeakDerivativesL2.zero_order
        (memLp_dirichlet_mul_of_continuousOn hc.continuous.continuousOn hf.1)
  | succ k ih =>
      obtain ⟨hF, h⟩ := hasDirichletWeakDerivativesL2_succ_iff.mp hf
      refine hasDirichletWeakDerivativesL2_succ_iff.mpr
        ⟨memLp_dirichlet_mul_of_continuousOn hc.continuous.continuousOn hF, fun d => ?_⟩
      obtain ⟨F, hFk, heF⟩ := h d
      have hLower : HasDirichletWeakDerivativesL2 f k :=
        ⟨hf.1, fun ds hs => hf.2 ds (hs.trans (Nat.le_succ _))⟩
      have hD : ContDiff ℝ ∞ (fun x => fderiv ℝ c x d) :=
        (hc.fderiv_right (by simp)).clm_apply contDiff_const
      exact ⟨_, (ih hFk hc).add hn (ih hLower hD),
        (dirichletWeakDerivative_mul hn hF hFk.1 hc d heF).2⟩

theorem HasDirichletWeakDerivativesL2.finsetSum {n : ℕ} {ι : Type*} (hn : 0 < n)
    (s : Finset ι) {f : ι → E n → ℝ} {k : ℕ}
    (h : ∀ i ∈ s, HasDirichletWeakDerivativesL2 (f i) k) :
    HasDirichletWeakDerivativesL2 (fun x => ∑ i ∈ s, f i x) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero (ds : List (E n)) (ψ : 𝓓B[n]) :
          dirichletWeakDerivativeTest (0 : E n → ℝ) ds ψ = 0 := by
        induction ds generalizing ψ with
        | nil => simp [dirichletWeakDerivativeTest]
        | cons d ds ih => simp only [dirichletWeakDerivativeTest, ih, neg_zero]
      simp only [Finset.sum_empty]
      change HasDirichletWeakDerivativesL2 (0 : E n → ℝ) k
      exact ⟨MemLp.zero, fun ds _ => ⟨0, MemLp.zero, fun ψ => by simp [hzero]⟩⟩
  | insert i s hi ih =>
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi, Pi.add_def] using
        (h i (Finset.mem_insert_self i s)).add hn hs

/-- Smooth functions have all finite orders of L² weak regularity on the ball. -/
theorem HasDirichletWeakDerivativesL2.of_smooth {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    HasDirichletWeakDerivativesL2 f k := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hMem {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) : MemLp g 2 ν[n] :=
    MemLp.ae_eq (Eventually.of_forall fun x => mul_one (g x))
      (memLp_dirichlet_mul_of_continuousOn hg.continuous.continuousOn (memLp_const (1 : ℝ)))
  induction k generalizing f with
  | zero => exact HasDirichletWeakDerivativesL2.zero_order (hMem hf)
  | succ k ih =>
      refine hasDirichletWeakDerivativesL2_succ_iff.mpr ⟨hMem hf, fun d => ?_⟩
      let D (x : E n) := fderiv ℝ f x d
      have hD : ContDiff ℝ ∞ D := (hf.fderiv_right (by simp)).clm_apply contDiff_const
      refine ⟨D, ih hD, fun ψ => ?_⟩
      have he := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hf
        (contDiff_const (c := d))
      dsimp only at he
      have hz (x : E n) : dirichletVectorDivergence (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
          (fun _ => d) x = 0 := by simp [dirichletVectorDivergence]
      simp only [hz, mul_zero, add_zero] at he
      have he' := congrArg Neg.neg he.symm
      simpa only [neg_neg] using he'

/-- It suffices to test all lists of coordinate directions in one orthonormal
frame to obtain all weak derivatives through the same finite order. -/
theorem HasDirichletWeakDerivativesL2.of_coordinate_tests {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {k : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 ν[n])
    (h : ∀ is : List (Fin (2 * n)), is.length ≤ k →
      ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
        dirichletWeakDerivativeTest f (is.map b) ψ = ∫ x, ψ x * F x ∂ν[n]) :
    HasDirichletWeakDerivativesL2 f k := by
  induction k generalizing f with
  | zero => exact HasDirichletWeakDerivativesL2.zero_order hf
  | succ k ih =>
      have hCoord (i : Fin (2 * n)) := h [i] (by simp)
      choose F hF heF using hCoord
      have hFk (i : Fin (2 * n)) : HasDirichletWeakDerivativesL2 (F i) k := by
        apply ih (hF i)
        intro is his
        obtain ⟨R, hR, heR⟩ := h (is ++ [i]) (by simpa using Nat.succ_le_succ his)
        have he (ψ : 𝓓B[n]) : dirichletWeakDerivativeTest f [b i] ψ =
            ∫ x, ψ x * F i x ∂ν[n] := heF i ψ
        refine ⟨R, hR, fun ψ => ?_⟩
        rw [← dirichletWeakDerivativeTest_append_singleton (b i) he]
        simpa only [List.map_append, List.map_cons, List.map_nil] using heR ψ
      refine hasDirichletWeakDerivativesL2_succ_iff.mpr ⟨hf, fun d => ?_⟩
      have he (i : Fin (2 * n)) (ψ : 𝓓B[n]) :
          (∫ x, ψ x * F i x ∂ν[n]) =
            -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (b i) * f x ∂ν[n]) := (heF i ψ).symm
      have hSum := HasDirichletWeakDerivativesL2.finsetSum hn Finset.univ fun i _ =>
        (hFk i).mul_smooth hn (contDiff_const (c := inner ℝ (b i) d))
      exact ⟨_, hSum, (dirichletWeakDerivative_of_basis hn b hf F hF he d).2⟩

end KEBall
