import KEBall.DirichletParametricBorel
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Directional derivatives and transverse jets on a cylinder with boundary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Function
open scoped ContDiff Topology

namespace KEBall

private theorem finite_order_le_infty (k : ℕ) : (k : ℕ∞ω) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

private theorem finite_order_lt_infty (k : ℕ) : (k : ℕ∞ω) < ∞ :=
  WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)

noncomputable def withinDirectionalDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) (d : E)
    (f : E → ℝ) (x : E) : ℝ := fderivWithin ℝ f s x d

theorem contDiffOn_withinDirectionalDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (d : E) :
    ContDiffOn ℝ ∞ (withinDirectionalDerivative s d f) s :=
  ((contDiffOn_infty_iff_fderivWithin hs).mp hf).2.clm_apply contDiffOn_const

theorem contDiffOn_foldr_withinDirectionalDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (ds : List E) :
    ContDiffOn ℝ ∞ (ds.foldr (withinDirectionalDerivative s) f) s := by
  induction ds with
  | nil => exact hf
  | cons d ds ih => exact contDiffOn_withinDirectionalDerivative ih hs d

theorem eqOn_withinDirectionalDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f g : E → ℝ}
    (h : EqOn f g s) (d : E) : EqOn (withinDirectionalDerivative s d f)
      (withinDirectionalDerivative s d g) s := by
  intro x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L d) (fderivWithin_congr h (h hx))

theorem iteratedFDerivWithin_eq_foldr_directions {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    {k : ℕ} (v : Fin k → E) {x : E} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ k f s x v =
      (List.ofFn v).foldr (withinDirectionalDerivative s) f x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      have hD := hf.differentiableOn_iteratedFDerivWithin (finite_order_lt_infty k) hs x hx
      rw [iteratedFDerivWithin_succ_apply_left,
        ← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) hD, List.ofFn_succ]
      simp only [List.foldr_cons, withinDirectionalDerivative]
      exact congrArg (fun L : E →L[ℝ] ℝ => L (v 0))
        (fderivWithin_congr (fun y hy => ih (Fin.tail v) hy) (ih (Fin.tail v) hx))

theorem foldr_withinDirectionalDerivative_perm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (hClosure : s ⊆ closure (interior s))
    {ds es : List E} (h : ds.Perm es) :
    EqOn (ds.foldr (withinDirectionalDerivative s) f) (es.foldr (withinDirectionalDerivative s) f) s := by
  induction h with
  | nil => exact fun _ _ => rfl
  | cons d _ ih => exact eqOn_withinDirectionalDerivative ih d
  | swap d e ds =>
      intro x hx
      let g := ds.foldr (withinDirectionalDerivative s) f
      have hg := contDiffOn_foldr_withinDirectionalDerivative hf hs ds
      have hSym := (hg x hx).isSymmSndFDerivWithinAt (by simp; norm_cast) hs (hClosure hx) hx
      have hD := ((contDiffOn_infty_iff_fderivWithin hs).mp hg).2.differentiableOn (by simp) x hx
      change fderivWithin ℝ (fun y => fderivWithin ℝ g s y d) s x e =
        fderivWithin ℝ (fun y => fderivWithin ℝ g s y e) s x d
      rw [fderivWithin_clm_apply (hs x hx) hD (differentiableWithinAt_const d),
        fderivWithin_clm_apply (hs x hx) hD (differentiableWithinAt_const e)]
      simpa only [fderivWithin_const_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_zero, zero_add] using hSym.eq e d
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem hasFDerivWithinAt_comp_line {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {I : Set ℝ} {g : E → F} (x d : E) {t : ℝ}
    (hMap : MapsTo (fun u : ℝ => x + u • d) I s)
    (hg : DifferentiableWithinAt ℝ g s (x + t • d)) :
    HasDerivWithinAt (fun u : ℝ => g (x + u • d)) (fderivWithin ℝ g s (x + t • d) d) I t := by
  have hL : HasDerivAt (fun u : ℝ => x + u • d) d t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const d).const_add x
  exact hg.hasFDerivWithinAt.comp_hasDerivWithinAt t hL.hasDerivWithinAt hMap

/-- Transverse derivatives of a restriction to an affine line are the
iterated ambient directional derivatives on the domain of the restriction. -/
theorem iteratedDerivWithin_comp_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {I : Set ℝ} {g : E → ℝ}
    (hg : ContDiffOn ℝ ∞ g s) (hs : UniqueDiffOn ℝ s) (hI : UniqueDiffOn ℝ I)
    (x d : E) (hMap : MapsTo (fun u : ℝ => x + u • d) I s) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun u : ℝ => g (x + u • d)) I)
      (fun t => (List.replicate k d).foldr (withinDirectionalDerivative s) g (x + t • d)) I := by
  induction k with
  | zero => simp [EqOn]
  | succ k ih =>
      intro t ht
      let G := (List.replicate k d).foldr (withinDirectionalDerivative s) g
      have hG := contDiffOn_foldr_withinDirectionalDerivative hg hs (List.replicate k d)
      have h := hasFDerivWithinAt_comp_line x d hMap
        (hG.differentiableOn (by simp) _ (hMap ht))
      rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih ht),
        h.derivWithin (hI t ht)]
      rfl

private theorem foldr_withinDirectionalDerivative_comp_slice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} {U : Set E}
    (hI : UniqueDiffOn ℝ I) (hU : UniqueDiffOn ℝ U) {t : ℝ} (ht : t ∈ I)
    {f : ℝ × E → ℝ} (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) (ds : List E) :
    EqOn ((ds.map (fun d => (0, d))).foldr (withinDirectionalDerivative (I ×ˢ U)) f ∘
      fun x => (t, x)) (ds.foldr (withinDirectionalDerivative U) (fun x => f (t, x))) U := by
  induction ds with
  | nil => exact fun _ _ => rfl
  | cons d ds ih =>
      let G := (ds.map (fun d => (0, d))).foldr (withinDirectionalDerivative (I ×ˢ U)) f
      have hG := contDiffOn_foldr_withinDirectionalDerivative hf (hI.prod hU)
        (ds.map (fun d => (0, d)))
      intro x hx
      have hMap : MapsTo (fun y : E => (t, y)) U (I ×ˢ U) := fun _ hy => ⟨ht, hy⟩
      have hD : HasFDerivAt (fun y : E => (t, y))
          ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) x :=
        (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
      have h := ((hG.differentiableOn (by simp) _ ⟨ht, hx⟩).hasFDerivWithinAt.comp x
        hD.hasFDerivWithinAt hMap).fderivWithin (hU x hx)
      have hEq := fderivWithin_congr (𝕜 := ℝ) ih (ih hx)
      change fderivWithin ℝ G (I ×ˢ U) (t, x) (0, d) = fderivWithin ℝ
        (ds.foldr (withinDirectionalDerivative U) (fun y => f (t, y))) U x d
      rw [← hEq, h]
      rfl

private theorem list_perm_transverse_then_tangent {E : Type*} [Zero E]
    (ds : List (ℝ × E)) (h : ∀ v ∈ ds, v = (1, 0) ∨ ∃ d : E, v = (0, d)) :
    ∃ (k : ℕ) (es : List E), ds.Perm (es.map (fun d => (0, d)) ++ List.replicate k (1, 0)) := by
  induction ds with
  | nil => exact ⟨0, [], List.Perm.nil⟩
  | cons d ds ih =>
      obtain ⟨k, es, he⟩ := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
      rcases h d List.mem_cons_self with rfl | ⟨v, rfl⟩
      · refine ⟨k + 1, es, (he.cons _).trans ?_⟩
        rw [show k + 1 = k.succ from rfl, List.replicate_succ]
        exact List.perm_middle.symm
      · exact ⟨k, v :: es, he.cons _⟩

private theorem eqOn_foldr_transverse_eq_iteratedDerivWithin {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} {U : Set E}
    (hI : UniqueDiffOn ℝ I) (hU : UniqueDiffOn ℝ U) {f : ℝ × E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) (k : ℕ) {t : ℝ} (ht : t ∈ I) :
    EqOn (fun x => (List.replicate k ((1 : ℝ), (0 : E))).foldr
      (withinDirectionalDerivative (I ×ˢ U)) f (t, x))
      (fun x => iteratedDerivWithin k (fun u => f (u, x)) I t) U := by
  intro x hx
  have hMap : MapsTo (fun u : ℝ => ((0 : ℝ), x) + u • (1, (0 : E))) I (I ×ˢ U) := by
    intro u hu
    simpa using (show (u, x) ∈ I ×ˢ U from ⟨hu, hx⟩)
  have h := iteratedDerivWithin_comp_line hf (hI.prod hU) hI (0, x) (1, 0) hMap k ht
  simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, Prod.mk_add_mk, zero_add, add_zero] using h.symm

/-- Matching every transverse derivative as a function of the tangential
parameter forces equality of all mixed derivatives on the interface. -/
theorem eqOn_boundary_foldr_of_transverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I J : Set ℝ} {U : Set E}
    (hI : UniqueDiffOn ℝ I) (hJ : UniqueDiffOn ℝ J) (hU : UniqueDiffOn ℝ U)
    (hI' : I ×ˢ U ⊆ closure (interior (I ×ˢ U)))
    (hJ' : J ×ˢ U ⊆ closure (interior (J ×ˢ U)))
    {t : ℝ} (htI : t ∈ I) (htJ : t ∈ J) {f g : ℝ × E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) (hg : ContDiffOn ℝ ∞ g (J ×ˢ U))
    (he : ∀ k, EqOn (fun x => iteratedDerivWithin k (fun u => f (u, x)) I t)
      (fun x => iteratedDerivWithin k (fun u => g (u, x)) J t) U)
    (ds : List (ℝ × E)) (hd : ∀ v ∈ ds, v = (1, 0) ∨ ∃ d : E, v = (0, d)) :
    EqOn (fun x => ds.foldr (withinDirectionalDerivative (I ×ˢ U)) f (t, x))
      (fun x => ds.foldr (withinDirectionalDerivative (J ×ˢ U)) g (t, x)) U := by
  obtain ⟨k, es, hP⟩ := list_perm_transverse_then_tangent ds hd
  let F := (List.replicate k ((1 : ℝ), (0 : E))).foldr (withinDirectionalDerivative (I ×ˢ U)) f
  let G := (List.replicate k ((1 : ℝ), (0 : E))).foldr (withinDirectionalDerivative (J ×ˢ U)) g
  have hF : ContDiffOn ℝ ∞ F (I ×ˢ U) := contDiffOn_foldr_withinDirectionalDerivative hf (hI.prod hU) _
  have hG : ContDiffOn ℝ ∞ G (J ×ˢ U) := contDiffOn_foldr_withinDirectionalDerivative hg (hJ.prod hU) _
  have hEq : EqOn (fun x => F (t, x)) (fun x => G (t, x)) U :=
    (eqOn_foldr_transverse_eq_iteratedDerivWithin hI hU hf k htI).trans
      ((he k).trans (eqOn_foldr_transverse_eq_iteratedDerivWithin hJ hU hg k htJ).symm)
  have hD : EqOn (es.foldr (withinDirectionalDerivative U) (fun x => F (t, x)))
      (es.foldr (withinDirectionalDerivative U) (fun x => G (t, x))) U := by
    clear hP
    induction es with
    | nil => exact hEq
    | cons d ds ih => exact eqOn_withinDirectionalDerivative ih d
  intro x hx
  change ds.foldr (withinDirectionalDerivative (I ×ˢ U)) f (t, x) =
    ds.foldr (withinDirectionalDerivative (J ×ˢ U)) g (t, x)
  rw [foldr_withinDirectionalDerivative_perm hf (hI.prod hU) hI' hP ⟨htI, hx⟩,
    foldr_withinDirectionalDerivative_perm hg (hJ.prod hU) hJ' hP ⟨htJ, hx⟩]
  simp only [List.foldr_append]
  exact (foldr_withinDirectionalDerivative_comp_slice hI hU htI hF es hx).trans
    ((hD hx).trans (foldr_withinDirectionalDerivative_comp_slice hJ hU htJ hG es hx).symm)

/-- Transverse matching on a cylinder implies equality of the full
Taylor jets, including all mixed derivatives on the interface. -/
theorem eqOn_boundary_iteratedFDerivWithin_of_transverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I J : Set ℝ} {U : Set E}
    (hI : UniqueDiffOn ℝ I) (hJ : UniqueDiffOn ℝ J) (hU : UniqueDiffOn ℝ U)
    (hI' : I ×ˢ U ⊆ closure (interior (I ×ˢ U)))
    (hJ' : J ×ˢ U ⊆ closure (interior (J ×ˢ U)))
    {t : ℝ} (htI : t ∈ I) (htJ : t ∈ J) {f g : ℝ × E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) (hg : ContDiffOn ℝ ∞ g (J ×ˢ U))
    (he : ∀ k, EqOn (fun x => iteratedDerivWithin k (fun u => f (u, x)) I t)
      (fun x => iteratedDerivWithin k (fun u => g (u, x)) J t) U) (k : ℕ) :
    EqOn (fun x => iteratedFDerivWithin ℝ k f (I ×ˢ U) (t, x))
      (fun x => iteratedFDerivWithin ℝ k g (J ×ˢ U) (t, x)) U := by
  classical
  intro x hx
  let F := iteratedFDerivWithin ℝ k f (I ×ˢ U) (t, x)
  let G := iteratedFDerivWithin ℝ k g (J ×ˢ U) (t, x)
  have hEq (v : Fin k → ℝ × E) (hv : ∀ i, v i = (1, 0) ∨ ∃ d : E, v i = (0, d)) :
      F v = G v := by
    change iteratedFDerivWithin ℝ k f (I ×ˢ U) (t, x) v =
      iteratedFDerivWithin ℝ k g (J ×ˢ U) (t, x) v
    rw [iteratedFDerivWithin_eq_foldr_directions hf (hI.prod hU) v ⟨htI, hx⟩,
      iteratedFDerivWithin_eq_foldr_directions hg (hJ.prod hU) v ⟨htJ, hx⟩]
    apply eqOn_boundary_foldr_of_transverse hI hJ hU hI' hJ' htI htJ hf hg he _ _ hx
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hv i
  change F = G
  ext v
  let w (i : Fin k) (b : Bool) : ℝ × E := if b then (1, 0) else (0, (v i).2)
  let c (i : Fin k) (b : Bool) : ℝ := if b then (v i).1 else 1
  have hV : v = fun i => ∑ b : Bool, c i b • w i b := by
    funext i
    rcases hv : v i with ⟨a, d⟩
    simp [hv, c, w, Prod.smul_mk]
  have hExpand (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) ℝ) :
      T v = ∑ b : Fin k → Bool, (∏ i, c i (b i)) * T (fun i => w i (b i)) := by
    have h := T.toMultilinearMap.map_sum (fun i b => c i b • w i b)
    simp only [ContinuousMultilinearMap.coe_coe, MultilinearMap.map_smul_univ, smul_eq_mul] at h
    simpa only [← hV] using h
  rw [hExpand F, hExpand G]
  apply Finset.sum_congr rfl
  intro b _
  rw [hEq _ (fun i => by by_cases hi : b i = true <;> simp [w, hi])]

end KEBall
