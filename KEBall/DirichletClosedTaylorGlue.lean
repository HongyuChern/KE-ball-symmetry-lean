import KEBall.DirichletSmoothRepresentative

/-! Gluing smooth jets across the common boundary of two closed sets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology

namespace KEBall

theorem HasFTaylorSeriesUpToOn.union {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F}
    {P Q : E → FormalMultilinearSeries ℝ E F} {s t : Set E} [DecidablePred (· ∈ s)]
    (hs : IsClosed s) (ht : IsClosed t) (hf : HasFTaylorSeriesUpToOn ∞ f P s)
    (hg : HasFTaylorSeriesUpToOn ∞ g Q t) (hP : EqOn P Q (s ∩ t)) :
    HasFTaylorSeriesUpToOn ∞ (s.piecewise f g) (s.piecewise P Q) (s ∪ t) := by
  classical
  let w := s.piecewise f g
  let R := s.piecewise P Q
  have hF : EqOn f g (s ∩ t) := by
    intro x hx
    rw [← hf.zero_eq x hx.1, ← hg.zero_eq x hx.2, hP hx]
  have hsR : EqOn R P s := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have htR : EqOn R Q t := by
    intro x hx
    by_cases hy : x ∈ s
    · exact (hsR hy).trans (hP ⟨hy, hx⟩)
    · exact piecewise_eq_of_notMem _ _ _ hy
  have hsF : EqOn w f s := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have htF : EqOn w g t := by
    intro x hx
    by_cases hy : x ∈ s
    · exact (hsF hy).trans (hF ⟨hy, hx⟩)
    · exact piecewise_eq_of_notMem _ _ _ hy
  change HasFTaylorSeriesUpToOn ∞ w R (s ∪ t)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [hsR hx, hsF hx, hf.zero_eq x hx]
    · rw [htR hx, htF hx, hg.zero_eq x hx]
  · intro k hk x hx
    have hsD (hx : x ∈ s) : HasFDerivWithinAt (fun y => R y k) (R x (k + 1)).curryLeft s x := by
      rw [hsR hx]
      exact (hf.fderivWithin k hk x hx).congr (fun _ hy => congrFun (hsR hy) k)
        (congrFun (hsR hx) k)
    have htD (hx : x ∈ t) : HasFDerivWithinAt (fun y => R y k) (R x (k + 1)).curryLeft t x := by
      rw [htR hx]
      exact (hg.fderivWithin k hk x hx).congr (fun _ hy => congrFun (htR hy) k)
        (congrFun (htR hx) k)
    apply HasFDerivWithinAt.union
    · by_cases hxs : x ∈ s
      · exact hsD hxs
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [hs.closure_eq] using hxs)
    · by_cases hxt : x ∈ t
      · exact htD hxt
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [ht.closure_eq] using hxt)
  · intro k hk
    exact ((hf.cont k hk).congr (fun x hx => congrFun (hsR hx) k)).union_of_isClosed
      ((hg.cont k hk).congr (fun x hx => congrFun (htR hx) k)) hs ht

/-- All within derivatives of a smooth function on a set with unique
derivatives are themselves smooth on that set. -/
theorem ContDiffOn.contDiffOn_iteratedFDerivWithin_infty {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    (k : ℕ) : ContDiffOn ℝ ∞ (iteratedFDerivWithin ℝ k f s) s := by
  induction k with
  | zero =>
      rw [iteratedFDerivWithin_zero_eq_comp]
      let T := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv
      exact T.contDiff.comp_contDiffOn hf
  | succ k ih =>
      have hD := (contDiffOn_infty_iff_fderivWithin hs).mp ih |>.2
      rw [iteratedFDerivWithin_succ_eq_comp_left]
      let T := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv
      exact T.contDiff.comp_contDiffOn hD

noncomputable def dirichletRadialProjection {n : ℕ} (x : E n) : E n := ‖x‖⁻¹ • x

theorem norm_dirichletRadialProjection {n : ℕ} {x : E n} (hx : x ≠ 0) :
    ‖dirichletRadialProjection x‖ = 1 := by
  rw [dirichletRadialProjection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem contDiffOn_dirichletRadialProjection {n : ℕ} :
    ContDiffOn ℝ ∞ (dirichletRadialProjection : E n → E n) ({0}ᶜ : Set (E n)) := by
  intro x hx
  have hx' : x ≠ 0 := by simpa using hx
  exact ((contDiffAt_norm ℝ hx').inv (norm_ne_zero_iff.mpr hx')).smul
    contDiffAt_id |>.contDiffWithinAt

/-- Radial derivatives from the inner ball define smooth coefficients
on the punctured ambient space by radial projection to the sphere. -/
theorem contDiffOn_dirichletRadialJet {n : ℕ} {f : E n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedUnitBall n)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun x : E n =>
      iteratedFDerivWithin ℝ k f (closedUnitBall n) (dirichletRadialProjection x)
        (fun _ => dirichletRadialProjection x)) ({0}ᶜ : Set (E n)) := by
  have hU : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      (by change (interior (closedBall (0 : E n) 1)).Nonempty
          rw [interior_closedBall _ (by norm_num)]
          exact nonempty_ball.mpr (by norm_num))
  have hProj := contDiffOn_dirichletRadialProjection (n := n)
  have hP : MapsTo (dirichletRadialProjection : E n → E n) {0}ᶜ (closedUnitBall n) := by
    intro x hx
    exact mem_closedBall_zero_iff.mpr (norm_dirichletRadialProjection (by simpa using hx)).le
  have hD := ((ContDiffOn.contDiffOn_iteratedFDerivWithin_infty hf hU k).comp hProj hP)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let I (x : E n) := dirichletRadialProjection x
  let T (x : E n) := iteratedFDerivWithin ℝ k f (closedUnitBall n) (I x)
  let A (x : E n) (i : Fin k → Fin (2 * n)) :=
    (∏ j, inner ℝ (b (i j)) (I x)) * T x (fun j => b (i j))
  have hA (i : Fin k → Fin (2 * n)) :
      ContDiffOn ℝ ∞ (fun x => A x i) ({0}ᶜ : Set (E n)) := by
    apply ContDiffOn.mul
    · exact contDiffOn_prod fun j _ =>
        (innerSL ℝ (b (i j))).contDiff.comp_contDiffOn hProj
    · let C := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E n) ℝ (fun j => b (i j))
      exact C.contDiff.comp_contDiffOn hD
  have he (x : E n) : T x (fun _ => I x) = ∑ i : Fin k → Fin (2 * n), A x i := by
    classical
    let r (j : Fin (2 * n)) := inner ℝ (b j) (I x)
    have hRep : (fun _ : Fin k => I x) = fun _ => ∑ i, r i • b i :=
      funext fun _ => (b.sum_repr' (I x)).symm
    have h := (T x).toMultilinearMap.map_sum (fun (_ : Fin k) i => r i • b i)
    simp only [ContinuousMultilinearMap.coe_coe, MultilinearMap.map_smul_univ, smul_eq_mul] at h
    simpa only [← hRep, A, r] using h
  exact (ContDiffOn.sum (s := Finset.univ) (fun i _ => hA i)).congr (fun x _ => he x)

end KEBall
