import KEBall.DirichletBoundaryDirectionalJets

/-! Smooth extension across the sphere by transverse Borel interpolation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

local notation "I₋" => Icc (-(1 : ℝ) / 2) 0
local notation "I₊" => Icc (0 : ℝ) (1 / 2)
private def dirichletAnnulus (n : ℕ) : Set (E n) := {x | (3 : ℝ) / 4 < ‖x‖ ∧ ‖x‖ < 5 / 4}

local notation "U[" n "]" => dirichletAnnulus n

private theorem isOpen_dirichletAnnulus {n : ℕ} : IsOpen U[n] :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

private theorem uniqueDiffOn_dirichletClosedBall {n : ℕ} :
    UniqueDiffOn ℝ (closedUnitBall n) := by
  apply uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
  change (interior (closedBall (0 : E n) 1)).Nonempty
  rw [interior_closedBall _ (by norm_num)]
  exact nonempty_ball.mpr (by norm_num)

private theorem exists_compactSupport_radialJet {n : ℕ} {f : E n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedUnitBall n)) (k : ℕ) :
    ∃ A : E n → ℝ, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      EqOn A (fun x => iteratedFDerivWithin ℝ k f (closedUnitBall n)
        (dirichletRadialProjection x) (fun _ => dirichletRadialProjection x)) U[n] := by
  let b : ContDiffBump (1 : ℝ) :=
    ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let B (x : E n) := b ‖x‖
  let J (x : E n) := iteratedFDerivWithin ℝ k f (closedUnitBall n)
    (dirichletRadialProjection x) (fun _ => dirichletRadialProjection x)
  let A (x : E n) := B x * J x
  have hJ : ContDiffOn ℝ ∞ J ({0}ᶜ : Set (E n)) := contDiffOn_dirichletRadialJet hf k
  have hBzero (x : E n) (hx : ‖x‖ < 1 / 2) : B x = 0 := by
    apply b.zero_of_le_dist
    rw [Real.dist_eq, abs_of_neg (by linarith : ‖x‖ - 1 < 0)]
    change (1 : ℝ) / 2 ≤ _
    linarith
  have hNear (x : E n) (hx : x ≠ 0) : ({0}ᶜ : Set (E n)) ∈ 𝓝 x :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hx)
  have hA : ContDiff ℝ ∞ A := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))] with y hy
      simp only [A, hBzero y (mem_ball_zero_iff.mp hy), zero_mul]
    · exact (b.contDiff.comp_contDiffAt x (contDiffAt_norm ℝ hx)).mul (hJ.contDiffAt (hNear x hx))
  have hSupp : HasCompactSupport A := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E n) (3 / 2))
    intro x hx
    by_contra h
    have hNorm : (3 : ℝ) / 2 < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using h
    have hZ : B x = 0 := by
      apply b.zero_of_le_dist
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < ‖x‖ - 1)]
      change (1 : ℝ) / 2 ≤ _
      linarith
    exact hx (by simp only [A, hZ, zero_mul])
  refine ⟨A, hA, hSupp, fun x hx => ?_⟩
  have hB : B x = 1 := by
    apply b.one_of_mem_closedBall
    rw [mem_closedBall, Real.dist_eq, abs_le]
    change -(1 / 4 : ℝ) ≤ ‖x‖ - 1 ∧ ‖x‖ - 1 ≤ 1 / 4
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  change A x = J x
  simp only [A, hB, one_mul]

private theorem radialSlice_iteratedDerivWithin {n : ℕ} {f : E n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedUnitBall n)) {z : E n} (hz : ‖z‖ = 1)
    (k : ℕ) :
    iteratedDerivWithin k (fun t : ℝ => f ((1 + t) • z)) I₋ 0 =
      iteratedFDerivWithin ℝ k f (closedUnitBall n) z (fun _ => z) := by
  have hI : UniqueDiffOn ℝ I₋ := uniqueDiffOn_Icc (by norm_num)
  have hMap : MapsTo (fun t : ℝ => z + t • z) I₋ (closedUnitBall n) := by
    intro t ht
    change z + t • z ∈ closedUnitBall n
    rw [show z + t • z = (1 + t) • z by rw [add_smul, one_smul]]
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), hz, mul_one]
    linarith [ht.2]
  have h := iteratedDerivWithin_comp_line hf uniqueDiffOn_dirichletClosedBall hI
    z z hMap k (show (0 : ℝ) ∈ I₋ by norm_num)
  have hFun : (fun t : ℝ => z + t • z) = fun t => (1 + t) • z := by
    funext t
    rw [add_smul, one_smul]
  have he : (fun t : ℝ => f (z + t • z)) = fun t => f ((1 + t) • z) :=
    funext fun t => congrArg f (congrFun hFun t)
  rw [he] at h
  simp only [zero_smul, add_zero] at h
  rw [iteratedFDerivWithin_eq_foldr_directions hf uniqueDiffOn_dirichletClosedBall _
    (mem_closedBall_zero_iff.mpr hz.le), List.ofFn_const]
  exact h

private theorem closure_interior_dirichletCylinder {n : ℕ} {a b : ℝ} (h : a < b) :
    Icc a b ×ˢ U[n] ⊆ closure (interior (Icc a b ×ˢ U[n])) := by
  rw [interior_prod_eq, interior_Icc, isOpen_dirichletAnnulus.interior_eq,
    closure_prod_eq, closure_Ioo h.ne]
  exact prod_mono Subset.rfl subset_closure

private theorem exists_smooth_radial_cylinder_extension {n : ℕ} {f : E n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedUnitBall n)) :
    ∃ H : ℝ × E n → ℝ, ContDiffOn ℝ ∞ H (Icc (-(1 : ℝ) / 2) (1 / 2) ×ˢ U[n]) ∧
      EqOn H (fun p => f ((1 + p.1) • dirichletRadialProjection p.2)) (I₋ ×ˢ U[n]) := by
  classical
  choose A hA hAS hAJ using exists_compactSupport_radialJet hf
  obtain ⟨Q, hQ, hQJ⟩ := exists_contDiff_parametricBorel A hA hAS
  let P (p : ℝ × E n) := f ((1 + p.1) • dirichletRadialProjection p.2)
  let S : Set (ℝ × E n) := I₋ ×ˢ U[n]
  let T : Set (ℝ × E n) := I₊ ×ˢ U[n]
  have hU₀ : U[n] ⊆ ({0}ᶜ : Set (E n)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h
    have hn := hx.1
    rw [h, norm_zero] at hn
    linarith
  have hP : ContDiffOn ℝ ∞ P S := by
    apply hf.comp
    · have hProj : ContDiffOn ℝ ∞ (fun p : ℝ × E n => dirichletRadialProjection p.2) S :=
        contDiffOn_dirichletRadialProjection.comp contDiff_snd.contDiffOn (fun _ hp => hU₀ hp.2)
      exact (contDiff_const.add contDiff_fst).contDiffOn.smul hProj
    · intro p hp
      have ht := hp.1
      have hz := norm_dirichletRadialProjection (by simpa using hU₀ hp.2)
      apply mem_closedBall_zero_iff.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), hz, mul_one]
      linarith [ht.2]
  have hI : UniqueDiffOn ℝ I₋ := uniqueDiffOn_Icc (by norm_num)
  have hJ : UniqueDiffOn ℝ I₊ := uniqueDiffOn_Icc (by norm_num)
  have hU : UniqueDiffOn ℝ U[n] := isOpen_dirichletAnnulus.uniqueDiffOn
  have he (k : ℕ) : EqOn
      (fun x => iteratedDerivWithin k (fun t => P (t, x)) I₋ 0)
      (fun x => iteratedDerivWithin k (fun t => Q (t, x)) I₊ 0) U[n] := by
    intro x hx
    have hz := norm_dirichletRadialProjection (by simpa using hU₀ hx)
    have hQx : ContDiff ℝ ∞ (fun t : ℝ => Q (t, x)) :=
      hQ.comp (contDiff_id.prodMk contDiff_const)
    change iteratedDerivWithin k (fun t : ℝ => f ((1 + t) • dirichletRadialProjection x)) I₋ 0 =
      iteratedDerivWithin k (fun t : ℝ => Q (t, x)) I₊ 0
    rw [radialSlice_iteratedDerivWithin hf hz k,
      iteratedDerivWithin_eq_iteratedDeriv hJ
        ((hQx.of_le (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt)
        (show (0 : ℝ) ∈ I₊ by norm_num),
      hQJ, hAJ k hx]
  have hDer (k : ℕ) := eqOn_boundary_iteratedFDerivWithin_of_transverse
    hI hJ hU (closure_interior_dirichletCylinder (by norm_num))
    (closure_interior_dirichletCylinder (by norm_num))
    (show (0 : ℝ) ∈ I₋ by norm_num) (show (0 : ℝ) ∈ I₊ by norm_num) hP hQ.contDiffOn he k
  let H := S.piecewise P Q
  have hSmooth : ContDiffOn ℝ ∞ H (S ∪ T) := by
    intro p hp
    have hpU : p.2 ∈ U[n] := hp.elim (fun h => h.2) (fun h => h.2)
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (isOpen_dirichletAnnulus.mem_nhds hpU)
    let K := closedBall p.2 (r / 2)
    let S' := I₋ ×ˢ K
    let T' := I₊ ×ˢ K
    have hKU : K ⊆ U[n] := (closedBall_subset_ball (by linarith)).trans hrU
    have hDiffK : UniqueDiffOn ℝ K := by
      apply uniqueDiffOn_convex (convex_closedBall _ _)
      change (interior (closedBall p.2 (r / 2))).Nonempty
      rw [interior_closedBall _ (by positivity)]
      exact nonempty_ball.mpr (by positivity)
    have hP' := hP.mono (prod_mono Subset.rfl hKU : S' ⊆ S)
    have hQ' : ContDiffOn ℝ ∞ Q T' := hQ.contDiffOn
    have hJets : EqOn (ftaylorSeriesWithin ℝ P S') (ftaylorSeriesWithin ℝ Q T') (S' ∩ T') := by
      intro y hy
      have hyS : y ∈ S := (prod_mono Subset.rfl hKU : S' ⊆ S) hy.1
      have hyT : y ∈ T := (prod_mono Subset.rfl hKU : T' ⊆ T) hy.2
      have hy₀ : y.1 = 0 := le_antisymm hyS.1.2 hyT.1.1
      ext1 k
      change iteratedFDerivWithin ℝ k P S' y = iteratedFDerivWithin ℝ k Q T' y
      rw [iteratedFDerivWithin_subset (prod_mono Subset.rfl hKU : S' ⊆ S)
          (hI.prod hDiffK) (hI.prod hU) (hP.of_le (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hy.1,
        iteratedFDerivWithin_subset (prod_mono Subset.rfl hKU : T' ⊆ T)
          (hJ.prod hDiffK) (hJ.prod hU) (hQ.contDiffOn.of_le
            (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hy.2]
      have h := hDer k hyS.2
      change iteratedFDerivWithin ℝ k P S (0, y.2) =
        iteratedFDerivWithin ℝ k Q T (0, y.2) at h
      have he : (0, y.2) = y := Prod.ext hy₀.symm rfl
      rw [he] at h
      exact h
    have hS' : IsClosed S' := isClosed_Icc.prod isClosed_closedBall
    have hT' : IsClosed T' := isClosed_Icc.prod isClosed_closedBall
    have hC := (HasFTaylorSeriesUpToOn.union hS' hT'
      (hP'.ftaylorSeriesWithin (hI.prod hDiffK)) (hQ'.ftaylorSeriesWithin (hJ.prod hDiffK))
      hJets).contDiffOn
    have hCH : ContDiffOn ℝ ∞ H (S' ∪ T') := by
      apply hC.congr
      intro y hy
      rcases hy with hy | hy
      · have hys : y ∈ S := (prod_mono Subset.rfl hKU : S' ⊆ S) hy
        simp only [H, piecewise_eq_of_mem S _ _ hys, piecewise_eq_of_mem S' _ _ hy]
      · by_cases hys : y ∈ S
        · have hy' : y ∈ S' := ⟨hys.1, hy.2⟩
          simp only [H, piecewise_eq_of_mem S _ _ hys, piecewise_eq_of_mem S' _ _ hy']
        · have hy' : y ∉ S' := fun hh => hys (prod_mono Subset.rfl hKU hh)
          simp only [H, piecewise_eq_of_notMem S _ _ hys, piecewise_eq_of_notMem S' _ _ hy']
    have hKn : K ∈ 𝓝 p.2 :=
      mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self (show 0 < r / 2 by positivity)))
        ball_subset_closedBall
    have hN : S' ∪ T' ∈ 𝓝[S ∪ T] p := by
      apply mem_of_superset (inter_mem (self_mem_nhdsWithin : S ∪ T ∈ 𝓝[S ∪ T] p)
        (mem_nhdsWithin_of_mem_nhds (continuous_snd.continuousAt hKn)))
      intro y hy
      rcases hy.1 with hyS | hyT
      · exact Or.inl ⟨hyS.1, hy.2⟩
      · exact Or.inr ⟨hyT.1, hy.2⟩
    exact (hCH p (mem_of_mem_nhdsWithin hp hN)).mono_of_mem_nhdsWithin hN
  refine ⟨H, ?_, fun _ hp => piecewise_eq_of_mem _ _ _ hp⟩
  apply hSmooth.mono
  intro p hp
  by_cases h : p.1 ≤ 0
  · exact Or.inl ⟨⟨hp.1.1, h⟩, hp.2⟩
  · exact Or.inr ⟨⟨le_of_not_ge h, hp.1.2⟩, hp.2⟩

/-- Any smooth function on the closed ball admits an extension smooth
on an open neighborhood of that ball. -/
theorem exists_smoothNear_closedUnitBall_of_contDiffOn {n : ℕ} {f : E n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedUnitBall n)) :
    ∃ g : E n → ℝ, SmoothNear (closedUnitBall n) g ∧ EqOn g f (closedUnitBall n) := by
  classical
  obtain ⟨H, hH, he⟩ := exists_smooth_radial_cylinder_extension hf
  let W := U[n]
  let L (x : E n) : ℝ × E n := (‖x‖ - 1, x)
  let g := (closedUnitBall n).piecewise f (H ∘ L)
  have hW : IsOpen W := isOpen_dirichletAnnulus
  have hL : ContDiffOn ℝ ∞ L W := by
    apply ContDiffOn.prodMk _ contDiffOn_id
    apply ContDiffOn.sub _ contDiffOn_const
    intro x hx
    have hx' : x ≠ 0 := by
      intro heq
      have hn := hx.1
      rw [heq, norm_zero] at hn
      linarith
    exact (contDiffAt_norm ℝ hx').contDiffWithinAt
  have hLMap : MapsTo L W (Icc (-(1 : ℝ) / 2) (1 / 2) ×ˢ W) := by
    intro x hx
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hx⟩
  have hComp := hH.comp hL hLMap
  have hAgree : EqOn g (H ∘ L) W := by
    intro x hx
    by_cases hxB : x ∈ closedUnitBall n
    · have hxU : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hxB
      have hPos : 0 < ‖x‖ := by linarith [hx.1]
      have hP : L x ∈ I₋ ×ˢ W := ⟨⟨by linarith [hx.1], by linarith⟩, hx⟩
      rw [show g x = f x from piecewise_eq_of_mem _ _ _ hxB]
      change f x = H (L x)
      rw [he hP]
      change f x = f ((1 + (‖x‖ - 1)) • dirichletRadialProjection x)
      rw [show 1 + (‖x‖ - 1) = ‖x‖ by ring, dirichletRadialProjection, smul_smul,
        mul_inv_cancel₀ hPos.ne', one_smul]
    · exact piecewise_eq_of_notMem _ _ _ hxB
  refine ⟨g, ⟨unitBall n ∪ W, isOpen_ball.union hW, ?_, ?_⟩, fun _ hx => piecewise_eq_of_mem _ _ _ hx⟩
  · intro x hx
    by_cases hxB : x ∈ unitBall n
    · exact Or.inl hxB
    · have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
      have hx₁ : 1 ≤ ‖x‖ := not_lt.mp (fun h => hxB (mem_ball_zero_iff.mpr h))
      exact Or.inr ⟨by linarith, by linarith⟩
  · exact ((hf.mono ball_subset_closedBall).congr
      (fun _ hx => piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hx))).union_of_isOpen
      (hComp.congr (fun _ hx => hAgree hx)) isOpen_ball hW

end KEBall
