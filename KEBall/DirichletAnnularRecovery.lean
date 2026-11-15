import KEBall.DirichletIteratedAngular

/-! The determinant recovers the last derivative on a closed-ball annulus. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

/-- A positive classical solution of a positive continuous density on the
closed ball has a positive within Hessian with the same determinant up to
the boundary. -/
theorem closedBall_withinHessian_posDef_and_det_of_C2 {n : ℕ} {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hf : ContinuousOn f (closedUnitBall n))
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) f (unitBall n)) :
    ∀ x ∈ closedUnitBall n,
      let A := complexHessianOfRealBilinear
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n) x)
      A.PosDef ∧ A.det.re = f x := by
  let S := closedUnitBall n
  let B := fderivWithin ℝ (fderivWithin ℝ u S) S
  let A (x : E n) := complexHessianOfRealBilinear (B x)
  have hI : interior S = unitBall n := interior_closedBall _ (by norm_num)
  have hCl : closure (unitBall n) = S := closure_ball (0 : E n) (by norm_num)
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    (hI.symm ▸ nonempty_ball.mpr (show 0 < (1 : ℝ) by norm_num))
  have hB : ContDiffOn ℝ 0 B S :=
    (hu.fderivWithin (m := 1) hS (by norm_num)).fderivWithin hS (by norm_num)
  have hA : ContinuousOn A S := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear hB i j).continuousOn
  have hInterior (x : E n) (hx : x ∈ unitBall n) : A x = complexHessian u x := by
    change complexHessianOfRealBilinear (B x) = _
    rw [show B x = realHessian u x from fderivWithin_fderivWithin_eq_of_mem_nhds
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)]
    exact complexHessianOfRealBilinear_eq
      ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx))
  have hD : ContinuousOn (fun x => (A x).det.re) S :=
    Complex.continuous_re.comp_continuousOn (continuous_id.matrix_det.comp_continuousOn hA)
  have hDEq : EqOn (fun x => (A x).det.re) f S := by
    refine EqOn.of_subset_closure (fun x hx => ?_) hD hf ball_subset_closedBall hCl.ge
    rw [hInterior x hx]
    exact hEq hx
  intro x hx
  change (A x).PosDef ∧ (A x).det.re = f x
  refine ⟨?_, hDEq hx⟩
  have hxCl : x ∈ closure (unitBall n) := hCl.symm ▸ hx
  have : NeBot (𝓝[unitBall n] x) := mem_closure_iff_nhdsWithin_neBot.mp hxCl
  have hA' : Tendsto A (𝓝[unitBall n] x) (𝓝 (A x)) :=
    (hA x hx).mono_left (nhdsWithin_mono _ ball_subset_closedBall)
  have hHerm : (A x).IsHermitian := by
    ext i j
    have hEntry (a b : Fin n) : Tendsto (fun y => A y a b) (𝓝[unitBall n] x) (𝓝 (A x a b)) :=
      (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hA') a)) b
    have hLim := (continuous_star.tendsto (A x j i)).comp (hEntry j i)
    apply tendsto_nhds_unique hLim
    apply (hEntry i j).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    change A y i j = star (A y j i)
    rw [hInterior y hy]
    exact (congrFun (congrFun (huP y hy).isHermitian.eq i) j).symm
  have hNonneg (z : Fin n → ℂ) : 0 ≤ (star z ⬝ᵥ (A x *ᵥ z)).re := by
    have hCont : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => (star z ⬝ᵥ (M *ᵥ z)).re) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    apply ge_of_tendsto ((hCont.tendsto (A x)).comp hA')
    filter_upwards [self_mem_nhdsWithin] with y hy
    change 0 ≤ (star z ⬝ᵥ (A y *ᵥ z)).re
    rw [hInterior y hy]
    exact (huP y hy).posSemidef.re_dotProduct_nonneg z
  have hSemi : (A x).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
      (fun z => RCLike.nonneg_iff.mpr ⟨hNonneg z, hHerm.im_star_dotProduct_mulVec_self z⟩)
  apply hSemi.posDef_iff_det_ne_zero.mpr
  intro he
  have hz := hDEq hx
  change (A x).det.re = f x at hz
  rw [he, Complex.zero_re] at hz
  exact (hfPos x hx).ne' hz.symm

/-- To gain one derivative on a closed-ball annulus, it suffices to
recover the within Hessian from the derivatives along the unitary fields. -/
theorem contDiffOn_closedBall_inter_succ_of_withinHessian {n r : ℕ}
    {U : Set (E n)} (hU : IsOpen U) {u : E n → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (closedUnitBall n))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (hRot : ∀ i j, ContDiffOn ℝ (r + 1 : ℕ)
      (dirichletAngularDerivative (dirichletUnitaryRotation (b i) (b j)) u) (closedUnitBall n ∩ U))
    (hJ : ContDiffOn ℝ (r + 1 : ℕ)
      (dirichletAngularDerivative (JCLM n) u) (closedUnitBall n ∩ U))
    (hRecover :
      let S := closedUnitBall n
      let T := S ∩ U
      UniqueDiffOn ℝ T → T ⊆ closure (interior T) →
      (∀ i j, ContDiffOn ℝ (r + 1 : ℕ)
        (fun x => fderivWithin ℝ u T x (dirichletUnitaryRotation (b i) (b j) x)) T) →
      ContDiffOn ℝ (r + 1 : ℕ) (fun x => fderivWithin ℝ u T x (J x)) T →
      (∀ x ∈ T, fderivWithin ℝ (fderivWithin ℝ u S) S x =
        fderivWithin ℝ (fderivWithin ℝ u T) T x) →
      ContDiffOn ℝ r (fderivWithin ℝ (fderivWithin ℝ u T) T) T) :
    ContDiffOn ℝ (r + 2 : ℕ) u (closedUnitBall n ∩ U) := by
  let S := closedUnitBall n
  let T := S ∩ U
  have hI : interior S = unitBall n := interior_closedBall _ (by norm_num)
  have hC : closure (interior S) = S := by
    rw [hI, unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    rfl
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    (hI.symm ▸ nonempty_ball.mpr (show 0 < (1 : ℝ) by norm_num))
  have hT : UniqueDiffOn ℝ T := hS.inter hU
  have hNbhd (x : E n) (hx : x ∈ T) : T ∈ 𝓝[S] x :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.2))
  have hD₁ (x : E n) (hx : x ∈ T) : fderivWithin ℝ u S x = fderivWithin ℝ u T x :=
    fderivWithin_of_mem_nhdsWithin (hNbhd x hx) (hS x hx.1)
      ((hu2.mono inter_subset_left x hx).differentiableWithinAt (by norm_num))
  have hD₂ (x : E n) (hx : x ∈ T) :
      fderivWithin ℝ (fderivWithin ℝ u S) S x = fderivWithin ℝ (fderivWithin ℝ u T) T x :=
    fderivWithin_fderivWithin_eq_of_mem_nhdsWithin (hNbhd x hx)
      (hu2.mono inter_subset_left x hx) hS hT hx.1
  have hClosure : T ⊆ closure (interior T) := by
    rw [interior_inter, hU.interior_eq]
    intro x hx
    rw [inter_comm]
    exact hU.inter_closure ⟨hx.2, by simpa only [hC] using hx.1⟩
  have hJ' : ContDiffOn ℝ (r + 1 : ℕ) (fun x => fderivWithin ℝ u T x (J x)) T := by
    refine hJ.congr fun x hx => ?_
    unfold dirichletAngularDerivative
    rw [hD₁ x hx, JCLM_apply]
  have hBT := hRecover hT hClosure (fun i j => (hRot i j).congr fun x hx => by
    unfold dirichletAngularDerivative
    rw [hD₁ x hx]) hJ' hD₂
  have hD : ContDiffOn ℝ 1 (fderivWithin ℝ u T) T :=
    (hu2.mono inter_subset_left).fderivWithin hT (by norm_num)
  have hD' : ContDiffOn ℝ ((r : ℕ∞ω) + 1) (fderivWithin ℝ u T) T :=
    contDiffOn_succ_of_fderivWithin (hD.differentiableOn one_ne_zero) (by simp) hBT
  have huT : DifferentiableOn ℝ u T := (hu2.mono inter_subset_left).differentiableOn (by norm_num)
  have hResult := contDiffOn_succ_of_fderivWithin huT
    (n := (r : ℕ∞ω) + 1) (by simp) hD'
  simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hResult

/-- If the first angular derivatives have one extra order on the closed
ball, then the potential gains one order on its intersection with an
open set away from the origin. -/
theorem contDiffOn_closedBall_inter_succ_of_angularDerivatives_det {n r : ℕ}
    {U : Set (E n)} (hU : IsOpen U) (hAway : (0 : E n) ∉ U)
    {u f : E n → ℝ} (hu2 : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hu : ContDiffOn ℝ (r + 1 : ℕ) u (closedUnitBall n ∩ U))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (hRot : ∀ i j, ContDiffOn ℝ (r + 1 : ℕ)
      (dirichletAngularDerivative (dirichletUnitaryRotation (b i) (b j)) u) (closedUnitBall n ∩ U))
    (hJ : ContDiffOn ℝ (r + 1 : ℕ)
      (dirichletAngularDerivative (JCLM n) u) (closedUnitBall n ∩ U))
    (hf : ContDiffOn ℝ r f (closedUnitBall n ∩ U))
    (hPos : ∀ x ∈ closedUnitBall n ∩ U,
      (complexHessianOfRealBilinear
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n) x)).PosDef)
    (hDet : ∀ x ∈ closedUnitBall n ∩ U,
      (complexHessianOfRealBilinear
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n) x)).det.re = f x) :
    ContDiffOn ℝ (r + 2 : ℕ) u (closedUnitBall n ∩ U) := by
  apply contDiffOn_closedBall_inter_succ_of_withinHessian hU hu2 b hRot hJ
  dsimp only
  intro hT hClosure hRot' hJ' hD₂
  exact contDiffOn_fderivWithin_fderivWithin_of_unitaryRotations_det hT (Subset.rfl) hClosure
    (fun x hx h => hAway (h ▸ hx.2)) b (hu2.mono inter_subset_left) hu
    hRot' hJ' hf (fun x hx => hD₂ x hx ▸ hPos x hx) (fun x hx => hD₂ x hx ▸ hDet x hx)

/-- Positive closed-ball C³ solutions with C³ angular derivatives gain
C⁴ regularity away from the center. -/
theorem contDiffOn_closedBall_inter_four_of_angularDerivatives_det {n : ℕ}
    {U : Set (E n)} (hU : IsOpen U) (hAway : (0 : E n) ∉ U)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 3 u (closedUnitBall n))
    (hf : ContDiffOn ℝ 2 f (closedUnitBall n))
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) f (unitBall n))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (hRot : ∀ i j, ContDiffOn ℝ 3
      (dirichletAngularDerivative (dirichletUnitaryRotation (b i) (b j)) u) (closedUnitBall n))
    (hJ : ContDiffOn ℝ 3 (dirichletAngularDerivative (JCLM n) u) (closedUnitBall n)) :
    ContDiffOn ℝ 4 u (closedUnitBall n ∩ U) := by
  have hu₂ : ContDiffOn ℝ 2 u (closedUnitBall n) := hu.of_le (by norm_num)
  have hA := closedBall_withinHessian_posDef_and_det_of_C2 hu₂ hf.continuousOn hfPos huP hEq
  exact contDiffOn_closedBall_inter_succ_of_angularDerivatives_det (r := 2) hU hAway
    hu₂ (hu.mono inter_subset_left) b (fun i j => (hRot i j).mono inter_subset_left)
    (hJ.mono inter_subset_left) (hf.mono inter_subset_left)
    (fun x hx => (hA x hx.1).1) (fun x hx => (hA x hx.1).2)

/-- The fixed Sobolev local inverse gives C⁴ regularity on every
closed-ball annulus for a C³ solution with positive smooth density. -/
theorem contDiffOn_closedBall_inter_four_of_smooth_localInverse {n k : ℕ} (hn : 0 < n)
    (hkr : 3 + 2 * (2 * n + 1) ≤ k + 2)
    {U : Set (E n)} (hU : IsOpen U) (hAway : (0 : E n) ∉ U)
    {G : dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun _ ℝ) →
      dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ)}
    (T : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ))
      (w : E n → ℝ), ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = w x)
    {d : dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun _ ℝ)}
    (hG : ∀ᶠ q in 𝓝 d, ContDiffAt ℝ ∞ G q)
    (hSol : ∀ᶠ q in 𝓝 d, ∀ f : E n → ℝ, ContinuousOn f (unitBall n) → f =ᵐ[ν[n]] q.val.1 →
      ∃ w : E n → ℝ, ContDiffOn ℝ 2 w (closedUnitBall n) ∧
        (∀ x ∈ unitSphere n, w x = 0) ∧ (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
        EqOn (fun x => (complexHessian w x).det.re) f (unitBall n) ∧
        w =ᵐ[ν[n]] (G q).val.1)
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (hv : ContDiffOn ℝ 3 v (closedUnitBall n))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f)
    (hfPos : ∀ x ∈ closedUnitBall n, 0 < f x) :
    ContDiffOn ℝ 4 v (closedUnitBall n ∩ U) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have hv₂ : ContDiffOn ℝ 2 v (closedUnitBall n) := hv.of_le (by norm_num)
  have hAngle (R : E n →L[ℝ] E n) (hR : star R = -R) (hRJ : ∀ x, R (J x) = J (R x)) :
      ContDiffOn ℝ 3 (dirichletAngularDerivative R v) (closedUnitBall n) :=
    contDiffOn_angularDerivative_of_smooth_localInverse hn hkr T hT hG hSol
      hf hv₂ hv0 hvP hvEq hd R hR hRJ
  refine contDiffOn_closedBall_inter_four_of_angularDerivatives_det hU hAway hv
    ((hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn) hfPos hvP hvEq b ?_ ?_
  · intro i j
    exact hAngle _ (dirichletUnitaryRotation_star (b i) (b j))
      (dirichletUnitaryRotation_J (b i) (b j))
  · refine hAngle _ (JCLM_star n) ?_
    intro x
    simp only [JCLM_apply]

end KEBall
