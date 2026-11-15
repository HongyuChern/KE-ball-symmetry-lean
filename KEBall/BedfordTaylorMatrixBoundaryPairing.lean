import KEBall.BedfordTaylorHessianAdjoint
import KEBall.BedfordTaylorMatrixOrderLimit
import KEBall.BedfordTaylorMixedProduct

/-!
# Boundary pairing for mixed Bedford–Taylor coefficients
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines KEBallProbe
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private theorem coordinateRowColumnDensity_adjoint_apply (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (φ : 𝓓(Ω, ℝ))
    (I J : CoordinateTuple n (k + 1)) :
    coordinateRowDerivative (coordinateColumnDerivative (matrixOfDensities g hg)) I J φ =
      ∫ x, smoothHessianWedge φ g I J x := by
  let term (i j : Fin (k + 1)) (x : ComplexModel n) :=
    (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (classicalComplexHessianEntry φ
      (coordinateVector (I i)) (coordinateVector (J j)) x *
        g (i.removeNth I) (j.removeNth J) x)
  have hterm (i j : Fin (k + 1)) : Integrable (term i j) volume :=
    (integrable_classicalComplexHessianEntry_mul φ _ _
      (locallyIntegrableOn_of_contDiffOn (hg (i.removeNth I) (j.removeNth J)))).const_mul _
  let eval : 𝓓'(Ω, ℂ) →+ ℂ :=
    { toFun := fun T => T φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change eval (coordinateRowDerivative (coordinateColumnDerivative (matrixOfDensities g hg)) I J) = _
  simp only [coordinateRowDerivative, coordinateColumnDerivative, Matrix.of_apply,
    alternatingDerivative, map_sum, map_zsmul, Finset.smul_sum]
  calc
    _ = ∑ i, ∑ j, ∫ x, term i j x := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      change (-1 : ℤ) ^ (i : ℕ) • ((-1 : ℤ) ^ (j : ℕ) •
        wirtingerDerivative (coordinateVector (I i)) (Complex.I • coordinateVector (I i))
          (wirtingerDerivative (coordinateVector (J j)) (-(Complex.I • coordinateVector (J j)))
            (matrixOfDensities g hg (i.removeNth I) (j.removeNth J))) φ) = _
      rw [matrixOfDensities, Matrix.of_apply, wirtingerHessian_regular_apply,
        ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ]
      simp only [smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, term, pow_add,
        ← mul_assoc]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = ∫ x, ∑ i, ∑ j, term i j x := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
      exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => hterm i j)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [smoothHessianWedge, Matrix.of_apply, term, mul_assoc]

private theorem hessianWedge_congr_germ
    {u p : ComplexModel n → ℝ} {x : ComplexModel n} (he : u =ᶠ[𝓝 x] p)
    (g : CoordinateDensities n k k) (I J : CoordinateTuple n (k + 1)) :
    smoothHessianWedge u g I J x = smoothHessianWedge p g I J x := by
  have h (a b : ComplexModel n) :
      classicalComplexHessianEntry u a b x = classicalComplexHessianEntry p a b x := by
    have hC : (fun y => (u y : ℂ)) =ᶠ[𝓝 x] fun y => (p y : ℂ) := he.fun_comp (fun t : ℝ => (t : ℂ))
    have hD : dz b (-(Complex.I • b)) (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
        dz b (-(Complex.I • b)) (fun y => (p y : ℂ)) := by
      filter_upwards [hC.eventuallyEq_nhds] with y hy
      simp only [dz, rd, hy.fderiv_eq]
    simp only [classicalComplexHessianEntry, dz, rd, hD.fderiv_eq]
  simp only [smoothHessianWedge, Matrix.of_apply, h]

private theorem hessianWedge_weight_integrable
    (g : CoordinateDensities n k k) (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω)
    {p : ComplexModel n → ℝ} (hp : ContDiffOn ℝ ∞ p Ω) (φ : 𝓓(Ω, ℝ))
    (I J : CoordinateTuple n (k + 1)) :
    Integrable (fun x => (p x : ℂ) * smoothHessianWedge φ g I J x) volume := by
  simp only [smoothHessianWedge, Matrix.of_apply, Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hs : ContDiffOn ℝ ∞ (fun x => (p x : ℂ) * g (i.removeNth I) (j.removeNth J) x) Ω :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hp).mul (hg _ _)
  exact ((integrable_classicalComplexHessianEntry_mul φ (coordinateVector (I i))
    (coordinateVector (J j)) (locallyIntegrableOn_of_contDiffOn hs)).const_mul
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)))).congr
    (Eventually.of_forall fun x => by ring)

private theorem mixedProductStep_adjoint_apply_of_densities {p : ComplexModel n → ℝ}
    (hp : IsSmoothPshOn Ω p) (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (hPos : IsPositiveMatrixDistribution (matrixOfDensities g hg))
    (φ : 𝓓(Ω, ℝ)) (I J : CoordinateTuple n (k + 1)) :
    mixedProductStep (isLocallyBoundedPshOn_of_isSmoothPshOn hp) hPos I J φ =
      ∫ x, (p x : ℂ) * smoothHessianWedge φ g I J x := by
  let w : CoordinateDensities n k k := Matrix.of fun I J x => (p x : ℂ) * g I J x
  have hw : ∀ I J, ContDiffOn ℝ ∞ (w I J) Ω :=
    fun I J => (Complex.ofRealCLM.contDiff.comp_contDiffOn hp.1).mul (hg I J)
  unfold mixedProductStep
  rw [weightPositiveMatrixDistribution_of_densities hp g hg, coordinateRowColumnDensity_adjoint_apply w hw]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smoothHessianWedge, w, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem smoothPsh_cons {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u)
    {v : Fin k → ComplexModel n → ℝ} (hv : ∀ i, IsSmoothPshOn Ω (v i)) :
    ∀ r, IsSmoothPshOn Ω (Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) u v r) := by
  intro r
  induction r using Fin.cases with
  | zero => exact hu
  | succ r => exact hv r

/-- Coefficientwise integration by parts when the two smooth
potentials have a common germ off a compact set. -/
theorem smoothMixedProduct_swap_test
    {u p : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p)
    {v : Fin k → ComplexModel n → ℝ} (hv : ∀ i, IsSmoothPshOn Ω (v i))
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (he : EqOn u p ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I J : CoordinateTuple n (k + 1)) :
    mixedProduct (u := Fin.cons p v) (fun r =>
      isLocallyBoundedPshOn_of_isSmoothPshOn (smoothPsh_cons hp hv r)) I J (multiplySmoothTest χ hu.1) =
    mixedProduct (u := Fin.cons u v) (fun r =>
      isLocallyBoundedPshOn_of_isSmoothPshOn (smoothPsh_cons hu hv r)) I J (multiplySmoothTest χ hp.1) := by
  let U := multiplySmoothTest χ hu.1
  let P := multiplySmoothTest χ hp.1
  let g := smoothMixedDensities n k v
  have hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω :=
    contDiffOn_smoothMixedDensities v (fun r => (hv r).1)
  let hPos : IsPositiveMatrixDistribution (matrixOfDensities g hg) := smoothMixedDensities_isPositive v hv
  let vP := smoothPsh_cons hp hv
  let vU := smoothPsh_cons hu hv
  let A := mixedProduct (u := Fin.cons p v) (fun r => isLocallyBoundedPshOn_of_isSmoothPshOn (vP r)) I J U
  let B := mixedProduct (u := Fin.cons u v) (fun r => isLocallyBoundedPshOn_of_isSmoothPshOn (vU r)) I J P
  change A = B
  have hA : A = mixedProductStep (isLocallyBoundedPshOn_of_isSmoothPshOn hp) hPos I J U := by
    unfold A
    rw [mixedProduct_succ]
    have hTail : Fin.tail (Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) p v) = v :=
      Fin.tail_cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) p v
    have ht := (mixedProduct_congr_tuple hTail
      (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (vP i.succ)) (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hv i))).trans
      (mixedProduct_eq_smooth (u := v) hv)
    exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J U)
      (mixedProductStep_eq_of_coefficient_eq _ _ _ ht)
  have hB : B = mixedProductStep (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hPos I J P := by
    unfold B
    rw [mixedProduct_succ]
    have hTail : Fin.tail (Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) u v) = v :=
      Fin.tail_cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) u v
    have ht := (mixedProduct_congr_tuple hTail
      (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (vU i.succ)) (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hv i))).trans
      (mixedProduct_eq_smooth (u := v) hv)
    exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J P)
      (mixedProductStep_eq_of_coefficient_eq _ _ _ ht)
  have hA₁ : A = ∫ x, (p x : ℂ) * smoothHessianWedge U g I J x :=
    hA.trans (mixedProductStep_adjoint_apply_of_densities hp g hg hPos U I J)
  have hB₁ : B = ∫ x, (u x : ℂ) * smoothHessianWedge P g I J x :=
    hB.trans (mixedProductStep_adjoint_apply_of_densities hu g hg hPos P I J)
  have hA₂ : A = ∫ x, U x • smoothHessianWedge p g I J x := by
    unfold A
    rw [mixedProduct_eq_smooth vP]
    simp only [matrixOfDensities, Matrix.of_apply, complexRegularDistribution_apply]
    rfl
  have hB₂ : B = ∫ x, P x • smoothHessianWedge u g I J x := by
    unfold B
    rw [mixedProduct_eq_smooth vU]
    simp only [matrixOfDensities, Matrix.of_apply, complexRegularDistribution_apply]
    rfl
  have hiA : Integrable (fun x => U x • smoothHessianWedge p g I J x) :=
    U.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (locallyIntegrableOn_of_contDiffOn (contDiffOn_smoothHessianWedge g hg hp.1 I J))
  have hiB : Integrable (fun x => P x • smoothHessianWedge u g I J x) :=
    P.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (locallyIntegrableOn_of_contDiffOn (contDiffOn_smoothHessianWedge g hg hu.1 I J))
  have hAB : A - B = B - A := by
    rw [hA₁, hB₁, ← integral_sub (hessianWedge_weight_integrable g hg hp.1 U I J)
      (hessianWedge_weight_integrable g hg hu.1 P I J), ← hB₁, ← hA₁, hB₂, hA₂,
      ← integral_sub hiB hiA]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxK : x ∈ K
    · have hU : (U : ComplexModel n → ℝ) =ᶠ[𝓝 x] u := by
        filter_upwards [hχ x hxK] with y hy
        change χ y * u y = u y
        rw [show χ y = 1 from hy, one_mul]
      have hP : (P : ComplexModel n → ℝ) =ᶠ[𝓝 x] p := by
        filter_upwards [hχ x hxK] with y hy
        change χ y * p y = p y
        rw [show χ y = 1 from hy, one_mul]
      rw [hessianWedge_congr_germ hU, hessianWedge_congr_germ hP, hU.eq_of_nhds, hP.eq_of_nhds]
      simp only [Complex.real_smul]
    · by_cases hxΩ : x ∈ Ω
      · have h : u =ᶠ[𝓝 x] p := by
          filter_upwards [Ω.isOpen.mem_nhds hxΩ, hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy hyK
          exact he ⟨hy, hyK⟩
        have hUP : (U : ComplexModel n → ℝ) =ᶠ[𝓝 x] P := by
          filter_upwards [h] with y hy
          simp only [U, P, multiplySmoothTest_apply, hy]
        rw [hessianWedge_congr_germ h, hessianWedge_congr_germ hUP, h.eq_of_nhds, hUP.eq_of_nhds]
        simp
      · have hU : (U : ComplexModel n → ℝ) =ᶠ[𝓝 x] 0 := by
          filter_upwards [(isClosed_tsupport U).isOpen_compl.mem_nhds
            (show x ∉ tsupport U from fun hx => hxΩ (U.tsupport_subset hx))] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        have hP : (P : ComplexModel n → ℝ) =ᶠ[𝓝 x] 0 := by
          filter_upwards [(isClosed_tsupport P).isOpen_compl.mem_nhds
            (show x ∉ tsupport P from fun hx => hxΩ (P.tsupport_subset hx))] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        rw [hessianWedge_congr_germ hU, hessianWedge_congr_germ hP, hU.eq_of_nhds, hP.eq_of_nhds]
        have hzero (a b : ComplexModel n) :
            classicalComplexHessianEntry (0 : ComplexModel n → ℝ) a b x = 0 := by
          change classicalComplexHessianEntry (fun _ : ComplexModel n => (0 : ℝ)) a b x = 0
          rw [classicalComplexHessianEntry_eq_realHessian (contDiffAt_const (c := (0 : ℝ)))]
          simp [realHessian_eq_fderiv]
        simp [smoothHessianWedge, hzero]
  linear_combination hAB / 2

set_option maxHeartbeats 750000 in
/-- Integration by parts with smooth paired factors and locally
bounded PSH factors in the common tail. -/
theorem mixedProduct_swap_test_of_tail_approximation
    {u p : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p)
    {v : Fin k → ComplexModel n → ℝ} (hv : ∀ i, IsLocallyBoundedPshOn Ω (v i))
    {v' : ℕ → Fin k → ComplexModel n → ℝ}
    (hv' : ∀ j i, IsSmoothPshOn Ω (v' j i))
    (hanti : ∀ i x, x ∈ Ω → Antitone (fun j => v' j i x))
    (hlim : ∀ i x, x ∈ Ω → Tendsto (fun j => v' j i x) atTop (𝓝 (v i x)))
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (he : EqOn u p ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I J : CoordinateTuple n (k + 1)) :
    mixedProduct (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hp) hv)
      I J (multiplySmoothTest χ hu.1) =
    mixedProduct (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hv)
      I J (multiplySmoothTest χ hp.1) := by
  let U := multiplySmoothTest χ hu.1
  let P := multiplySmoothTest χ hp.1
  let A (w : Fin k → ComplexModel n → ℝ) (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) :=
    mixedProduct (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hp) hw) I J U
  let B (w : Fin k → ComplexModel n → ℝ) (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) :=
    mixedProduct (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hw) I J P
  let C (m : ℕ) : Prop :=
    ∀ w : Fin k → ComplexModel n → ℝ, ∀ hw : ∀ i, IsLocallyBoundedPshOn Ω (w i),
      (∀ i : Fin k, (i : ℕ) < m → IsSmoothPshOn Ω (w i)) →
      (∀ i : Fin k, m ≤ (i : ℕ) → w i = v i) → A w hw = B w hw
  have hCtop : C k := by
    intro w hw hpre _
    exact smoothMixedProduct_swap_test hu hp (fun i => hpre i i.isLt) hK he χ hχ I J
  have hC : C 0 := Nat.decreasingInduction' (fun m hm _ ih => by
    intro w hw hpre hpost
    let r : Fin k := ⟨m, hm⟩
    let w' (j : ℕ) := Function.update w r (v' j r)
    let hw' (j : ℕ) := locallyBoundedPsh_update (u := w) hw r
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hv' j r))
    have hwEq (j : ℕ) : A (w' j) (hw' j) = B (w' j) (hw' j) := by
      refine ih (w' j) (hw' j) ?_ ?_
      · intro i hi
        by_cases h : i = r
        · simpa [w', h] using hv' j r
        · simp only [w', Function.update_of_ne h]
          have hne : (i : ℕ) ≠ m := fun e => h (Fin.ext e)
          exact hpre i (by omega)
      · intro i hi
        have hne : i ≠ r := fun e => by
          have h := congrArg Fin.val e
          change (i : ℕ) = m at h
          omega
        simp only [w', Function.update_of_ne hne]
        exact hpost i (by omega)
    have hlimit (q : ComplexModel n → ℝ) (hq : IsSmoothPshOn Ω q) (φ : 𝓓(Ω, ℝ)) :
        Tendsto (fun j => mixedProduct
          (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hq) (hw' j)) I J φ)
          atTop (𝓝 (mixedProduct
            (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hq) hw) I J φ)) := by
      let a : Fin (k + 1) → ComplexModel n → ℝ := Fin.cons q w
      have ha : ∀ i, IsLocallyBoundedPshOn Ω (a i) :=
        locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hq) hw
      have haPre (i : Fin (k + 1)) (hi : i < r.succ) : IsSmoothPshOn Ω (a i) := by
        cases i using Fin.cases with
        | zero => exact hq
        | succ i => exact hpre i (Fin.succ_lt_succ_iff.mp hi)
      have haLim (x : ComplexModel n) (hx : x ∈ Ω) :
          Tendsto (fun j => v' j r x) atTop (𝓝 (a r.succ x)) := by
        change Tendsto (fun j => v' j r x) atTop (𝓝 (w r x))
        rw [hpost r le_rfl]
        exact hlim r x hx
      have h := weakMatrixLimit_mixedProduct_update (u := a) ha r.succ haPre
        (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hv' j r)) (hanti r) haLim
      apply (h I J φ).congr
      intro j
      have heq : Function.update a r.succ (v' j r) =
          Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) q (w' j) :=
        (Fin.cons_update (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) _ _ _ _).symm
      exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J φ)
        (mixedProduct_congr_tuple heq _ _)
    exact tendsto_nhds_unique (hlimit p hp U) ((hlimit u hu P).congr fun j => (hwEq j).symm))
    (Nat.zero_le _) hCtop
  exact hC v hv (fun _ hi => by omega) (fun _ _ => rfl)

/-- Common-boundary pairing with a smooth weight and a locally
bounded PSH factor with a common-boundary smooth approximation. -/
theorem integral_quadraticMeasure_mixedProduct_swap
    {u p : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    {p' : ℕ → ComplexModel n → ℝ} (hp' : ∀ j, IsSmoothPshOn Ω (p' j))
    (hpAnti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hpLim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    {v : Fin k → ComplexModel n → ℝ} (hv : ∀ i, IsLocallyBoundedPshOn Ω (v i))
    {v' : ℕ → Fin k → ComplexModel n → ℝ}
    (hv' : ∀ j i, IsSmoothPshOn Ω (v' j i))
    (hvAnti : ∀ i x, x ∈ Ω → Antitone (fun j => v' j i x))
    (hvLim : ∀ i x, x ∈ Ω → Tendsto (fun j => v' j i x) atTop (𝓝 (v i x)))
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (he : ∀ j, EqOn u (p' j) ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (a : CoordinateTuple n (k + 1) → ℂ) :
    (∫ x : Ω, χ x * u x ∂quadraticMeasure
        (mixedProduct_positive (locallyBoundedPsh_cons hp hv)) a) =
      ∫ x : Ω, χ x * p x ∂quadraticMeasure
        (mixedProduct_positive
          (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hv)) a := by
  let U := multiplySmoothTest χ hu.1
  let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)
  let μ := quadraticMeasure (mixedProduct_positive (locallyBoundedPsh_cons
    (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hv)) a
  let : μ.Regular := quadraticMeasure_regular (mixedProduct_positive (locallyBoundedPsh_cons
    (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hv)) a
  let μp (j : ℕ) := quadraticMeasure
    (mixedProduct_positive (locallyBoundedPsh_cons (hpL j) hv)) a
  let μlim := quadraticMeasure (mixedProduct_positive (locallyBoundedPsh_cons hp hv)) a
  change (∫ x : Ω, U x ∂μlim) = ∫ x : Ω, χ x * p x ∂μ
  have hEq (j : ℕ) : (∫ x : Ω, U x ∂μp j) = ∫ x : Ω, χ x * p' j x ∂μ := by
    let P := multiplySmoothTest χ (hp' j).1
    change (∫ x : Ω, U x ∂μp j) = ∫ x : Ω, P x ∂μ
    simp only [μ, μp, U, P, integral_quadraticMeasure, quadraticDistribution_apply]
    simp_rw [mixedProduct_swap_test_of_tail_approximation hu (hp' j) hv hv' hvAnti hvLim
      hK (he j) χ hχ]
  let t : Fin (k + 1) → ComplexModel n → ℝ := Fin.cons p v
  let ht := locallyBoundedPsh_cons hp hv
  have hweak := weakMatrixLimit_mixedProduct_update (u := t) ht (0 : Fin (k + 1))
    (fun i hi => (Fin.not_lt_zero i hi).elim) hpL hpAnti hpLim
  have hweak' : WeakMatrixLimit (fun j => mixedProduct (locallyBoundedPsh_cons (hpL j) hv))
      (mixedProduct ht) := by
    intro I J φ
    apply (hweak I J φ).congr
    intro j
    have heq : Function.update t 0 (p' j) =
        Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) (p' j) v :=
      Fin.update_cons_zero (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) p v (p' j)
    exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J φ)
      (mixedProduct_congr_tuple heq _ _)
  have hleft : Tendsto (fun j => ∫ x : Ω, U x ∂μp j) atTop (𝓝 (∫ x : Ω, U x ∂μlim)) :=
    hweak'.integral_quadraticMeasure (fun j => mixedProduct_positive
      (locallyBoundedPsh_cons (hpL j) hv)) (mixedProduct_positive ht) a U
  exact tendsto_nhds_unique hleft ((tendsto_integral_psh_weight_of_antitone hp hpL hpAnti hpLim μ χ).congr
    fun j => (hEq j).symm)

end KEBall.BedfordTaylor
