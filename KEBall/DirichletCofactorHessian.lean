import KEBall.DirichletWeakLinearization
import KEBall.DirichletGlobalWeakFourthDerivative
import KEBall.DirichletRegularity
import KEBall.BallGreenLocal
import KEBall.FiberEnergyGreen

/-! The real coefficient field of the Monge–Ampère linearization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions NNReal

namespace KEBall

theorem dirichletCofactorOperator_contDiffOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (dirichletCofactorOperator u) U := by
  let R := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hH := hermitianRealification_contDiffOn
    (matrixField_adjugate_contDiffOn (complexHessian_contDiffOn hU hu))
  exact (contDiffOn_const (c := (8 : ℝ)⁻¹)).smul ((contDiffOn_const (c := R)).clm_comp hH)

theorem dirichletCofactorOperator_adjoint_eq {n : ℕ} {u : E n → ℝ} {x : E n}
    (hH : (complexHessian u x).IsHermitian) :
    (dirichletCofactorOperator u x).adjoint = dirichletCofactorOperator u x := by
  ext v : 1
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = inner ℝ (dirichletCofactorOperator u x w) v := real_inner_comm _ _
    _ = _ := by rw [dirichletCofactorOperator_inner, dirichletCofactorOperator_inner,
      hermitianRealification_symm hH.adjugate w v]

private theorem contDiff_euclideanAdjoint {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (fun x => (A x).adjoint) := by
  let T : (E n →L[ℝ] E n) ≃ₗᵢ[ℝ] (E n →L[ℝ] E n) := ContinuousLinearMap.adjoint
  exact T.toContinuousLinearEquiv.contDiff.comp hA

/-- Extend the actual cofactor operator by a smooth compactly supported
self-adjoint field that agrees on the closed ball. -/
theorem exists_smooth_selfAdjoint_dirichletCofactorExtension {n : ℕ}
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) :
    ∃ A : E n → E n →L[ℝ] E n, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      (∀ x, (A x).adjoint = A x) ∧ ∀ x ∈ closedUnitBall n, A x = dirichletCofactorOperator u x := by
  obtain ⟨U, hU, hSub, hu⟩ := hu
  obtain ⟨W, hWS, hWC, hEq⟩ := exists_contDiff_extension_closedUnitBall ⊤ hU hSub
    (dirichletCofactorOperator_contDiffOn hU hu)
  let B (x : E n) := (2 : ℝ)⁻¹ • (W x + (W x).adjoint)
  have hB : ContDiff ℝ ∞ B := (contDiff_const (c := (2 : ℝ)⁻¹)).smul (hWC.add (contDiff_euclideanAdjoint hWC))
  have hBS : HasCompactSupport B := by
    apply hWS.mono'
    intro x hx
    by_contra h
    apply hx
    have hz : W x = 0 := image_eq_zero_of_notMem_tsupport h
    simp [B, hz]
  refine ⟨B, hB, hBS, ?_, ?_⟩
  · intro x
    change ((2 : ℝ)⁻¹ • (W x + (W x).adjoint)).adjoint = _
    simp [B, add_comm]
  · intro x hx
    have hxH := MoserTrudinger.complexHessian_isHermitian_of_smooth
      (hu.contDiffAt (hU.mem_nhds (hSub hx)))
    have hWx := (hEq x hx).eq_of_nhds
    change (2 : ℝ)⁻¹ • (W x + (W x).adjoint) = dirichletCofactorOperator u x
    rw [hWx, dirichletCofactorOperator_adjoint_eq hxH, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- A smooth bounded coefficient extension of the actual cofactor operator
with the ellipticity bounds used by the global Dirichlet estimates. -/
private theorem exists_weakCofactorDirichletSolution_with_extension {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) :
    ∃ (w : DirichletSobolev n) (A : E n → E n →L[ℝ] E n) (K : ℝ≥0) (M : ℝ),
      IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      IsDirichletWeakSolution A g w ∧ ContDiff ℝ ∞ A ∧
      MemLp A ⊤ ((volume0 n).restrict (unitBall n)) ∧
      (∀ x, (A x).adjoint = A x) ∧
      (∀ x ∈ unitBall n, ∀ v : E n, (a * l) * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) ∧
      LipschitzOnWith K A (closedUnitBall n) ∧ 0 ≤ M ∧
      ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M := by
  obtain ⟨w, hw⟩ :=
    (existsUnique_weakCofactorDirichletSolution hn hu huP ha hl hDensity hElliptic g).exists
  obtain ⟨A, hA, hAS, hSym, hEq⟩ := exists_smooth_selfAdjoint_dirichletCofactorExtension hu
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hA hAS
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hA.continuous.continuousOn
  have hM₀ : 0 ≤ M := (norm_nonneg (A 0)).trans (hM 0 (by simp))
  have hLp : MemLp A ⊤ ((volume0 n).restrict (unitBall n)) :=
    hA.continuous.memLp_top_of_hasCompactSupport hAS _
  have hwA : IsDirichletWeakSolution A g w := by
    intro v
    refine Eq.trans ?_ (hw v)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    rw [hEq x (ball_subset_closedBall hx)]
  have hCoer (x : E n) (hx : x ∈ unitBall n) (v : E n) : (a * l) * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v := by
    rw [hEq x (ball_subset_closedBall hx), dirichletCofactorOperator_inner_self (huP x hx)]
    calc
      (a * l) * ‖v‖ ^ 2 = a * (l * ‖v‖ ^ 2) := by ring
      _ ≤ (complexHessian u x).det.re * (l * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hDensity x hx) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hElliptic x hx v) (posDef_det_re_pos (huP x hx)).le
  exact ⟨w, A, K, M, hw, hwA, hA, hLp, hSym, hCoer, hLip.lipschitzOnWith, hM₀, hM⟩

/-- The actual determinant linearization has a weak Dirichlet solution
whose real Hessian entries are square integrable on the whole ball. -/
theorem exists_weakCofactorDirichletSolution_with_L2Hessian {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) :
    ∃ w : DirichletSobolev n, IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      ∀ (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (i j : Fin (2 * n)),
        ∃ F : E n → ℝ, MemLp F 2 ((volume0 n).restrict (unitBall n)) ∧
          ∀ ψ : 𝓓(dirichletBallOpens n, ℝ), dirichletHessianEntry w ψ (b j) (b i) =
            ∫ x in unitBall n, ψ x * F x ∂volume0 n := by
  obtain ⟨w, _, _, _, hw, hwA, hA, hLp, hSym, hCoer, hLip, hM₀, hM⟩ :=
    exists_weakCofactorDirichletSolution_with_extension hn hu huP ha hl hDensity hElliptic g
  exact ⟨w, hw, fun b i j => exists_dirichletHessianEntryL2 hn b hLp hA hSym
    (mul_pos ha hl) hCoer hLip hM₀ hM hwA i j⟩

/-- For forcing with an L² weak gradient, the actual cofactor Dirichlet solution has
square-integrable third weak derivatives on the entire ball. -/
theorem exists_weakCofactorDirichletSolution_with_L2ThirdDerivative_of_weakGradient {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) (hg : HasDirichletWeakGradientL2 (g : E n → ℝ)) :
    ∃ w : DirichletSobolev n, IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      ∀ i j k : Fin (2 * n), let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
        ∃ F : E n → ℝ, MemLp F 2 ((volume0 n).restrict (unitBall n)) ∧
          ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
            dirichletThirdDerivativeEntry w ψ (b k) (b j) (b i) =
              ∫ x in unitBall n, ψ x * F x ∂volume0 n := by
  obtain ⟨w, _, _, _, hw, hwA, hA, hLp, hSym, hCoer, hLip, hM₀, hM⟩ :=
    exists_weakCofactorDirichletSolution_with_extension hn hu huP ha hl hDensity hElliptic g
  exact ⟨w, hw, fun i j k => hwA.exists_dirichletThirdDerivativeEntryL2_of_weakGradient hn hLp hA hSym
    (mul_pos ha hl) hCoer hLip hM₀ hM hg i j k⟩

private theorem exists_smooth_dirichletForcingRepresentative {n : ℕ}
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G)
    (hRep : g =ᵐ[(volume0 n).restrict (unitBall n)] G) :
    ∃ G' : E n → ℝ, ContDiff ℝ ∞ G' ∧ g =ᵐ[(volume0 n).restrict (unitBall n)] G' := by
  obtain ⟨U, hU, hSub, hGc⟩ := hG
  obtain ⟨G', _, hG'c, hAgree⟩ := exists_contDiff_extension_closedUnitBall ⊤ hU hSub hGc
  have hRep' : g =ᵐ[(volume0 n).restrict (unitBall n)] G' := by
    filter_upwards [hRep, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hxb
    exact hx.trans (hAgree x (ball_subset_closedBall hxb)).eq_of_nhds.symm
  exact ⟨G', hG'c, hRep'⟩

/-- The weak solution of the actual cofactor equation gains two orders of
square-integrable weak derivatives on the whole ball. -/
theorem exists_weakCofactorDirichletSolution_with_weakDerivatives {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (k : ℕ) (g : DirichletBallL2 n ℝ) (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k) :
    ∃ w : DirichletSobolev n, IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      HasDirichletWeakDerivativesL2 ((w : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2) := by
  obtain ⟨w, _, _, _, hw, hwA, hA, hLp, hSym, hCoer, hLip, hM₀, hM⟩ :=
    exists_weakCofactorDirichletSolution_with_extension hn hu huP ha hl hDensity hElliptic g
  exact ⟨w, hw, hwA.hasDirichletWeakDerivativesL2 hn (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
    hLp hA hSym (mul_pos ha hl) hCoer hLip hM₀ hM k hg⟩

/-- A single weak solution of the actual cofactor equation with smooth
forcing has square-integrable weak derivatives of every finite order. -/
theorem exists_weakCofactorDirichletSolution_with_allWeakDerivatives {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G)
    (hRep : g =ᵐ[(volume0 n).restrict (unitBall n)] G) :
    ∃ w : DirichletSobolev n, IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      ∀ k, HasDirichletWeakDerivativesL2 ((w : DirichletBallL2Pair n).fst : E n → ℝ) k := by
  obtain ⟨G', hG'c, hRep'⟩ := exists_smooth_dirichletForcingRepresentative g hG hRep
  obtain ⟨w, _, _, _, hw, hwA, hA, hLp, hSym, hCoer, hLip, hM₀, hM⟩ :=
    exists_weakCofactorDirichletSolution_with_extension hn hu huP ha hl hDensity hElliptic g
  refine ⟨w, hw, fun k => ?_⟩
  have hg := (HasDirichletWeakDerivativesL2.of_smooth hn hG'c k).congr hRep'.symm
  have hW := hwA.hasDirichletWeakDerivativesL2 hn (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
    hLp hA hSym (mul_pos ha hl) hCoer hLip hM₀ hM k hg
  exact ⟨hW.1, fun ds hds => hW.2 ds (hds.trans (Nat.le_add_right k 2))⟩

/-- For smooth forcing, the actual cofactor Dirichlet solution has
square-integrable third weak derivatives on the entire ball. -/
theorem exists_weakCofactorDirichletSolution_with_L2ThirdDerivative {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G)
    (hRep : g =ᵐ[(volume0 n).restrict (unitBall n)] G) :
    ∃ w : DirichletSobolev n, IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      ∀ i j k : Fin (2 * n), let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
        ∃ F : E n → ℝ, MemLp F 2 ((volume0 n).restrict (unitBall n)) ∧
          ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
            dirichletThirdDerivativeEntry w ψ (b k) (b j) (b i) =
              ∫ x in unitBall n, ψ x * F x ∂volume0 n := by
  obtain ⟨G', hG'c, hRep'⟩ := exists_smooth_dirichletForcingRepresentative g hG hRep
  exact exists_weakCofactorDirichletSolution_with_L2ThirdDerivative_of_weakGradient
    hn hu huP ha hl hDensity hElliptic g (HasDirichletWeakGradientL2.of_smooth_ae hn hG'c hRep')

/-- For smooth forcing, the actual cofactor Dirichlet solution has
square-integrable fourth weak derivatives on the entire ball. -/
theorem exists_weakCofactorDirichletSolution_with_L2FourthDerivative {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G)
    (hRep : g =ᵐ[(volume0 n).restrict (unitBall n)] G) :
    ∃ w : DirichletSobolev n, IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      ∀ i j k m : Fin (2 * n), let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
        ∃ F : E n → ℝ, MemLp F 2 ((volume0 n).restrict (unitBall n)) ∧
          ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
            dirichletFourthDerivativeEntry w ψ (b m) (b k) (b j) (b i) =
              ∫ x in unitBall n, ψ x * F x ∂volume0 n := by
  obtain ⟨G', hG'c, hRep'⟩ := exists_smooth_dirichletForcingRepresentative g hG hRep
  obtain ⟨w, _, _, _, hw, hwA, hA, hLp, hSym, hCoer, hLip, hM₀, hM⟩ :=
    exists_weakCofactorDirichletSolution_with_extension hn hu huP ha hl hDensity hElliptic g
  exact ⟨w, hw, fun i j k m => hwA.exists_dirichletFourthDerivativeEntryL2 hn hLp hA hSym
    (mul_pos ha hl) hCoer hLip hM₀ hM hG'c hRep' i j k m⟩

end KEBall
