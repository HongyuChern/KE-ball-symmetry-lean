import KEBall.DirichletAngularGradient

/-! Distributional Hessian entries and the elliptic trace of the weak equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions Gradient

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- A Hessian entry tested against a smooth compactly supported scalar function. -/
noncomputable def dirichletHessianEntry {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (v w : E n) : ℝ :=
  -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v *
    inner ℝ w ((u : DirichletBallL2Pair n).snd x) ∂ν[n])

/-- The distributional Hessian of the scalar component is symmetric. -/
theorem dirichletHessianEntry_comm {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (v w : E n) :
    dirichletHessianEntry u ψ v w = dirichletHessianEntry u ψ w v := by
  let ψv := dirichletTestFieldDerivative ψ (fun _ => v) contDiff_const
  let ψw := dirichletTestFieldDerivative ψ (fun _ => w) contDiff_const
  have h (x : E n) : fderiv ℝ (ψv : E n → ℝ) x w = fderiv ℝ (ψw : E n → ℝ) x v := by
    have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
    change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y w) x v
    rw [fderiv_clm_apply hd (differentiableAt_const v),
      fderiv_clm_apply hd (differentiableAt_const w)]
    simpa using hs.eq w v
  unfold dirichletHessianEntry
  change -(∫ x, ψv x * inner ℝ w ((u : DirichletBallL2Pair n).snd x) ∂ν[n]) =
    -(∫ x, ψw x * inner ℝ v ((u : DirichletBallL2Pair n).snd x) ∂ν[n])
  rw [dirichletSobolev_integral_weakGradient u ψv w, dirichletSobolev_integral_weakGradient u ψw v]
  simp_rw [h]

/-- The weak Dirichlet identity on ordinary smooth compactly supported tests. -/
theorem IsDirichletWeakSolution.integral_fderiv_test {n : ℕ}
    {A : E n → E n →L[ℝ] E n} {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u) (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
      ∫ x, ψ x * g x ∂ν[n] := by
  let w : DirichletSobolev n := ⟨dirichletTestL2Graph n ψ,
    subset_closure (LinearMap.mem_range_self (dirichletTestL2Graph n) ψ)⟩
  have hLeft : (∫ x, inner ℝ (A x ((u : DirichletBallL2Pair n).snd x))
      ((w : DirichletBallL2Pair n).snd x) ∂ν[n]) =
      ∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [dirichletTestGradientToL2_ae ψ] with x hx
    change inner ℝ _ (dirichletTestGradientToL2 n ψ x) = _
    rw [hx, real_inner_comm, inner_gradient_left]
  have hRight : (∫ x, g x * ((w : DirichletBallL2Pair n).fst x) ∂ν[n]) =
      ∫ x, ψ x * g x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae ψ] with x hx
    change g x * dirichletTestToL2 ψ x = _
    rw [hx, mul_comm]
  exact hLeft.symm.trans ((hu w).trans hRight)

/-- The equation on compactly supported smooth tests extends to all Dirichlet graph tests. -/
theorem IsDirichletWeakSolution.of_test {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ν[n]) (g : DirichletBallL2 n ℝ) (u : DirichletSobolev n)
    (hTest : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
        ∫ x, ψ x * g x ∂ν[n]) :
    IsDirichletWeakSolution A g u := by
  let F := dirichletCoefficientAction hA (u : DirichletBallL2Pair n).snd
  let L : DirichletBallL2Pair n →L[ℝ] ℝ := (innerSL ℝ F).comp (WithLp.sndL 2 ℝ _ _)
  let R : DirichletBallL2Pair n →L[ℝ] ℝ := (innerSL ℝ g).comp (WithLp.fstL 2 ℝ _ _)
  let S : Set (DirichletBallL2Pair n) := {z | L z = R z}
  have hClosed : IsClosed S := isClosed_eq L.continuous R.continuous
  have hRange : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ S := by
    rintro _ ⟨ψ, rfl⟩
    change inner ℝ F (dirichletTestGradientToL2 n ψ) = inner ℝ g (dirichletTestToL2 ψ)
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine Eq.trans ?_ ((hTest ψ).trans ?_)
    · apply integral_congr_ae
      filter_upwards [dirichletCoefficientAction_ae hA (u : DirichletBallL2Pair n).snd,
        dirichletTestGradientToL2_ae ψ] with x hF hψ
      change F x = _ at hF
      rw [hF, hψ, real_inner_comm, inner_gradient_left]
    · apply integral_congr_ae
      filter_upwards [dirichletTestToL2_ae ψ] with x hx
      rw [hx, Real.inner_apply, mul_comm]
  intro w
  have h : inner ℝ F (w : DirichletBallL2Pair n).snd = inner ℝ g (w : DirichletBallL2Pair n).fst :=
    closure_minimal hRange hClosed w.property
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
  simp only [Real.inner_apply] at h
  refine Eq.trans ?_ h
  apply integral_congr_ae
  filter_upwards [dirichletCoefficientAction_ae hA (u : DirichletBallL2Pair n).snd] with x hx
  change F x = _ at hx
  rw [hx]

/-- Smooth matrix coefficient in the orthonormal frame used to test a Hessian. -/
theorem contDiff_dirichletCoefficientEntry {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (v w : E n) : ContDiff ℝ ∞ (fun x => inner ℝ w (A x v)) :=
  (innerSL ℝ w).contDiff.comp (hA.clm_apply contDiff_const)

/-- The divergence of one column of a coefficient field. -/
noncomputable def dirichletColumnDivergence {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (A : E n → E n →L[ℝ] E n)
    (v x : E n) : ℝ :=
  ∑ j, fderiv ℝ (fun y => inner ℝ (b j) (A y v)) x (b j)

/-- Contraction of the distributional Hessian with smooth matrix coefficients. -/
noncomputable def dirichletHessianTrace {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) : ℝ :=
  ∑ i, ∑ j, dirichletHessianEntry u
    (dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hA (b i) (b j))) (b j) (b i)

/-- Integration by parts expands the Hessian trace into the principal term
and the derivatives of the coefficient columns. -/
theorem dirichletHessianTrace_eq_neg_integral {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (u : DirichletSobolev n) (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletHessianTrace b u ψ hA =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) -
        ∫ x, ψ x * (∑ i, dirichletColumnDivergence b A (b i) x *
          inner ℝ (b i) ((u : DirichletBallL2Pair n).snd x)) ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let F (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (U x)
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (A x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) := contDiff_dirichletCoefficientEntry hA _ _
  let Dc (i j : Fin (2 * n)) (x : E n) := fderiv ℝ (c i j) x (b j)
  have hDc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (Dc i j) :=
    ((hc i j).fderiv_right (by simp)).clm_apply contDiff_const
  let ψj (j : Fin (2 * n)) := dirichletTestFieldDerivative ψ (fun _ => b j) contDiff_const
  let D (i j : Fin (2 * n)) :=
    dirichletTestFieldDerivative (dirichletTestMul ψ (hc i j)) (fun _ => b j) contDiff_const
  have hInt (i : Fin (2 * n)) (φ : 𝓓(dirichletBallOpens n, ℝ)) :
      Integrable (fun x => φ x * F i x) ν[n] := by
    have hF : Integrable (F i) ν[n] := ((Lp.memLp U).const_inner (b i)).integrable (by norm_num)
    exact φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (hF.locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hProduct (i j : Fin (2 * n)) (x : E n) :
      D i j x = ψj j x * c i j x + ψ x * Dc i j x := by
    change fderiv ℝ (fun y => ψ y * c i j y) x (b j) =
      fderiv ℝ (ψ : E n → ℝ) x (b j) * c i j x + ψ x * fderiv ℝ (c i j) x (b j)
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) ((hc i j).differentiable (by simp) x)]
    simp [mul_comm, add_comm]
  have hPrinc (x : E n) :
      (∑ i, ∑ j, (ψj j x * c i j x) * F i x) = fderiv ℝ (ψ : E n → ℝ) x (A x (U x)) := by
    have hInner (i : Fin (2 * n)) :
        (∑ j, ψj j x * c i j x) = fderiv ℝ (ψ : E n → ℝ) x (A x (b i)) := by
      calc
        _ = fderiv ℝ (ψ : E n → ℝ) x (∑ j, c i j x • b j) := by
          simp only [map_sum, map_smul, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ = _ := congrArg (fderiv ℝ (ψ : E n → ℝ) x) (b.sum_repr' (A x (b i)))
    simp_rw [← Finset.sum_mul, hInner]
    calc
      _ = fderiv ℝ (ψ : E n → ℝ) x (A x (∑ i, F i x • b i)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = _ := congrArg (fun v => fderiv ℝ (ψ : E n → ℝ) x (A x v)) (b.sum_repr' (U x))
  have hDiv (x : E n) :
      (∑ i, ∑ j, (ψ x * Dc i j x) * F i x) =
        ψ x * ∑ i, dirichletColumnDivergence b A (b i) x * F i x := by
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, dirichletColumnDivergence, Dc, c]
  have hPrincI : Integrable (fun x => fderiv ℝ (ψ : E n → ℝ) x (A x (U x))) ν[n] := by
    refine (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
      hInt i (dirichletTestMul (ψj j) (hc i j))).congr ?_
    exact Eventually.of_forall hPrinc
  have hDivI : Integrable (fun x => ψ x *
      ∑ i, dirichletColumnDivergence b A (b i) x * F i x) ν[n] := by
    refine (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
      hInt i (dirichletTestMul ψ (hDc i j))).congr ?_
    exact Eventually.of_forall hDiv
  change (∑ i, ∑ j, -(∫ x, D i j x * F i x ∂ν[n])) =
    -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x (U x)) ∂ν[n]) -
      ∫ x, ψ x * (∑ i, dirichletColumnDivergence b A (b i) x * F i x) ∂ν[n]
  simp_rw [Finset.sum_neg_distrib]
  rw [sub_eq_add_neg, ← neg_add, ← integral_add hPrincI hDivI]
  congr 1
  have hSumI (i : Fin (2 * n)) : Integrable (fun x => ∑ j, D i j x * F i x) ν[n] :=
    integrable_finsetSum Finset.univ fun j _ => hInt i (D i j)
  simp_rw [← integral_finsetSum _ (fun j _ => hInt _ (D _ j))]
  rw [← integral_finsetSum _ (fun i _ => hSumI i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ i, ∑ j, D i j x * F i x) = _
    simp_rw [hProduct, add_mul, Finset.sum_add_distrib]
    rw [hPrinc, hDiv]

/-- The weak equation identifies the tested Hessian trace as the negative
right-hand side minus the divergence correction of the coefficient columns. -/
theorem IsDirichletWeakSolution.dirichletHessianTrace_eq_integral {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u) (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletHessianTrace b u ψ hA = -(∫ x, ψ x * g x ∂ν[n]) -
      ∫ x, ψ x * (∑ i, dirichletColumnDivergence b A (b i) x *
        inner ℝ (b i) ((u : DirichletBallL2Pair n).snd x)) ∂ν[n] := by
  rw [dirichletHessianTrace_eq_neg_integral hn b hA u ψ, hu.integral_fderiv_test ψ]

/-- A distributional Hessian entry is additive in its test function. -/
theorem dirichletHessianEntry_add {n : ℕ} (hn : 0 < n) (u : DirichletSobolev n)
    (ψ χ : 𝓓(dirichletBallOpens n, ℝ)) (v w : E n) :
    dirichletHessianEntry u (ψ + χ) v w =
      dirichletHessianEntry u ψ v w + dirichletHessianEntry u χ v w := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let f (x : E n) := inner ℝ w ((u : DirichletBallL2Pair n).snd x)
  have hf : Integrable f ν[n] :=
    ((Lp.memLp (u : DirichletBallL2Pair n).snd).const_inner w).integrable (by norm_num)
  have hInt (φ : 𝓓(dirichletBallOpens n, ℝ)) :
      Integrable (fun x => fderiv ℝ (φ : E n → ℝ) x v * f x) ν[n] :=
    (dirichletTestFieldDerivative φ (fun _ => v) contDiff_const).integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ) (hf.locallyIntegrable.locallyIntegrableOn (unitBall n))
  unfold dirichletHessianEntry
  change -(∫ x, fderiv ℝ (fun y => ψ y + χ y) x v * f x ∂ν[n]) =
    -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * f x ∂ν[n]) +
    -(∫ x, fderiv ℝ (χ : E n → ℝ) x v * f x ∂ν[n])
  rw [← neg_add, ← integral_add (hInt ψ) (hInt χ)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change fderiv ℝ (fun y => ψ y + χ y) x v * f x =
      fderiv ℝ (ψ : E n → ℝ) x v * f x + fderiv ℝ (χ : E n → ℝ) x v * f x
    rw [fderiv_fun_add (ψ.contDiff.differentiable (by simp) x)
      (χ.contDiff.differentiable (by simp) x), add_apply, add_mul]

/-- The tested Hessian contraction is additive in the smooth coefficients. -/
theorem dirichletHessianTrace_add {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A B : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    dirichletHessianTrace b u ψ (hA.add hB) =
      dirichletHessianTrace b u ψ hA + dirichletHessianTrace b u ψ hB := by
  unfold dirichletHessianTrace
  simp_rw [← Finset.sum_add_distrib, ← dirichletHessianEntry_add hn]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply TestFunction.ext
  intro x
  simp [add_apply, inner_add_right, mul_add]

/-- A smooth scalar factor can be moved from the coefficients to the test. -/
theorem dirichletHessianTrace_smul {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : E n → E n →L[ℝ] E n} {m : E n → ℝ}
    (hA : ContDiff ℝ ∞ A) (hm : ContDiff ℝ ∞ m) :
    dirichletHessianTrace b u ψ (hm.smul hA) =
      dirichletHessianTrace b u (dirichletTestMul ψ hm) hA := by
  unfold dirichletHessianTrace
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply TestFunction.ext
  intro x
  simp [real_inner_smul_right, mul_assoc]

/-- Symmetry of the distributional Hessian allows transposing the coefficients. -/
theorem dirichletHessianTrace_adjoint {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hAdj : ContDiff ℝ ∞ (fun x => (A x).adjoint)) :
    dirichletHessianTrace b u ψ hAdj = dirichletHessianTrace b u ψ hA := by
  unfold dirichletHessianTrace
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [dirichletHessianEntry_comm u _ (b j) (b i)]
  congr 1
  apply TestFunction.ext
  intro x
  simp only [dirichletTestMul_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

theorem dirichletHessianTrace_congr {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A B : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (he : A = B) :
    dirichletHessianTrace b u ψ hA = dirichletHessianTrace b u ψ hB := by
  subst B
  rfl

/-- The tested Hessian contraction commutes with finite sums of coefficients. -/
theorem dirichletHessianTrace_sum {n : ℕ} {ι : Type*} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : ι → E n → E n →L[ℝ] E n}
    (hA : ∀ i, ContDiff ℝ ∞ (A i)) (s : Finset ι) :
    dirichletHessianTrace b u ψ (ContDiff.sum fun i (_ : i ∈ s) => hA i) =
      ∑ i ∈ s, dirichletHessianTrace b u ψ (hA i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hZ : (fun x => ∑ i ∈ (∅ : Finset ι), A i x) =
        (fun _ : E n => (0 : E n →L[ℝ] E n)) := by
      funext x
      simp
    rw [dirichletHessianTrace_congr b u ψ _ contDiff_const hZ, Finset.sum_empty]
    unfold dirichletHessianTrace
    have hz (i j : Fin (2 * n)) :
        dirichletTestMul ψ (contDiff_dirichletCoefficientEntry
          (contDiff_const : ContDiff ℝ ∞ (fun _ : E n => (0 : E n →L[ℝ] E n)))
          (b i) (b j)) = 0 := by
      apply TestFunction.ext
      intro x
      simp
    simp_rw [hz, dirichletHessianEntry]
    simp
  | insert a s ha ih =>
    have hEq : (fun x => ∑ i ∈ insert a s, A i x) = (A a + fun x => ∑ i ∈ s, A i x) := by
      funext x
      simp [Finset.sum_insert ha]
    have hs : ContDiff ℝ ∞ (fun x => ∑ i ∈ s, A i x) :=
      ContDiff.sum fun i (_ : i ∈ s) => hA i
    rw [dirichletHessianTrace_congr b u ψ _ ((hA a).add hs) hEq,
      dirichletHessianTrace_add hn b u ψ (hA a) hs, ih, Finset.sum_insert ha]

end KEBall
