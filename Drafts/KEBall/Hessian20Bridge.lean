import Drafts.KEBall.ConnectionComplex
import KEBall.Specification

/-!
# The paper's coordinate (2,0) Hessian is the actual covariant Hessian

Stage02 source draft, not kernel checked. The symbols in Specification
are preserved unchanged. We first compute the complex Christoffel coefficients
of the actual retained connection, then substitute them in its Hessian.
The inverse transpose is derived by matrix multiplication, not assumed.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall
open KEBallProbe

/-- The (2,0) component of a real bilinear expression in the fixed coordinates.
For a covariant tensor A this is A((e_i-iJe_i)/2,(e_j-iJe_j)/2). -/
noncomputable def complexify20 {n : ℕ} (A : E n → E n → ℝ)
    (i j : Fin n) : ℂ :=
  (4 : ℂ)⁻¹ *
    ((A (realDirection i) (realDirection j) : ℂ) -
     (A (imagDirection i) (imagDirection j) : ℂ) -
     Complex.I * ((A (realDirection i) (imagDirection j) : ℂ) +
       (A (imagDirection i) (realDirection j) : ℂ)))

/-- The ordinary pure Wirtinger second derivative has exactly the 1/4 factor. -/
theorem partialZ_partialZ_eq_complexify20 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    partialZ i (partialZ j (fun y => (u y : ℂ))) x =
      complexify20 (fun v w => realHessian u x v w) i j := by
  have hc : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (imagDirection j) (fun y => (u y : ℂ))) x = _
  rw [dz, rd_dz_at hc, rd_dz_at hc]
  simp only [rd_rd_ofReal hu, complexify20]
  push_cast
  ring_nf
  simp
  ring

private theorem rd_add_at {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f h : X → ℂ} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (hh : ContDiffAt ℝ ∞ h x) (a : X) :
    rd a (fun y => f y + h y) x = rd a f x + rd a h x := by
  simp [rd, fderiv_fun_add (hf.differentiableAt (by simp))
    (hh.differentiableAt (by simp))]

/-- Differentiating the real Hessian as a complex-valued scalar uses the
actual third Frechet derivative. -/
theorem rd_realHessian_ofReal {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (a v w : E n) :
    rd a (fun y => (realHessian u y v w : ℂ)) x =
      (realThirdDerivative u x a v w : ℂ) := by
  have hs := ((realHessian_contDiffAt hu).clm_apply (contDiffAt_const (c := v))).clm_apply
    (contDiffAt_const (c := w))
  rw [rd_ofReal (hs.differentiableAt (by simp)), fderiv_realHessian_apply hu]

/-- The real directional derivative of an actual complex Hessian entry. -/
theorem rd_complexHessian_eq_third {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (a : E n) (j l : Fin n) :
    rd a (fun y => complexHessian u y j l) x =
      (4 : ℂ)⁻¹ *
        ((realThirdDerivative u x a (realDirection j) (realDirection l) : ℂ) +
         (realThirdDerivative u x a (imagDirection j) (imagDirection l) : ℂ) +
         Complex.I *
           ((realThirdDerivative u x a (realDirection j) (imagDirection l) : ℂ) -
            (realThirdDerivative u x a (imagDirection j) (realDirection l) : ℂ))) := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hs (v w : E n) : ContDiffAt ℝ ∞
      (fun y => (realHessian u y v w : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (((realHessian_contDiffAt huAt).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const)
  have heq : (fun y => complexHessian u y j l) =ᶠ[𝓝 x]
      (fun y => (4 : ℂ)⁻¹ *
        ((realHessian u y (realDirection j) (realDirection l) : ℂ) +
         (realHessian u y (imagDirection j) (imagDirection l) : ℂ) +
         Complex.I *
           ((realHessian u y (realDirection j) (imagDirection l) : ℂ) -
            (realHessian u y (imagDirection j) (realDirection l) : ℂ)))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact complexHessian_real_entry (hu.contDiffAt (hU.mem_nhds hy)) j l
  change fderiv ℝ (fun y => complexHessian u y j l) x a = _
  rw [heq.fderiv_eq]
  change rd a _ x = _
  rw [rd_const_mul_at
      (((hs _ _).add (hs _ _)).add (contDiffAt_const.mul ((hs _ _).sub (hs _ _)))),
    rd_add_at ((hs _ _).add (hs _ _))
      (contDiffAt_const.mul ((hs _ _).sub (hs _ _))),
    rd_add_at (hs _ _) (hs _ _),
    rd_const_mul_at ((hs _ _).sub (hs _ _)),
    rd_sub_at (hs _ _) (hs _ _)]
  simp only [rd_realHessian_ofReal huAt]

/-- The eight real third-jet terms in the holomorphic metric derivative. -/
theorem partialZ_complexHessian_eq_third {n : ℕ} {u : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    {x : E n} (hx : x ∈ U) (i j l : Fin n) :
    partialZ i (fun y => complexHessian u y j l) x =
      (8 : ℂ)⁻¹ *
        ((realThirdDerivative u x (realDirection i) (realDirection j)
            (realDirection l) : ℂ) +
         (realThirdDerivative u x (realDirection i) (imagDirection j)
            (imagDirection l) : ℂ) +
         (realThirdDerivative u x (imagDirection i) (realDirection j)
            (imagDirection l) : ℂ) -
         (realThirdDerivative u x (imagDirection i) (imagDirection j)
            (realDirection l) : ℂ) +
         Complex.I *
          ((realThirdDerivative u x (realDirection i) (realDirection j)
              (imagDirection l) : ℂ) -
           (realThirdDerivative u x (realDirection i) (imagDirection j)
              (realDirection l) : ℂ) -
           (realThirdDerivative u x (imagDirection i) (realDirection j)
              (realDirection l) : ℂ) -
           (realThirdDerivative u x (imagDirection i) (imagDirection j)
              (imagDirection l) : ℂ))) := by
  change (2 : ℂ)⁻¹ *
    (rd (realDirection i) (fun y => complexHessian u y j l) x -
     Complex.I * rd (imagDirection i) (fun y => complexHessian u y j l) x) = _
  rw [rd_complexHessian_eq_third hU hu hx, rd_complexHessian_eq_third hU hu hx]
  ring_nf
  simp
  ring

/-- The actual connection satisfies g^T Gamma = partial_i(g_{j,*}). -/
theorem connection_const_complex_row {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (i j l : Fin n) :
    (∑ k : Fin n, complexHessian u x k l *
      complexCoord (D.connection (fun _ : E n => realDirection j) x
        (realDirection i)) k) =
      partialZ i (fun y => complexHessian u y j l) x := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hr := inner_connection_const_eq_third D hU hu hg hx
    (realDirection i) (realDirection j) (realDirection l)
  have hi := inner_connection_const_eq_third D hU hu hg hx
    (realDirection i) (realDirection j) (imagDirection l)
  rw [hg x hx, realMetricForm_eq, hermitianRealification_realDirection] at hr
  rw [hg x hx, realMetricForm_eq, hermitianRealification_imagDirection] at hi
  rw [partialZ_complexHessian_eq_third hU hu hx]
  simp only [J_realDirection_eq_imag, J_imagDirection_eq_neg,
    map_neg, neg_apply] at hr hi
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    simp only [realThirdDerivative_symm12 huAt,
      realThirdDerivative_symm23 hU hu hx] at hr ⊢
    simp only [Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib] at hr ⊢
    linarith
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    simp only [realThirdDerivative_symm12 huAt,
      realThirdDerivative_symm23 hU hu hx] at hi ⊢
    simp only [Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib] at hi ⊢
    linarith

/-- No index convention is guessed: the transpose follows by solving the row
identity with the inverse of the concrete complex Hessian. -/
theorem connection_const_complex_coordinates {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hdet : IsUnit (complexHessian u x).det)
    (i j k : Fin n) :
    complexCoord (D.connection (fun _ : E n => realDirection j) x
        (realDirection i)) k =
      ∑ l : Fin n, inverseCoefficient u x k l *
        partialZ i (fun y => complexHessian u y j l) x := by
  let A := complexHessian u x
  let c := complexCoord
    (D.connection (fun _ : E n => realDirection j) x (realDirection i))
  let b : Fin n → ℂ := fun l => partialZ i (fun y => complexHessian u y j l) x
  have hrow : A.transpose.mulVec c = b := by
    funext l
    exact connection_const_complex_row D hU hu hg hx i j l
  have hc : c = A⁻¹.transpose.mulVec b := by
    have h := congrArg (A⁻¹.transpose.mulVec) hrow
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv A hdet, Matrix.transpose_one, Matrix.one_mulVec] at h
    exact h
  have h := congrFun hc k
  simpa only [A, c, b, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, inverseCoefficient] using h

/-- The complex-linear part of du evaluated on a real vector. -/
theorem wirtinger_covector_apply {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (v : E n) :
    (∑ k : Fin n, partialZ k (fun y => (u y : ℂ)) x * complexCoord v k) =
      (2 : ℂ)⁻¹ * ((fderiv ℝ u x v : ℂ) -
        Complex.I * (fderiv ℝ u x (J v) : ℂ)) := by
  have hr := fderiv_eq_wirtinger hu v
  have hi := fderiv_eq_wirtinger hu (J v)
  have hj : (∑ k : Fin n,
      partialZ k (fun y => (u y : ℂ)) x * complexCoord (J v) k) =
      Complex.I * (∑ k : Fin n,
        partialZ k (fun y => (u y : ℂ)) x * complexCoord v k) := by
    simp only [complexCoord_J, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hj] at hi
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_sub] at hi
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · simp only [Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib] at hr ⊢
    linarith
  · simp only [Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib] at hi ⊢
    linarith

/-- The connection correction in the complexified Hessian is du^{1,0}(Gamma). -/
theorem hessian_complexify20_eq_second_sub_connection {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (i j : Fin n) :
    complexify20 (D.hessian u x) i j =
      partialZ i (partialZ j (fun y => (u y : ℂ))) x -
        ∑ k : Fin n, partialZ k (fun y => (u y : ℂ)) x *
          complexCoord (D.connection (fun _ : E n => realDirection j) x
            (realDirection i)) k := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  let C := D.connection (fun _ : E n => realDirection j) x (realDirection i)
  have hri : D.connection (fun _ : E n => imagDirection j) x (realDirection i) =
      J C := by
    rw [← J_realDirection_eq_imag, connection_const_J_right D hU hu hg hx]
  have hir : D.connection (fun _ : E n => realDirection j) x (imagDirection i) =
      J C := by
    rw [← J_realDirection_eq_imag, connection_const_J_left D hU hu hg hx]
  have hii : D.connection (fun _ : E n => imagDirection j) x (imagDirection i) =
      -C := by
    rw [← J_realDirection_eq_imag, connection_const_J_right D hU hu hg hx, hir,
      J_sq]
  rw [partialZ_partialZ_eq_complexify20 huAt,
    wirtinger_covector_apply (huAt.differentiableAt (by simp))]
  simp only [complexify20, hessian_eq_realHessian_sub_connection D huAt,
    hri, hir, hii, map_neg]
  dsimp only [C]
  push_cast
  ring

/-- The unchanged covariantHessian20 of the frozen Specification is exactly
the (2,0) part of the retained actual Levi-Civita Hessian. -/
theorem covariantHessian20_eq_hessian_complexification {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hdet : IsUnit (complexHessian u x).det)
    (i j : Fin n) :
    covariantHessian20 u x i j = complexify20 (D.hessian u x) i j := by
  rw [hessian_complexify20_eq_second_sub_connection D hU hu hg hx]
  unfold covariantHessian20
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [connection_const_complex_coordinates D hU hu hg hx hdet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The original solution constructs a single metric and connection for both
the complex-structure compatibility and the exact paper Hessian. -/
theorem IsSolution.exists_local_hessian20_bridge {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ Y : E n → E n, DifferentiableAt ℝ Y x →
        ∀ v : E n, D.connection (fun y => J (Y y)) x v =
          J (D.connection Y x v)) ∧
      (∀ x ∈ V, ∀ i j : Fin n,
        covariantHessian20 u x i j = complexify20 (D.hessian u x) i j) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg⟩ := hu.exists_local_metric hp
  have huV := hu.contDiffOn_ball.mono hVB
  refine ⟨g, D, V, hV, hpV, hVB, hg, ?_, ?_⟩
  · intro x hx Y hY v
    exact connection_J_field D hV huV hg hx hY v
  · intro x hx i j
    exact covariantHessian20_eq_hessian_complexification D hV huV hg hx
      (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx))) i j

end KEBall
