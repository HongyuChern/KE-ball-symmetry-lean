import Drafts.KEBall.ConnectionTrace

/-!
# Coordinates and first derivatives of the actual connection

Stage04 DRAFT: not elaborated in this environment. The connection coefficient
is defined from D.connection, not from a prescribed Christoffel formula.
All neighbourhood statements use the inherited open-set smoothness model.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall
open KEBallProbe

/-- Real directional differentiation of a COMPLEX-valued function. This is
an algebraic identity for its actual real Frechet derivative, even when that
derivative is totalized at a nondifferentiability point. -/
theorem rd_eq_full_wirtinger {n : ℕ} (f : E n → ℂ) (x v : E n) :
    rd v f x = ∑ i : Fin n,
      (partialZ i f x * complexCoord v i +
        partialBar i f x * star (complexCoord v i)) := by
  calc
    _ = ∑ i : Fin n, ((v (realIndex i) : ℂ) * rd (realDirection i) f x +
        (v (imagIndex i) : ℂ) * rd (imagDirection i) f x) := by
      change fderiv ℝ f x v = _
      nth_rw 1 [← interleaved_decomposition v]
      simp only [map_sum, map_add, map_smul, rd, Complex.real_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [partialZ, partialBar, dz, rd, map_neg]
      simp [complexCoord, Complex.star_def] <;> ring_nf <;> simp [Complex.I_sq]

/-- Local equality of scalar functions suffices for both Wirtinger operators. -/
theorem partialBar_congr_nhds {n : ℕ} {f h : E n → ℂ} {x : E n}
    (heq : f =ᶠ[𝓝 x] h) (i : Fin n) : partialBar i f x = partialBar i h x := by
  simp only [partialBar, dz, rd, heq.fderiv_eq]

theorem partialZ_congr_nhds {n : ℕ} {f h : E n → ℂ} {x : E n}
    (heq : f =ᶠ[𝓝 x] h) (i : Fin n) : partialZ i f x = partialZ i h x := by
  simp only [partialZ, dz, rd, heq.fderiv_eq]

/-- A real-linear complex covector that commutes with J is complex linear. -/
theorem complex_linear_covector_coordinates {n : ℕ} (L : E n →L[ℝ] ℂ)
    (hJ : ∀ v, L (J v) = Complex.I * L v) (v : E n) :
    L v = ∑ i : Fin n, L (realDirection i) * complexCoord v i := by
  nth_rw 1 [← interleaved_decomposition v]
  simp only [map_sum, map_add, map_smul, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← J_realDirection_eq_imag, hJ]
  simp only [complexCoord]
  ring

/-- Coordinates of D acting on actual constant fields. -/
noncomputable def complexConnectionCoeff {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (x : E n) (i j k : Fin n) : ℂ :=
  complexCoord (D.euclideanConnection (realDirection i) (realDirection j) x) k

theorem complexConnectionCoeff_smoothAt {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (x : E n) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun y => complexConnectionCoeff D y i j k) x := by
  exact (complexCoordCLM k).contDiff.contDiffAt.comp x
    (D.contDiffAt_euclideanConnection x (realDirection i) (realDirection j))

/-- Complex bilinear coordinates, derived from the actual connection's
J-linearity and torsion-free constant-frame symmetry. -/
theorem euclideanConnection_complex_coordinates {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) (k : Fin n) :
    complexCoord (D.euclideanConnection v w x) k =
      ∑ i : Fin n, ∑ j : Fin n,
        complexConnectionCoeff D x i j k * complexCoord v i * complexCoord w j := by
  have hleft (a b : E n) : complexCoord (D.euclideanConnection a b x) k =
      ∑ i : Fin n, complexCoord
        (D.euclideanConnection (realDirection i) b x) k * complexCoord a i := by
    let L := (complexCoordCLM k).comp (D.connection (fun _ : E n => b) x)
    have hJ (z : E n) : L (J z) = Complex.I * L z := by
      change complexCoord (D.connection (fun _ : E n => b) x (J z)) k = _
      rw [connection_const_J_left D hU hu hg hx, complexCoord_J]
      rfl
    exact complex_linear_covector_coordinates L hJ a
  rw [hleft]
  apply Finset.sum_congr rfl
  intro i _
  have hright : complexCoord (D.euclideanConnection (realDirection i) w x) k =
      ∑ j : Fin n, complexConnectionCoeff D x i j k * complexCoord w j := by
    change complexCoord (D.connection (fun _ : E n => w) x (realDirection i)) k = _
    rw [connection_const_swap D hU hu hg hx]
    change complexCoord (D.euclideanConnection w (realDirection i) x) k = _
    rw [hleft]
    apply Finset.sum_congr rfl
    intro j _
    unfold complexConnectionCoeff PoincareMT.LeviCivitaData.euclideanConnection
    rw [connection_const_swap D hU hu hg hx]
  rw [hright, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Differentiate fixed coordinate fields; neither v nor w is varied. -/
theorem rd_euclideanConnection_coordinates {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (a v w : E n) (k : Fin n) :
    complexCoord (fderiv ℝ (D.euclideanConnection v w) x a) k =
      ∑ i : Fin n, ∑ j : Fin n,
        rd a (fun y => complexConnectionCoeff D y i j k) x *
          complexCoord v i * complexCoord w j := by
  have heq : (fun y => complexCoord (D.euclideanConnection v w y) k) =ᶠ[𝓝 x]
      (fun y => ∑ i : Fin n, ∑ j : Fin n,
        complexConnectionCoeff D y i j k * complexCoord v i * complexCoord w j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact euclideanConnection_complex_coordinates D hU hu hg hy v w k
  have hd := (complexCoordCLM k).hasFDerivAt.comp x
    ((D.contDiffAt_euclideanConnection x v w).differentiableAt (by simp)).hasFDerivAt
  have hfirst : rd a (fun y => complexCoord (D.euclideanConnection v w y) k) x =
      complexCoord (fderiv ℝ (D.euclideanConnection v w) x a) k := by
    change fderiv ℝ ((complexCoordCLM k) ∘ D.euclideanConnection v w) x a = _
    rw [hd.fderiv]
    rfl
  rw [← hfirst]
  change fderiv ℝ _ x a = _
  rw [heq.fderiv_eq]
  change rd a _ x = _
  have hc (i j : Fin n) : DifferentiableAt ℝ
      (fun y => complexConnectionCoeff D y i j k * complexCoord v i * complexCoord w j) x :=
    ((complexConnectionCoeff_smoothAt D x i j k).differentiableAt (by simp)).mul_const
      (complexCoord v i) |>.mul_const (complexCoord w j)
  have hci (i : Fin n) : DifferentiableAt ℝ
      (fun y => ∑ j : Fin n,
        complexConnectionCoeff D y i j k * complexCoord v i * complexCoord w j) x :=
    DifferentiableAt.fun_sum (fun j _ => hc i j)
  rw [rd_sum_differentiableAt hci]
  apply Finset.sum_congr rfl
  intro i _
  rw [rd_sum_differentiableAt (fun j => hc i j)]
  apply Finset.sum_congr rfl
  intro j _
  have hco := (complexConnectionCoeff_smoothAt D x i j k).differentiableAt (by simp)
  rw [rd_mul_differentiableAt (hco.mul_const _) (differentiableAt_const _),
    rd_mul_differentiableAt hco (differentiableAt_const _)]
  simp only [rd, fderiv_const_apply, zero_apply, mul_zero, add_zero]


/-- Complex anti-index symmetry of the actual metric's third derivatives. -/
theorem partialBar_metric_swap {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (k j s : Fin n) :
    partialBar j (fun y => complexHessian u y k s) x =
      partialBar s (fun y => complexHessian u y k j) x := by
  have hf : ContDiffOn ℝ ∞ (fun y => (u y : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hfAt := hf.contDiffAt (hU.mem_nhds hx)
  have hs := smoothAt_dz hfAt (realDirection s) (-imagDirection s)
  have hj := smoothAt_dz hfAt (realDirection j) (-imagDirection j)
  have heq : partialBar j (partialBar s (fun y => (u y : ℂ))) =ᶠ[𝓝 x]
      partialBar s (partialBar j (fun y => (u y : ℂ))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dz_comm_on hU hf (realDirection j) (-imagDirection j)
      (realDirection s) (-imagDirection s) hy
  calc
    _ = partialZ k (partialBar j (partialBar s (fun y => (u y : ℂ)))) x :=
      dz_comm_at hs _ _ _ _
    _ = partialZ k (partialBar s (partialBar j (fun y => (u y : ℂ)))) x :=
      partialZ_congr_nhds heq k
    _ = _ := (dz_comm_at hj _ _ _ _).symm

/-- The corresponding fourth-jet symmetry, with local equality before the
additional derivative. No pointwise equality is illegitimately differentiated. -/
theorem partialBar_partialZ_metric_swap {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (i l j s : Fin n) :
    partialBar j (partialZ i (fun y => complexHessian u y l s)) x =
      partialBar s (partialZ i (fun y => complexHessian u y l j)) x := by
  have hls := (complexHessian_contDiffOn hU hu l s).contDiffAt (hU.mem_nhds hx)
  have hlj := (complexHessian_contDiffOn hU hu l j).contDiffAt (hU.mem_nhds hx)
  have heq : partialBar j (fun y => complexHessian u y l s) =ᶠ[𝓝 x]
      partialBar s (fun y => complexHessian u y l j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact partialBar_metric_swap hU hu hy l j s
  calc
    _ = partialZ i (partialBar j (fun y => complexHessian u y l s)) x :=
      dz_comm_at hls _ _ _ _
    _ = partialZ i (partialBar s (fun y => complexHessian u y l j)) x :=
      partialZ_congr_nhds heq i
    _ = _ := (dz_comm_at hlj _ _ _ _).symm

end KEBall
