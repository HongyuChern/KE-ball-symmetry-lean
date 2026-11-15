import KEBall.BoundaryHessian
import KEBall.BoundaryRegularity
import KEBall.ComplexFlux
import KEBall.Specification

/-!
# Actual horizontal boundary geometry

The horizontal projection is the orthogonal complement of the genuine
normal `x` and Hopf vector `J x`. Boundary positivity of the slope is
deduced from the already proved tangent Hessian and positive definiteness
of the solution metric, using a constructed nonzero horizontal vector.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

@[simp] theorem complexCoord_complexVectorReal {n : ℕ} (z : Fin n → ℂ) :
    complexCoord (complexVectorReal z) = z := by
  funext i
  simp only [complexCoord, complexVectorReal_realIndex, complexVectorReal_imagIndex]
  rw [mul_comm Complex.I, Complex.re_add_im]

theorem inner_J_self_zero {n : ℕ} (x : E n) : inner ℝ x (J x) = 0 := by
  have h := inner_J_skew x x
  have hc : inner ℝ (J x) x = inner ℝ x (J x) := real_inner_comm _ _
  rw [hc] at h
  linarith

theorem sphere_inner_self {n : ℕ} {x : E n} (hx : x ∈ unitSphere n) :
    inner ℝ x x = 1 := by
  have hnorm : ‖x‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  rw [real_inner_self_eq_norm_sq, hnorm, one_pow]

noncomputable def horizontalProjection {n : ℕ} (x v : E n) : E n :=
  v - inner ℝ v x • x - inner ℝ v (J x) • J x

theorem horizontalProjection_inner_normal {n : ℕ} {x : E n}
    (hx : x ∈ unitSphere n) (v : E n) :
    inner ℝ x (horizontalProjection x v) = 0 := by
  simp only [horizontalProjection, inner_sub_right, real_inner_smul_right,
    sphere_inner_self hx, inner_J_self_zero, mul_one, mul_zero, sub_zero]
  rw [real_inner_comm x v, sub_self]

theorem horizontalProjection_inner_hopf {n : ℕ} {x : E n}
    (hx : x ∈ unitSphere n) (v : E n) :
    inner ℝ (J x) (horizontalProjection x v) = 0 := by
  have hJn : inner ℝ (J x) x = 0 := by
    rw [real_inner_comm, inner_J_self_zero]
  simp only [horizontalProjection, inner_sub_right, real_inner_smul_right,
    inner_J_J, sphere_inner_self hx, hJn, mul_zero, sub_zero, mul_one]
  exact sub_eq_zero.mpr (real_inner_comm _ _)

theorem horizontalProjection_eq_self {n : ℕ} {x v : E n}
    (hn : inner ℝ x v = 0) (hJ : inner ℝ (J x) v = 0) :
    horizontalProjection x v = v := by
  have hnv : inner ℝ v x = 0 := by rw [real_inner_comm]; exact hn
  have hJv : inner ℝ v (J x) = 0 := by rw [real_inner_comm]; exact hJ
  simp only [horizontalProjection, hnv, hJv, zero_smul, sub_zero]

theorem inner_euclideanGradient {n : ℕ} (h : E n → ℝ) (x v : E n) :
    inner ℝ (euclideanGradient h x) v = fderiv ℝ h x v := by
  have hv := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr v
  have hd := congrArg (fderiv ℝ h x) hv
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] at hd
  rw [euclideanGradient, sum_inner]
  simp only [real_inner_smul_left, EuclideanSpace.inner_single_left,
    conj_trivial, one_mul]
  simpa only [mul_comm] using hd

theorem euclideanGradient_realIndex {n : ℕ} (h : E n → ℝ) (x : E n) (i : Fin n) :
    euclideanGradient h x (realIndex i) = fderiv ℝ h x (realDirection i) := by
  simpa only [realDirection, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    using inner_euclideanGradient h x (realDirection i)

theorem euclideanGradient_imagIndex {n : ℕ} (h : E n → ℝ) (x : E n) (i : Fin n) :
    euclideanGradient h x (imagIndex i) = fderiv ℝ h x (imagDirection i) := by
  simpa only [imagDirection, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    using inner_euclideanGradient h x (imagDirection i)

theorem horizontalGradient_eq_projection {n : ℕ} (h : E n → ℝ) (x : E n) :
    horizontalGradient h x = horizontalProjection x (euclideanGradient h x) := rfl

theorem horizontalGradient_inner_normal {n : ℕ} (h : E n → ℝ) {x : E n}
    (hx : x ∈ unitSphere n) : inner ℝ x (horizontalGradient h x) = 0 :=
  horizontalProjection_inner_normal hx _

theorem horizontalGradient_inner_hopf {n : ℕ} (h : E n → ℝ) {x : E n}
    (hx : x ∈ unitSphere n) : inner ℝ (J x) (horizontalGradient h x) = 0 :=
  horizontalProjection_inner_hopf hx _

theorem inner_horizontalGradient {n : ℕ} (h : E n → ℝ) {x v : E n}
    (hn : inner ℝ x v = 0) (hJ : inner ℝ (J x) v = 0) :
    inner ℝ (horizontalGradient h x) v = fderiv ℝ h x v := by
  simp only [horizontalGradient, inner_sub_left, real_inner_smul_left,
    hn, hJ, mul_zero, sub_zero, inner_euclideanGradient]

theorem exists_nonzero_horizontal {n : ℕ} (hn : 2 ≤ n) {x : E n}
    (hx : x ∈ unitSphere n) :
    ∃ v : E n, v ≠ 0 ∧ inner ℝ x v = 0 ∧ inner ℝ (J x) v = 0 := by
  classical
  have hxn : x ≠ 0 := by
    intro hz
    have hs := sphere_inner_self hx
    simp [hz] at hs
  have hzc : complexCoord x ≠ 0 := fun hz => hxn (complexCoord_eq_zero_iff.mp hz)
  obtain ⟨i, hi⟩ : ∃ i : Fin n, complexCoord x i ≠ 0 := by
    by_contra h
    apply hzc
    funext i
    exact Classical.byContradiction (fun hi => h ⟨i, hi⟩)
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  let w : Fin n → ℂ := Pi.single i (star (complexCoord x j)) -
    Pi.single j (star (complexCoord x i))
  have hwj : w j = -star (complexCoord x i) := by simp [w, hji]
  have hw : w ≠ 0 := by
    intro hz
    have he := congrFun hz j
    rw [hwj] at he
    exact hi (by simpa only [Pi.zero_apply, neg_eq_zero, star_eq_zero] using he)
  have hdot : (∑ k : Fin n, star (complexCoord x k) * w k) = 0 := by
    simp only [w, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp [Pi.single_apply, mul_comm]
  refine ⟨complexVectorReal w, ?_, ?_, ?_⟩
  · intro hv
    apply hw
    rw [← complexCoord_complexVectorReal w, hv]
    exact complexCoord_eq_zero_iff.mpr rfl
  · rw [inner_complexVectorReal, hdot]
    rfl
  · rw [inner_complexVectorReal]
    have he : (∑ k : Fin n, star (complexCoord (J x) k) * w k) =
        -Complex.I * (∑ k : Fin n, star (complexCoord x k) * w k) := by
      simp only [complexCoord_J, star_mul, Complex.star_def, Complex.conj_I,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he, hdot, mul_zero]
    rfl

theorem sphere_metric_horizontal {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x v w : E n} (hx : x ∈ unitSphere n)
    (hvn : inner ℝ x v = 0) (hvJ : inner ℝ (J x) v = 0)
    (hwn : inner ℝ x w = 0) (hwJ : inner ℝ (J x) w = 0) :
    realMetricForm u x v w = 2 * boundarySlope u x * inner ℝ v w := by
  have hvJn : inner ℝ x (J v) = 0 := by
    have h := inner_J_skew x v
    rw [hvJ] at h
    linarith
  have hwJn : inner ℝ x (J w) = 0 := by
    have h := inner_J_skew x w
    rw [hwJ] at h
    linarith
  rw [realMetricForm_eq_average_hessian (hu.contDiffAt (Metric.sphere_subset_closedBall hx)),
    sphere_tangent_hessian hu hzero hx hvn hwn,
    sphere_tangent_hessian hu hzero hx hvJn hwJn, inner_J_J]
  ring

theorem IsSolution.boundarySlope_pos {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    0 < boundarySlope u x := by
  obtain ⟨v, hv, hvn, hvJ⟩ := exists_nonzero_horizontal hn hx
  have hp := hermitianRealification_pos
    (hu.hessian_posDef_closedBall (Metric.sphere_subset_closedBall hx)) v hv
  rw [← realMetricForm_eq, sphere_metric_horizontal hu.2.1 hu.2.2.2.2 hx hvn hvJ hvn hvJ] at hp
  have hinner : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
  nlinarith

#print axioms exists_nonzero_horizontal
#print axioms inner_euclideanGradient
#print axioms sphere_metric_horizontal
#print axioms IsSolution.boundarySlope_pos

end KEBall
