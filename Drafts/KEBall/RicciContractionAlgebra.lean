import Drafts.KEBall.ComplexTensorContraction

/-!
# Finite coordinate curvature contraction

Stage04 DRAFT, not kernel checked. No differential-geometric definitions,
KE hypotheses, or Ricci axioms occur here. The application supplies actual
connection coefficients, their actual derivatives, and proved frame moments.
-/
set_option autoImplicit false
open scoped BigOperators

namespace KEBall.CurvatureCoordinateAlgebra

variable {ι α : Type*} [Fintype ι] [Fintype α]

noncomputable def conn (A : ι → ι → ι → ℂ) (v w : ι → ℂ) (k : ι) : ℂ :=
  ∑ i, ∑ l, A i l k * v i * w l

noncomputable def dconn (P Q : ι → ι → ι → ι → ℂ)
    (a v w : ι → ℂ) (k : ι) : ℂ :=
  conn (fun i l k => ∑ j, (P j i l k * a j + Q j i l k * star (a j))) v w k

noncomputable def curvature (A : ι → ι → ι → ℂ)
    (P Q : ι → ι → ι → ι → ℂ) (v w z : ι → ℂ) (k : ι) : ℂ :=
  dconn P Q v w z k + conn A v (conn A w z) k -
    (dconn P Q w v z k + conn A w (conn A v z) k)

/-- Swap two finite sums inside a third without choosing an ordering of indices. -/
theorem sum3_rotate {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (f : β → γ → δ → ℂ) :
    (∑ b, ∑ c, ∑ d, f b c d) = ∑ d, ∑ b, ∑ c, f b c d := by
  classical
  calc
    _ = ∑ b, ∑ d, ∑ c, f b c d := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- A weighted pair contraction; c and d need not be related. -/
theorem weighted_pair (c d : α → ι → ℂ) (A : ι → ι → ℂ) :
    (∑ a, ∑ i, ∑ j, A i j * c a i * d a j) =
      ∑ i, ∑ j, A i j * (∑ a, c a i * d a j) := by
  classical
  calc
    _ = ∑ i, ∑ a, ∑ j, A i j * c a i * d a j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, A i j * c a i * d a j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

/-- Any complex bilinear diagonal vanishes in an isotropic real frame. -/
theorem conn_frame_zero (c : α → ι → ℂ)
    (hhol : ∀ i j, (∑ a, c a i * c a j) = 0)
    (A : ι → ι → ι → ℂ) (k : ι) :
    (∑ a, conn A (c a) (c a) k) = 0 := by
  classical
  unfold conn
  rw [weighted_pair]
  simp only [hhol, mul_zero, Finset.sum_const_zero]

theorem conn_sum_right (A : ι → ι → ι → ℂ) (v : ι → ℂ)
    (w : α → ι → ℂ) (k : ι) :
    (∑ a, conn A v (w a) k) = conn A v (fun l => ∑ a, w a l) k := by
  classical
  unfold conn
  calc
    _ = ∑ i, ∑ a, ∑ l, A i l k * v i * w a l := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ a, A i l k * v i * w a l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

/-- Composition remains complex bilinear in its two free slots. -/
theorem conn_nested (A : ι → ι → ι → ℂ) (v c d : ι → ℂ) (k : ι) :
    conn A c (conn A v d) k =
      conn (fun i m k => ∑ l, ∑ j, A i l k * A j m l * v j) c d k := by
  classical
  unfold conn
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ l, ∑ j, ∑ m, A i l k * (A j m l * v j * d m) * c i := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ m, ∑ l, ∑ j, A i l k * (A j m l * v j * d m) * c i :=
      sum3_rotate _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The only surviving derivative contraction is antiholomorphic. -/
theorem dconn_cross_frame (c : α → ι → ℂ) (C : ι → ι → ℂ)
    (hhol : ∀ i j, (∑ a, c a i * c a j) = 0)
    (hpair : ∀ i j, (∑ a, c a i * star (c a j)) = C i j)
    (P Q : ι → ι → ι → ι → ℂ) (v : ι → ℂ) (k : ι) :
    (∑ a, dconn P Q (c a) v (c a) k) =
      ∑ i, ∑ l, ∑ j, Q j i l k * v i * C l j := by
  classical
  unfold dconn conn
  simp only [Finset.sum_mul]
  calc
    _ = ∑ i, ∑ l, ∑ j, ∑ a,
        (P j i l k * c a j + Q j i l k * star (c a j)) * v i * c a l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = P j i l k * v i * (∑ a, c a j * c a l) +
            Q j i l k * v i * (∑ a, c a l * star (c a j)) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by rw [hhol, hpair]; ring

/-- The full coordinate curvature, including both connection quadratic terms,
is contracted here. Their vanishing is proved rather than assumed. -/
theorem curvature_frame_trace (c : α → ι → ℂ) (C : ι → ι → ℂ)
    (hhol : ∀ i j, (∑ a, c a i * c a j) = 0)
    (hpair : ∀ i j, (∑ a, c a i * star (c a j)) = C i j)
    (A : ι → ι → ι → ℂ) (P Q : ι → ι → ι → ι → ℂ)
    (v : ι → ℂ) (k : ι) :
    (∑ a, curvature A P Q v (c a) (c a) k) =
      -(∑ i, ∑ l, ∑ j, Q j i l k * v i * C l j) := by
  classical
  have hfirst : (∑ a, dconn P Q v (c a) (c a) k) = 0 :=
    conn_frame_zero c hhol _ k
  have hquad1 : (∑ a, conn A v (conn A (c a) (c a)) k) = 0 := by
    rw [conn_sum_right]
    have hz : (fun l => ∑ a, conn A (c a) (c a) l) = (fun _ => 0) := by
      funext l
      exact conn_frame_zero c hhol A l
    rw [hz]
    simp only [conn, mul_zero, Finset.sum_const_zero]
  have hquad2 : (∑ a, conn A (c a) (conn A v (c a)) k) = 0 := by
    simp_rw [conn_nested]
    exact conn_frame_zero c hhol _ k
  simp only [curvature, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hfirst, hquad1, hquad2, zero_add, add_zero, zero_sub]
  rw [dconn_cross_frame c C hhol hpair]

/-- Lowering the output index makes the two antiholomorphic indices symmetric.
After inverse contraction this is exactly the derivative of the connection trace.
The application proves hsym by differentiating its actual metric row identity. -/
theorem lowered_contraction_trace [DecidableEq ι]
    (G C : ι → ι → ℂ) (Q : ι → ι → ι → ι → ℂ)
    (hinv : ∀ k l, (∑ j, G k j * C l j) = if k = l then 1 else 0)
    (hsym : ∀ i l j s, (∑ k, G k s * Q j i l k) =
      ∑ k, G k j * Q s i l k) (i s : ι) :
    (∑ l, ∑ j, C l j * (∑ k, G k s * Q j i l k)) =
      ∑ k, Q s i k k := by
  calc
    _ = ∑ l, ∑ j, C l j * (∑ k, G k j * Q s i l k) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym i l j s]
    _ = ∑ l, ∑ k, (∑ j, G k j * C l j) * Q s i l k := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [hinv]
      simp

/-- Reorder precisely the five slots appearing in the Ricci contraction. -/
theorem sum5_ricci_order (f : ι → ι → ι → ι → ι → ℂ) :
    (∑ k, ∑ s, ∑ i, ∑ l, ∑ j, f k s i l j) =
      ∑ i, ∑ s, ∑ l, ∑ j, ∑ k, f k s i l j := by
  classical
  calc
    _ = ∑ s, ∑ k, ∑ i, ∑ l, ∑ j, f k s i l j := Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ k, ∑ l, ∑ j, f k s i l j := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ k, ∑ l, ∑ j, f k s i l j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro s _
      rw [sum3_rotate, sum3_rotate]

/-- The remaining metric contraction, with the manuscript's inverse transpose. -/
theorem ricci_coefficient_sum [DecidableEq ι]
    (G C : ι → ι → ℂ) (Q : ι → ι → ι → ι → ℂ)
    (hinv : ∀ k l, (∑ j, G k j * C l j) = if k = l then 1 else 0)
    (hsym : ∀ i l j s, (∑ k, G k s * Q j i l k) =
      ∑ k, G k j * Q s i l k) (v w : ι → ℂ) :
    (∑ k, ∑ s, G k s * (∑ i, ∑ l, ∑ j, Q j i l k * v i * C l j) * star (w s)) =
      ∑ i, ∑ s, (∑ k, Q s i k k) * v i * star (w s) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum5_ricci_order]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = (∑ l, ∑ j, C l j * (∑ k, G k s * Q j i l k)) * v i * star (w s) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [lowered_contraction_trace G C Q hinv hsym]
      simp only [Finset.sum_mul]

end KEBall.CurvatureCoordinateAlgebra
