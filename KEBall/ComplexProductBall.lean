import KEBall.ComplexBallMove
import PshLines.FirstPass.MongeAmpere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Product balls in Euclidean complex coordinates
-/

set_option autoImplicit false

open Metric Set TopologicalSpace

namespace KEBall

open PshLines.FirstPass (ComplexModel)

private noncomputable def complexProductIsometry (n m : ℕ) :
    ComplexModel (n + m) ≃ₗᵢ[ℂ] WithLp 2 (ComplexModel n × ComplexModel m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℂ))

/-- Splitting the Euclidean complex coordinates into the two ball factors. -/
noncomputable def complexProductCoordinates (n m : ℕ) :
    ComplexModel (n + m) ≃L[ℂ] ComplexModel n × ComplexModel m :=
  (complexProductIsometry n m).toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℂ _ _)

theorem measurePreserving_complexProductCoordinates (n m : ℕ) :
    MeasureTheory.MeasurePreserving (complexProductCoordinates n m) := by
  let e := complexProductIsometry n m
  let er : ComplexModel (n + m) ≃ₗᵢ[ℝ] WithLp 2 (ComplexModel n × ComplexModel m) :=
    ⟨e.toLinearEquiv.restrictScalars ℝ, e.norm_map⟩
  exact (WithLp.volume_preserving_ofLp (ComplexModel n) (ComplexModel m)).comp er.measurePreserving

theorem complexProductCoordinates_coordinateVector_inl {n m : ℕ} (i : Fin n) :
    complexProductCoordinates n m (PshLines.FirstPass.MongeAmpere.coordinateVector
      (finSumFinEquiv (Sum.inl i))) = (PshLines.FirstPass.MongeAmpere.coordinateVector i, 0) := by
  change WithLp.ofLp (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℂ)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv.symm
      (PiLp.single 2 (finSumFinEquiv (Sum.inl i)) 1))) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_single, Equiv.symm_apply_apply]
  apply Prod.ext
  · ext j
    change (PiLp.single (β := fun _ : Fin n ⊕ Fin m => ℂ) 2 (Sum.inl i) (1 : ℂ)) (Sum.inl j) = (PiLp.single (β := fun _ : Fin n => ℂ) 2 i 1) j
    simp [PiLp.single_apply, Pi.single_apply]
  · ext j
    change (PiLp.single (β := fun _ : Fin n ⊕ Fin m => ℂ) 2 (Sum.inl i) (1 : ℂ)) (Sum.inr j) = 0
    simp [PiLp.single_apply, Pi.single_apply]

theorem complexProductCoordinates_coordinateVector_inr {n m : ℕ} (i : Fin m) :
    complexProductCoordinates n m (PshLines.FirstPass.MongeAmpere.coordinateVector
      (finSumFinEquiv (Sum.inr i))) = (0, PshLines.FirstPass.MongeAmpere.coordinateVector i) := by
  change WithLp.ofLp (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℂ)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv.symm
      (PiLp.single 2 (finSumFinEquiv (Sum.inr i)) 1))) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_single, Equiv.symm_apply_apply]
  apply Prod.ext
  · ext j
    change (PiLp.single (β := fun _ : Fin n ⊕ Fin m => ℂ) 2 (Sum.inr i) (1 : ℂ)) (Sum.inl j) = 0
    simp [PiLp.single_apply, Pi.single_apply]
  · ext j
    change (PiLp.single (β := fun _ : Fin n ⊕ Fin m => ℂ) 2 (Sum.inr i) (1 : ℂ)) (Sum.inr j) = (PiLp.single (β := fun _ : Fin m => ℂ) 2 i 1) j
    simp [PiLp.single_apply, Pi.single_apply]

noncomputable def complexProductBall (n m : ℕ) : Opens (ComplexModel (n + m)) :=
  ⟨(complexProductCoordinates n m) ⁻¹' (ball 0 1 ×ˢ ball 0 1),
    (isOpen_ball.prod isOpen_ball).preimage (complexProductCoordinates n m).continuous⟩

theorem mem_complexProductBall {n m : ℕ} {z : ComplexModel (n + m)} :
    z ∈ complexProductBall n m ↔
      ‖(complexProductCoordinates n m z).1‖ < 1 ∧ ‖(complexProductCoordinates n m z).2‖ < 1 := by
  change (complexProductCoordinates n m z ∈ ball 0 1 ×ˢ ball 0 1) ↔ _
  simp only [mem_prod, mem_ball, dist_zero_right]

theorem norm_sq_complexProductCoordinates {n m : ℕ} (z : ComplexModel (n + m)) :
    ‖z‖ ^ 2 = ‖(complexProductCoordinates n m z).1‖ ^ 2 + ‖(complexProductCoordinates n m z).2‖ ^ 2 := by
  rw [← (complexProductIsometry n m).norm_map z]
  exact WithLp.prod_norm_sq_eq_of_L2 (complexProductIsometry n m z)

theorem norm_fst_complexProductCoordinates_le {n m : ℕ} (z : ComplexModel (n + m)) :
    ‖(complexProductCoordinates n m z).1‖ ≤ ‖z‖ := by
  rw [← (complexProductIsometry n m).norm_map z]
  exact WithLp.norm_fst_le _ (complexProductIsometry n m z)

theorem norm_snd_complexProductCoordinates_le {n m : ℕ} (z : ComplexModel (n + m)) :
    ‖(complexProductCoordinates n m z).2‖ ≤ ‖z‖ := by
  rw [← (complexProductIsometry n m).norm_map z]
  exact WithLp.norm_snd_le _ (complexProductIsometry n m z)

theorem norm_le_complexProductCoordinates {n m : ℕ} (z : ComplexModel (n + m)) :
    ‖z‖ ≤ ‖(complexProductCoordinates n m z).1‖ + ‖(complexProductCoordinates n m z).2‖ := by
  nlinarith only [norm_sq_complexProductCoordinates z, norm_nonneg z,
    norm_nonneg (complexProductCoordinates n m z).1, norm_nonneg (complexProductCoordinates n m z).2]

/-- The product of the two changes of center, in the ambient complex model. -/
noncomputable def complexProductBallMove {n m : ℕ}
    (a h z : ComplexModel (n + m)) : ComplexModel (n + m) :=
  let e := complexProductCoordinates n m
  e.symm (complexBallMove (e a).1 (e h).1 (e z).1, complexBallMove (e a).2 (e h).2 (e z).2)

@[simp] theorem complexProductCoordinates_ballMove {n m : ℕ}
    (a h z : ComplexModel (n + m)) :
    complexProductCoordinates n m (complexProductBallMove (n := n) (m := m) a h z) =
      (complexBallMove (complexProductCoordinates n m a).1 (complexProductCoordinates n m h).1
        (complexProductCoordinates n m z).1,
      complexBallMove (complexProductCoordinates n m a).2 (complexProductCoordinates n m h).2
        (complexProductCoordinates n m z).2) :=
  (complexProductCoordinates n m).apply_symm_apply _

theorem complexProductBallMove_mapsTo {n m : ℕ} {a h : ComplexModel (n + m)}
    (ha : a ∈ complexProductBall n m) (hah : a + h ∈ complexProductBall n m) :
    MapsTo (complexProductBallMove (n := n) (m := m) a h) (complexProductBall n m) (complexProductBall n m) := by
  let e := complexProductCoordinates n m
  have ha' := mem_complexProductBall.mp ha
  have hah' : ‖(e a).1 + (e h).1‖ < 1 ∧ ‖(e a).2 + (e h).2‖ < 1 := by
    simpa only [e, map_add, Prod.fst_add, Prod.snd_add] using mem_complexProductBall.mp hah
  intro z hz
  have hz' : e z ∈ ball 0 1 ×ˢ ball 0 1 := hz
  change e (complexProductBallMove (n := n) (m := m) a h z) ∈ ball 0 1 ×ˢ ball 0 1
  rw [complexProductCoordinates_ballMove]
  exact ⟨complexBallMove_mapsTo_unitBall ha'.1 hah'.1 hz'.1,
    complexBallMove_mapsTo_unitBall ha'.2 hah'.2 hz'.2⟩

theorem differentiableOn_complexProductBallMove {n m : ℕ} {a h : ComplexModel (n + m)}
    (ha : a ∈ complexProductBall n m) (hah : a + h ∈ complexProductBall n m) :
    DifferentiableOn ℂ (complexProductBallMove (n := n) (m := m) a h) (complexProductBall n m) := by
  let e := complexProductCoordinates n m
  let P : Set (ComplexModel (n + m)) := complexProductBall n m
  have ha' := mem_complexProductBall.mp ha
  have hah' : ‖(e a).1 + (e h).1‖ < 1 ∧ ‖(e a).2 + (e h).2‖ < 1 := by
    simpa only [e, map_add, Prod.fst_add, Prod.snd_add] using mem_complexProductBall.mp hah
  have he1 : DifferentiableOn ℂ (fun z => (e z).1) P := e.differentiable.differentiableOn.fst
  have he2 : DifferentiableOn ℂ (fun z => (e z).2) P := e.differentiable.differentiableOn.snd
  have h1 := (differentiableOn_complexBallMove ha'.1 hah'.1).comp he1
    (fun _ hz => (show e _ ∈ ball 0 1 ×ˢ ball 0 1 from hz).1)
  have h2 := (differentiableOn_complexBallMove ha'.2 hah'.2).comp he2
    (fun _ hz => (show e _ ∈ ball 0 1 ×ˢ ball 0 1 from hz).2)
  exact e.symm.differentiable.comp_differentiableOn (h1.prodMk h2)

theorem complexProductBallMove_at_center {n m : ℕ} {a h : ComplexModel (n + m)}
    (ha : a ∈ complexProductBall n m) (hah : a + h ∈ complexProductBall n m) :
    complexProductBallMove (n := n) (m := m) a h a = a + h := by
  let e := complexProductCoordinates n m
  have ha' := mem_complexProductBall.mp ha
  have hah' : ‖(e a).1 + (e h).1‖ < 1 ∧ ‖(e a).2 + (e h).2‖ < 1 := by
    simpa only [e, map_add, Prod.fst_add, Prod.snd_add] using mem_complexProductBall.mp hah
  apply e.injective
  rw [complexProductCoordinates_ballMove, complexBallMove_at_center ha'.1 hah'.1,
    complexBallMove_at_center ha'.2 hah'.2, map_add]
  rfl

set_option maxHeartbeats 800000 in
theorem exists_complexProductBallMove_displacement (n m : ℕ)
    {r δ : ℝ} (hδ : 0 ≤ δ) (hrδ : r + δ < 1) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
      ∀ a : ComplexModel (n + m), ‖(complexProductCoordinates n m a).1‖ ≤ r →
        ‖(complexProductCoordinates n m a).2‖ ≤ r →
      ∀ h : ComplexModel (n + m), ‖h‖ ≤ δ →
      ∀ z ∈ complexProductBall n m,
        ‖complexProductBallMove (n := n) (m := m) a h z - z‖ ≤ L * ‖h‖ ∧
        ‖(complexProductBallMove (n := n) (m := m) a h z - z) +
          (complexProductBallMove (n := n) (m := m) a (-h) z - z)‖ ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨C₁, L₁, hC₁, hL₁, h₁⟩ := exists_complexBallMove_displacement (H := ComplexModel n) hδ hrδ
  obtain ⟨C₂, L₂, hC₂, hL₂, h₂⟩ := exists_complexBallMove_displacement (H := ComplexModel m) hδ hrδ
  refine ⟨C₁ + C₂, L₁ + L₂, add_nonneg hC₁ hC₂, add_nonneg hL₁ hL₂, ?_⟩
  intro a ha₁ ha₂ h hh z hz
  let e := complexProductCoordinates n m
  let F := complexProductBallMove (n := n) (m := m) a h
  let G := complexProductBallMove (n := n) (m := m) a (-h)
  have hh₁ := norm_fst_complexProductCoordinates_le (n := n) (m := m) h
  have hh₂ := norm_snd_complexProductCoordinates_le (n := n) (m := m) h
  have hz' := mem_complexProductBall.mp hz
  have he₁ := h₁ (e a).1 ha₁ (e h).1 (hh₁.trans hh) (e z).1 hz'.1.le
  have he₂ := h₂ (e a).2 ha₂ (e h).2 (hh₂.trans hh) (e z).2 hz'.2.le
  constructor
  · have hfst : ‖(e (F z - z)).1‖ ≤ L₁ * ‖(e h).1‖ := by
      simpa only [e, F, map_sub, complexProductCoordinates_ballMove, Prod.fst_sub] using he₁.1
    have hsnd : ‖(e (F z - z)).2‖ ≤ L₂ * ‖(e h).2‖ := by
      simpa only [e, F, map_sub, complexProductCoordinates_ballMove, Prod.snd_sub] using he₂.1
    calc
      ‖F z - z‖ ≤ ‖(e (F z - z)).1‖ + ‖(e (F z - z)).2‖ :=
        norm_le_complexProductCoordinates (n := n) (m := m) _
      _ ≤ L₁ * ‖(e h).1‖ + L₂ * ‖(e h).2‖ := add_le_add hfst hsnd
      _ ≤ (L₁ + L₂) * ‖h‖ := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hh₁ hL₁) (mul_le_mul_of_nonneg_left hh₂ hL₂)
  · let d := (F z - z) + (G z - z)
    have hfst : ‖(e d).1‖ ≤ C₁ * ‖(e h).1‖ ^ 2 := by
      simpa only [e, d, F, G, map_add, map_sub, complexProductCoordinates_ballMove,
        map_neg, Prod.fst_add, Prod.fst_sub, Prod.fst_neg] using he₁.2
    have hsnd : ‖(e d).2‖ ≤ C₂ * ‖(e h).2‖ ^ 2 := by
      simpa only [e, d, F, G, map_add, map_sub, complexProductCoordinates_ballMove,
        map_neg, Prod.snd_add, Prod.snd_sub, Prod.snd_neg] using he₂.2
    calc
      ‖d‖ ≤ ‖(e d).1‖ + ‖(e d).2‖ := norm_le_complexProductCoordinates (n := n) (m := m) d
      _ ≤ C₁ * ‖(e h).1‖ ^ 2 + C₂ * ‖(e h).2‖ ^ 2 := add_le_add hfst hsnd
      _ ≤ (C₁ + C₂) * ‖h‖ ^ 2 := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh₁ 2) hC₁)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh₂ 2) hC₂)

end KEBall
