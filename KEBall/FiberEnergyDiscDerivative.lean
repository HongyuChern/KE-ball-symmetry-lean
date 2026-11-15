import KEBall.FiberEnergyIntegral
import KEBall.FiberEnergyMixedHessian

/-!
# Second derivatives of the energy in disc directions
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall.MoserTrudinger

open KEBallProbe

/-- Signed Monge–Ampère energy of each fiber over the disc. -/
noncomputable def fiberEnergy {n : ℕ} (u : E n × E 1 → ℝ) (w : E 1) : ℝ :=
  signedSmoothEnergy (fun z => u (z, w))

theorem productComplexHessian_contDiff {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (i j : Fin n ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun p : E n × E 1 => productComplexHessian u p.1 p.2 i j) := by
  have hf : ContDiff ℝ ∞ (fun p => (u p : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  exact contDiff_iff_contDiffAt.mpr fun p =>
    smoothAt_dz (smoothAt_dz hf.contDiffAt _ _) _ _

/-- The signed fiber energy is smooth for a smooth family. -/
theorem fiberEnergy_contDiff {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (fiberEnergy u) := by
  let H (p : E 1 × E n) := complexHessian (fun y => u (y, p.1)) p.2
  have hH (i j : Fin n) : ContDiff ℝ ∞ (fun p => H p i j) := by
    have h := (productComplexHessian_contDiff hu (Sum.inl i) (Sum.inl j)).comp
      (contDiff_snd.prodMk contDiff_fst : ContDiff ℝ ∞ (fun p : E 1 × E n => (p.2, p.1)))
    simp_rw [Function.comp_def, productComplexHessian_fiber hu] at h
    exact h
  have hD : ContDiff ℝ ∞ (fun p => (H p).det) := by
    simp_rw [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    exact contDiff_const.mul (contDiff_prod fun i _ => hH (σ i) i)
  have hF : ContDiff ℝ ∞ (fun p : E 1 × E n => u (p.2, p.1) * (H p).det.re) :=
    (hu.comp (contDiff_snd.prodMk contDiff_fst)).mul (Complex.reCLM.contDiff.comp hD)
  exact (contDiff_fiberIntegral hn hF).div_const (n + 1 : ℝ)

private theorem affineDirection_hasDerivAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (w a : P) (t : ℝ) : HasDerivAt (fun s : ℝ => w + s • a) a t := by
  simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const a).const_add w

private theorem affine_second_derivative {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P → ℝ} (hF : ContDiff ℝ ∞ F) (w a : P) :
    deriv (deriv (fun t : ℝ => F (w + t • a))) 0 = fderiv ℝ (fderiv ℝ F) w a a := by
  have h₁ : deriv (fun t : ℝ => F (w + t • a)) = fun t => fderiv ℝ F (w + t • a) a := by
    funext t
    exact ((hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (affineDirection_hasDerivAt w a t)).deriv
  rw [h₁]
  have hF' : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hA : HasFDerivAt (fun p => fderiv ℝ F p a) ((fderiv ℝ (fderiv ℝ F) w).flip a) w := by
    simpa using ((hF'.differentiable (by simp) w).hasFDerivAt.clm_apply (hasFDerivAt_const a w))
  have hA₀ : HasFDerivAt (fun p => fderiv ℝ F p a) ((fderiv ℝ (fderiv ℝ F) w).flip a)
      (w + (0 : ℝ) • a) := by simpa only [zero_smul, add_zero] using hA
  exact (hA₀.comp_hasDerivAt 0 (affineDirection_hasDerivAt w a 0)).deriv

private theorem discAffineFamily_contDiff {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (w a : E 1) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => u (p.2, w + p.1 • a)) :=
  hu.comp (contDiff_snd.prodMk (contDiff_const.add (contDiff_fst.smul contDiff_const)))

private theorem parameterDerivative_discAffine {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (w a : E 1) :
    parameterDerivative (fun p : ℝ × E n => u (p.2, w + p.1 • a)) =
      fun p => discDirectionalDerivative u a (p.2, w + p.1 • a) := by
  funext p
  have h : HasDerivAt (fun s : ℝ => (p.2, w + s • a)) ((0 : E n), a) p.1 :=
    (hasFDerivAt_prodMk_right p.2 (w + p.1 • a)).comp_hasDerivAt p.1
      (affineDirection_hasDerivAt w a p.1)
  have h₁ := ((hu.differentiable (by simp) (p.2, w + p.1 • a)).hasFDerivAt.comp_hasDerivAt p.1 h)
  have h₂ := hasDerivAt_family_value (discAffineFamily_contDiff hu w a) p.1 p.2
  exact h₂.unique h₁

/-- Second derivative of the signed fiber energy along a real disc direction. -/
theorem realHessian_fiberEnergy_of_eventually_posDef {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ w z, z ∈ unitSphere n → u (z, w) = 0)
    (w a : E 1) (hP : ∀ᶠ w' in 𝓝 w, ∀ z ∈ unitBall n,
      (complexHessian (fun y => u (y, w')) z).PosDef) :
    realHessian (fiberEnergy u) w a a =
      ∫ z in unitBall n,
        realHessian (fun y => u (z, y)) w a a * (complexHessian (fun y => u (y, w)) z).det.re +
          discDirectionalDerivative u a (z, w) *
            cofactorContraction (fun y => u (y, w))
              (fun y => discDirectionalDerivative u a (y, w)) z ∂volume0 n := by
  let v : ℝ × E n → ℝ := fun p => u (p.2, w + p.1 • a)
  have hv : ContDiff ℝ ∞ v := discAffineFamily_contDiff hu w a
  have hPath : Tendsto (fun s : ℝ => w + s • a) (𝓝 0) (𝓝 w) := by
    simpa only [zero_smul, add_zero] using
      (affineDirection_hasDerivAt w a 0).continuousAt.tendsto
  have hPv : ∀ᶠ s : ℝ in 𝓝 0, ∀ z ∈ unitBall n,
      (complexHessian (fun y => v (s, y)) z).PosDef :=
    hPath.eventually hP
  have h := (hasDerivAt_deriv_familyEnergy hn hv
    (fun s z hz => h0 (w + s • a) z hz) 0 hPv).deriv
  change deriv (deriv (fun s : ℝ => fiberEnergy u (w + s • a))) 0 = _ at h
  rw [affine_second_derivative (fiberEnergy_contDiff hn hu)] at h
  have hD : parameterDerivative v = fun p =>
      discDirectionalDerivative u a (p.2, w + p.1 • a) :=
    parameterDerivative_discAffine hu w a
  have hDD (z : E n) : parameterDerivative (parameterDerivative v) (0, z) =
      realHessian (fun y => u (z, y)) w a a := by
    have h' := (hasDerivAt_family_value (parameterDerivative_contDiff hv) 0 z).deriv
    have h₁ : deriv (fun s : ℝ => u (z, w + s • a)) =
        fun s => parameterDerivative v (s, z) :=
      funext fun s => (hasDerivAt_family_value hv s z).deriv
    have hslice : ContDiff ℝ ∞ (fun y => u (z, y)) :=
      hu.comp (contDiff_const.prodMk contDiff_id)
    rw [← h₁, affine_second_derivative hslice] at h'
    exact h'.symm
  simp only [hDD] at h
  simpa only [realHessian, hD, v, zero_smul, add_zero] using h

theorem realHessian_fiberEnergy {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ w z, z ∈ unitSphere n → u (z, w) = 0)
    (hP : ∀ w ∈ unitBall 1, ∀ z ∈ unitBall n,
      (complexHessian (fun y => u (y, w)) z).PosDef)
    (w a : E 1) (hw : w ∈ unitBall 1) :
    realHessian (fiberEnergy u) w a a =
      ∫ z in unitBall n,
        realHessian (fun y => u (z, y)) w a a * (complexHessian (fun y => u (y, w)) z).det.re +
          discDirectionalDerivative u a (z, w) *
            cofactorContraction (fun y => u (y, w))
              (fun y => discDirectionalDerivative u a (y, w)) z ∂volume0 n :=
  realHessian_fiberEnergy_of_eventually_posDef hn hu h0 w a
    (Filter.Eventually.mono (isOpen_ball.mem_nhds hw) hP)

end KEBall.MoserTrudinger
