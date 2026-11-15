import KEBall.DirichletFieldProductInterpolation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The scalar size used by the discrete estimates is the genuine L2
seminorm, with triangle inequalities for finite sums. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open MeasureTheory Metric Set
open scoped BigOperators ENNReal

namespace KEBall

theorem dirichletLpSize_two_eq_lpNorm {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
    dirichletLpSize f 2 = lpNorm f 2 ((volume0 n).restrict (unitBall n)) := by
  have hMeas := (dirichlet_memLp_of_continuousOn hn hf 2).aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) hMeas]
  simp only [dirichletLpSize, ENNReal.toReal_ofNat, Real.norm_eq_abs, one_div]

theorem dirichletLpSize_two_add_le {n : ℕ} (hn : 0 < n)
    {f g : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n)) :
    dirichletLpSize (f + g) 2 ≤ dirichletLpSize f 2 + dirichletLpSize g 2 := by
  rw [dirichletLpSize_two_eq_lpNorm hn (hf.add hg),
    dirichletLpSize_two_eq_lpNorm hn hf, dirichletLpSize_two_eq_lpNorm hn hg]
  exact lpNorm_add_le (dirichlet_memLp_of_continuousOn hn hf 2) (by norm_num)

theorem dirichletLpSize_two_finset_sum_le {n : ℕ} {ι : Type*} (hn : 0 < n)
    (s : Finset ι) (F : ι → E n → ℝ)
    (hF : ∀ i ∈ s, ContinuousOn (F i) (closedUnitBall n)) :
    dirichletLpSize (fun x => ∑ i ∈ s, F i x) 2 ≤
      ∑ i ∈ s, dirichletLpSize (F i) 2 := by
  rw [dirichletLpSize_two_eq_lpNorm hn (continuousOn_finsetSum s hF)]
  have h := lpNorm_sum_le (fun i hi => dirichlet_memLp_of_continuousOn hn (hF i hi) 2)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hSum : (∑ i ∈ s, F i) = (fun x => ∑ i ∈ s, F i x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hSum] at h
  exact h.trans_eq (Finset.sum_congr rfl (fun i hi => (dirichletLpSize_two_eq_lpNorm hn (hF i hi)).symm))

theorem dirichletLpSize_two_list_sum_le {n : ℕ} {ι : Type*} (hn : 0 < n)
    (L : List ι) (F : ι → E n → ℝ)
    (hF : ∀ i ∈ L, ContinuousOn (F i) (closedUnitBall n)) :
    dirichletLpSize (fun x => (L.map (fun i => F i x)).sum) 2 ≤
      (L.map (fun i => dirichletLpSize (F i) 2)).sum := by
  have hCont (L' : List ι) (hL' : ∀ i ∈ L', ContinuousOn (F i) (closedUnitBall n)) :
      ContinuousOn (fun x => (L'.map (fun i => F i x)).sum) (closedUnitBall n) := by
    induction L' with
    | nil => simpa using (continuousOn_const (s := closedUnitBall n) (c := (0 : ℝ)))
    | cons i L' ih =>
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using
        (hL' i (List.mem_cons_self)).add (ih (fun j hj => hL' j (List.mem_cons_of_mem i hj)))
  induction L with
  | nil => simp [dirichletLpSize]
  | cons i L ih =>
    have hTail : ∀ j ∈ L, ContinuousOn (F j) (closedUnitBall n) :=
      fun j hj => hF j (List.mem_cons_of_mem i hj)
    have h := dirichletLpSize_two_add_le hn (hF i List.mem_cons_self) (hCont L hTail)
    simpa only [List.map_cons, List.sum_cons, Pi.add_def] using
      h.trans (add_le_add le_rfl (ih hTail))

end KEBall
