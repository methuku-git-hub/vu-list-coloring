module
public import Vu.RoundOutcome
public import Vu.RevisedScalars
public import Vu.SuccessfulRound
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- A mark outcome avoiding the two types of bad events gives a state
satisfying (I1)-(I2) for round j+1 with the manuscript's exact caps.
The positivity restriction is on marks in the support of the product law. -/
public theorem state_of_successful_marks (ha : 0 < a) (ha₁ : a < 1) (hb : 0 < b) (hb₁ : b < 1)
    (hM : 1 ≤ M) (hk : 0 < k) (j : ℕ) (ω : C → V → Bool) :
    let ν := b/32
    let p := a*ν
    let τ := roundTau b p j
    let cap := cutoff a M ν p (Vu.Revised.cap a M ν p j)
    let w := fun x c => kept d s a ν p τ cap c (ω c) x
    (∀ x c, ω c x = true → 0 < s.weight x c) →
    (∀ c x, 0 ≤ markProb s p c x) → (∀ c x, markProb s p c x ≤ 1/M) →
    (∀ x, s.color x = none → k*(1-ν*p) ≤ ∑ c, w x c) →
    (∀ x c, 0 < s.weight x c → ∀ i ∈ indices d x,
      (∑ y ∈ testSet G x i, raw d s p c (ω c) y) ≤ threshold (testCoeff V a b i) k τ p b ν →
      ∑ y ∈ testSet G x i, remainingWeight (G := G) w ω c y ≤ (1-(1-4*ν)*p)*threshold (testCoeff V a b i) k τ p b ν) →
    ∃ s' : ColoringState G L k, (∀ x c, s.color x = some c → s'.color x = some c) ∧
      RoundBounds s' d.tests a b (roundTau b p (j+1)) (Vu.Revised.cap a M ν p (j+1)) := by
  classical
  intro ν p τ cap w hmark h₀ h₁ htot hrem
  have hn : 0 < ν := by dsimp [ν]; positivity
  have hp : 0 < p := mul_pos ha hn
  have hpν : p ≤ ν := by
    dsimp only [p]; exact (mul_le_mul_of_nonneg_right ha₁.le hn.le).trans_eq (one_mul _)
  have hcap : 0 < cap := by
    exact (cap_pos a M ν p j).trans_le (le_max_left ..)
  have hc := contraction b p ν hb hb₁ hp hpν rfl
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hw (x : V) (c : C) := kept_bounds d s a ν p τ cap hcap.le hM c (fun z => ⟨h₀ c z,h₁ c z⟩) (ω c) x
  let tot (x : V) := ∑ c, w x c
  have hden x (hx : extendedColor s ω x = none) : 0 < tot x :=
    (mul_pos hk' hc.1).trans_le (htot x ((extended_none_iff s ω x).mp hx).1)
  obtain ⟨s',hcolor,hweight,hext⟩ := extend_coloring_state s ω w hmark (fun x c => (hw x c).2.1)
    (fun x c => kept_zero d s a ν p τ cap c (ω c) x)
    (fun x y c h => kept_zero_neighbor d s a ν p τ cap c (ω c) x y h) hden
  let factor := 1/(1-ν*p)
  have hfac : 0 ≤ factor := div_nonneg zero_le_one hc.1.le
  have hrow (x : V) (c : C) : s'.weight x c ≤ factor*remainingWeight (G := G) w ω c x := by
    rw [hweight]
    split
    next h =>
      obtain ⟨ho,hn⟩ := (extended_none_iff s ω x).mp h
      simp only [remainingWeight,hn,ite_true]
      have hfrac : (k:ℝ)/tot x ≤ factor := (div_le_div_iff₀ (hden x h) hc.1).mpr (by simpa using htot x ho)
      exact (by ring : (k:ℝ)*w x c/tot x = ((k:ℝ)/tot x)*w x c).le.trans
        (mul_le_mul_of_nonneg_right hfrac (hw x c).2.1)
    next =>
      apply mul_nonneg hfac
      dsimp only [remainingWeight]; split <;> first | exact (hw x c).2.1 | exact le_rfl
  refine ⟨s',hext,(bounds_iff d s' a _ _).mpr ⟨?_,?_⟩⟩
  · intro x c
    apply (hrow x c).trans
    have hwn : remainingWeight (G := G) w ω c x ≤ cap := by
      dsimp only [remainingWeight]; split <;> first | exact (hw x c).2.2.2 | exact hcap.le
    exact mul_le_mul hc.2.1 hwn (by dsimp only [remainingWeight]; split <;> first | exact (hw x c).2.1 | exact le_rfl) (by norm_num)
  · intro x c hpos i hi
    have hn : w x c ≠ 0 := by intro he; rw [hweight] at hpos; simp [he] at hpos
    have hold : 0 < s.weight x c := lt_of_le_of_ne (s.nonneg x c) (fun he =>
      hn (kept_zero d s a ν p τ cap c (ω c) x he.symm))
    have hpass : passes d s a ν p τ c (ω c) x := by
      by_contra hp'; exact hn (by simp [w,kept,hp'])
    have hr := hrem x c hold i hi (hpass i hi)
    let m := testCoeff V a b i
    have hm : 0 ≤ m := by cases i <;> dsimp [m,testCoeff] <;> first | positivity | linarith
    have hτ : 0 < τ := Real.exp_pos _
    have hscale : 0 ≤ m*k*τ := mul_nonneg (mul_nonneg hm hk'.le) hτ.le
    apply (sum_le_sum (fun y _ => hrow y c)).trans
    rw [←mul_sum,round_tau_succ]
    apply (mul_le_mul_of_nonneg_left hr hfac).trans
    change factor*((1-(1-4*ν)*p)*threshold m k τ p b ν) ≤ m*k*(τ*Real.exp (-b*p/2))
    dsimp only [threshold,factor,τ]
    linarith only [mul_le_mul_of_nonneg_left hc.2.2 hscale]
end Vu.Revised
