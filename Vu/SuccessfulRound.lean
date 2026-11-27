module
public import Vu.RoundOutcome
namespace Vu
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : Decomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- The contribution of vertices that received no offer, before (W4). -/
@[expose] public noncomputable def remainingWeight (w : V → C → ℝ) (ω : C → V → Bool) (c : C) (x : V) :=
  if accepted G ω x = none then w x c else 0

/-- A mark outcome avoiding the two types of bad events gives a state
satisfying (I1)-(I2) for round j+1 with the manuscript's exact caps.
The positivity restriction is on marks in the support of the product law. -/
public theorem state_of_successful_marks (ha : 0 < a) (ha₁ : a < 1) (hb : 0 < b) (hb₁ : b < 1)
    (hM : 0 ≤ M) (hk : 0 < k) (j : ℕ) (ω : C → V → Bool) :
    let ν := roundNu b
    let p := a*ν
    let τ := roundTau b p j
    let cap := clipCap a M ν p (roundCap a M ν p j)
    let w := fun x c => keptWeight d s a ν p τ cap c (ω c) x
    (∀ x c, ω c x = true → 0 < s.weight x c) →
    (∀ c x, 0 ≤ markProb s p c x) → (∀ c x, markProb s p c x < 1) →
    (∀ c x, M*(markProb s p c x/(1-markProb s p c x)) ≤ 1) →
    (∀ x, s.color x = none → k*(1-ν*p) ≤ ∑ c, w x c) →
    (∀ x c, 0 < s.weight x c → ∀ i ∈ testIndices d x,
      (∑ y ∈ testSet G x i, preWeight d s p cap c (ω c) y) ≤ testThreshold (testCoeff V a b i) k τ ν p b →
      ∑ y ∈ testSet G x i, remainingWeight (G := G) w ω c y ≤ (1-(1-5*ν)*p)*testThreshold (testCoeff V a b i) k τ ν p b) →
    ∃ s' : ColoringState G L k, (∀ x c, s.color x = some c → s'.color x = some c) ∧
      RoundBounds s' d.tests a b (roundTau b p (j+1)) (roundCap a M ν p (j+1)) := by
  classical
  intro ν p τ cap w hmark h₀ h₁ hsmall htot hrem
  obtain ⟨hn,hn',hnb⟩ := round_nu_bounds hb
  have hp : 0 < p := mul_pos ha hn
  have hpν : p ≤ ν := by
    dsimp only [p]; exact (mul_le_mul_of_nonneg_right ha₁.le hn.le).trans_eq (one_mul _)
  have hcap : 0 < cap := by
    dsimp only [cap,clipCap]
    have hK := round_cap_pos a M ν p hn hp j
    positivity
  have hc := round_contraction b p ν hb hb₁ hp hpν hn' hnb j
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hw (x : V) (c : C) := kept_weight_bounds d s a ν p τ cap hcap.le hM c (h₀ c) (h₁ c) (hsmall c) (ω c) x
  let tot (x : V) := ∑ c, w x c
  have hden x (hx : extendedColor s ω x = none) : 0 < tot x :=
    (mul_pos hk' hc.1).trans_le (htot x ((extended_none_iff s ω x).mp hx).1)
  obtain ⟨s',hcolor,hweight,hext⟩ := extend_coloring_state s ω w hmark (fun x c => (hw x c).1)
    (fun x c => kept_zero_of_old_zero d s a ν p τ cap hcap.le c (ω c) x)
    (fun x y c h => kept_zero_of_neighbor_mark d s a ν p τ cap hcap.le c (ω c) x y h) hden
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
        (mul_le_mul_of_nonneg_right hfrac (hw x c).1)
    next =>
      apply mul_nonneg hfac
      dsimp only [remainingWeight]; split <;> first | exact (hw x c).1 | exact le_rfl
  refine ⟨s',hext,(round_bounds_iff_indexed d s' a _ _).mpr ⟨?_,?_⟩⟩
  · intro x c
    apply (hrow x c).trans
    have hwn : remainingWeight (G := G) w ω c x ≤ cap := by
      dsimp only [remainingWeight]; split <;> first | exact (hw x c).2.1.trans (hw x c).2.2 | exact hcap.le
    exact mul_le_mul hc.2.1 hwn (by dsimp only [remainingWeight]; split <;> first | exact (hw x c).1 | exact le_rfl) (by norm_num)
  · intro x c hpos i hi
    have hn : w x c ≠ 0 := by intro he; rw [hweight] at hpos; simp [he] at hpos
    have hold : 0 < s.weight x c := lt_of_le_of_ne (s.nonneg x c) (fun he =>
      hn (kept_zero_of_old_zero d s a ν p τ cap hcap.le c (ω c) x he.symm))
    have hpass : passes d s a ν p τ cap c (ω c) x := by
      by_contra hp'; exact hn (if_neg hp' : keptWeight d s a ν p τ cap c (ω c) x = 0)
    have hr := hrem x c hold i hi (hpass i hi)
    let m := testCoeff V a b i
    have hm : 0 ≤ m := by cases i <;> dsimp [m,testCoeff] <;> first | positivity | linarith
    have hτ : 0 < τ := Real.exp_pos _
    have hscale : 0 ≤ m*k*τ := mul_nonneg (mul_nonneg hm hk'.le) hτ.le
    apply (sum_le_sum (fun y _ => hrow y c)).trans
    rw [←mul_sum,round_tau_succ]
    apply (mul_le_mul_of_nonneg_left hr hfac).trans
    change factor*((1-(1-5*ν)*p)*testThreshold m k τ ν p b) ≤ m*k*(τ*Real.exp (-b*p/2))
    dsimp only [testThreshold,factor]
    linarith only [mul_le_mul_of_nonneg_left hc.2.2 hscale]
end Vu
