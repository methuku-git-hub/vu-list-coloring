module
public import Vu.ConditionedOffers
public import Vu.RevisedEvents
public import Vu.RevisedRemaining
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- Lemma 6.4 with the actual mark probabilities and retained weights.
Integrating over the exposed marks gives the joint bad-test probability. -/
public theorem state_offer_tail (ν p τ K cap A : ℝ) (ha : 0 < a) (hp : 0 < p) (hpν : p ≤ ν)
    (hν : ν ≤ 1/32) (hpa : p = a*ν) (hτ : τ ≤ 1) (hc : 0 ≤ cap) (hA : 0 ≤ A)
    (hM : 1 ≤ M) (hk : 0 < k) (hD : 0 < D) (hdeg : ∀ y, G.degree y ≤ D)
    (hbounds : RoundBounds s d.tests a b τ K)
    (h₀ : ∀ c y, 0 ≤ markProb s p c y) (h₁ : ∀ c y, markProb s p c y ≤ 1/M)
    (hmax : ∀ c y, markProb s p c y ≤ A/D) (hmark : ∀ c y, markProb s p c y ≤ ν*p)
    (x : V) (c : C) (i : Option (Finset V)) (hi : i ∈ indices d x)
    (hL : 0 < threshold (testCoeff V a b i) k τ p b ν) :
    let q := fun e => markLaw (fun y => activation (markProb s p e y)) (fun y => (activation_odds _ (h₀ e y)).1) (fun y => (activation_odds _ (h₀ e y)).2.1.le)
    let l := threshold (testCoeff V a b i) k τ p b ν
    let u := ν*p*l
    (FiniteLaw.independent q).chance (badTest d s a ν p τ cap x c i) ≤
      Real.exp (-u^2/(2*((1+cap^2*(1+A)*p)*D))) := by
  classical
  intro q l u
  let π := markProb s p
  let T := testSet G x i
  let others := (univ.erase c).toList
  let w (v : V → Bool) (y : V) := if y ∈ T then kept d s a ν p τ cap c v y else 0
  let pass (v : V → Bool) := (∑ y ∈ T, raw d s p c v y) ≤ l
  have hb := kept_bounds d s a ν p τ cap hc hM c (fun z => ⟨h₀ c z,h₁ c z⟩)
  have hw v y : 0 ≤ w v y := by dsimp [w]; split <;> first | exact (hb v y).2.1 | rfl
  have hout v y (hy : y ∉ T) : w v y = 0 := by simp [w,hy]
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hsum (y : V) : (∑ e, π e y) = if s.color y = none then p else 0 := by
    simp only [π,markProb,←sum_div,←mul_sum]
    split
    next h => rw [s.total y h]; field_simp
    next h => simp [s.painted y _ h]
  have hlist (y : V) : (others.map (fun e => π e y)).sum + π c y = ∑ e, π e y := by
    rw [show (others.map (fun e => π e y)).sum = ∑ e ∈ univ.erase c, π e y by
      exact Finset.sum_map_toList ..]
    exact sum_erase_add _ _ (mem_univ _)
  have hT := (card_le_card (index_subset d x i hi)).trans ((G.card_neighborFinset_eq_degree x).le.trans (hdeg x))
  have hn (e : C) (y : V) (hy : 0 < π e y) : ∑ z ∈ G.neighborFinset y, π e z ≤ ν := by
    have hy' : 0 < s.weight y e := lt_of_le_of_ne (s.nonneg _ _) (by intro h; simp [π,markProb,←h] at hy)
    rw [show (∑ z ∈ G.neighborFinset y, π e z) = p*(∑ z ∈ G.neighborFinset y, s.weight z e)/k by
      simp [π,markProb,←sum_div,←mul_sum]]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbounds.2 y e hy').2 hp.le) hk'.le).trans
    have he : p*(1/a*(k:ℝ)*τ)/k = ν*τ := by rw [hpa]; field_simp
    rw [he]; simpa using mul_le_mul_of_nonneg_left hτ (hp.le.trans hpν)
  have htail := unexpose_remaining_tail G q c T w hw hout pass ((1-(1-4*ν)*p)*l) _ (Real.exp_pos _).le (by
    intro v hv
    apply fixed_offer_tail G T others D π h₀ (w v) p ν l A cap
      hD hT hp hpν hν hL hA hc (hw v) (fun y hy => by simpa [w,hy] using (hb v y).2.2.2)
      (hout v)
    · change (∑ y, w v y) ≤ l
      simp only [w,←sum_filter,filter_mem_eq_inter,univ_inter]
      exact (sum_le_sum (fun y _ => (hb v y).2.2.1)).trans hv
    · exact fun e _ y _ => hmax e y
    · intro y _
      have hh := hlist y
      rw [hsum] at hh
      split at hh <;> linarith only [hh,h₀ c y,hp]
    · intro y hy
      have hyT : y ∈ T := by by_contra h; simp [w,h] at hy
      have hcol : s.color y = none := by
        by_contra h
        simp [w,hyT,kept_zero d s a ν p τ cap c v y (s.painted y c h)] at hy
      have hh := hlist y
      rw [hsum,if_pos hcol] at hh
      linarith only [hh,hmark c y]
    · exact fun e _ y _ hy => hn e y hy)
  apply le_trans _ htail
  apply (FiniteLaw.independent q).mean_mono
  intro ω
  have he : (∑ y ∈ T, if accepted G ω y = none then w (ω c) y else 0) =
      ∑ y ∈ T, remainingWeight (G := G) (fun z e => kept d s a ν p τ cap e (ω e) z) ω c y :=
    sum_congr rfl (fun y hy => by simp only [w,if_pos hy,remainingWeight])
  by_cases h : badTest d s a ν p τ cap x c i ω
  · have hh : (1-(1-4*ν)*p)*l < ∑ y ∈ T, if accepted G ω y = none then w (ω c) y else 0 := by rw [he]; exact h.2
    simp [h,show pass (ω c) from h.1,hh]
  · simp [h]; split <;> norm_num
end Vu.Revised
