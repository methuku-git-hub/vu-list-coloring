module
public import Vu.ExposeColor
public import Vu.FixedColorTail
public import Vu.RoundEvents
namespace Vu
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Integrating after fixing color c gives a finite independent union over
the remaining colors. Every vertex in that union has accepted an offer.
The law of c is arbitrary, including atoms of zero mass. -/
public theorem unexpose_remaining_tail (q : C → FiniteLaw (V → Bool)) (c : C) (T : Finset V)
    (w : (V → Bool) → V → ℝ) (hw : ∀ v x, 0 ≤ w v x) (hout : ∀ v x, x ∉ T → w v x = 0)
    (pass : (V → Bool) → Prop) (B rate : ℝ) (hr : 0 ≤ rate)
    (h : ∀ v, pass v →
      coverageAverage ((univ.erase c).toList.map fun j => (q j).map (offerSet G T))
        (fun S => if B < setWeight (w v) univ-setWeight (w v) S then 1 else 0) ∅ ≤ rate) :
    (FiniteLaw.independent q).chance (fun ω => pass (ω c) ∧
      B < ∑ x ∈ T, (if accepted G ω x = none then w (ω c) x else 0)) ≤ rate := by
  classical
  let μ := FiniteLaw.independent q
  let E (ω : C → V → Bool) := pass (ω c) ∧ B < ∑ x ∈ T, if accepted G ω x = none then w (ω c) x else 0
  let ind (ω : C → V → Bool) : ℝ := if E ω then 1 else 0
  have hc : μ.chance E = μ.mean ind := by
    unfold FiniteLaw.chance
    congr 1
    funext ω
    by_cases he : E ω <;> simp [ind,he]
  change μ.chance E ≤ rate
  rw [hc]
  rw [FiniteLaw.expose_coordinate q c ind]
  have hconst := (q c).mean_const rate
  apply le_trans _ hconst.le
  apply (q c).mean_mono
  intro v
  by_cases hpass : pass v
  swap
  · have hem (ω : C → V → Bool) : ind (Function.update ω c v) = 0 := by simp [ind,E,hpass]
    simpa only [hem,FiniteLaw.mean_const] using hr
  let U (ω : C → V → Bool) := (univ.erase c).biUnion (fun j => offerSet G T (ω j))
  let bad (S : Finset V) : ℝ := if B < setWeight (w v) univ-setWeight (w v) S then 1 else 0
  have hu := mean_union_offers q (fun _ => offerSet G T) (univ.erase c).toList (Finset.nodup_toList _) bad ∅
  have hu' : μ.mean (fun ω => bad (U ω)) ≤ rate := by
    apply le_trans _ (h v hpass)
    apply le_of_eq
    simpa [U,μ,bad] using hu
  apply le_trans _ hu'
  apply μ.mean_mono
  intro ω
  let ω' := Function.update ω c v
  have hmem (x : V) (hx : x ∈ U ω) : accepted G ω' x ≠ none := by
    obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
    have hne := (mem_erase.mp hj).1
    have ho : x ∈ offerSet G univ (ω' j) := by
      obtain ⟨_,hm⟩ := mem_filter.mp hx
      simpa [offerSet,ω',hne] using hm
    exact fun hn => (no_accept_iff ω' x).mp hn j ho
  have hcmp : (∑ x ∈ T, if accepted G ω' x = none then w v x else 0) ≤
      setWeight (w v) univ-setWeight (w v) (U ω) := by
    have eq : setWeight (w v) univ-setWeight (w v) (U ω) = ∑ x, if x ∈ U ω then 0 else w v x := by
      rw [setWeight,setWeight,←sum_sdiff_eq_sub (subset_univ (U ω))]
      conv_rhs => enter [2,x]; rw [←ite_not]
      rw [←sum_filter]
      congr 1
      ext x
      simp
    rw [eq]
    calc
      _ ≤ ∑ x ∈ T, if x ∈ U ω then 0 else w v x := by
        apply sum_le_sum; intro x _
        by_cases hx : x ∈ U ω
        · simp [hx,hmem x hx]
        · by_cases hn : accepted G ω' x = none <;> simp [hx,hn,hw]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => by split <;> first | exact hw v x | exact le_rfl)
  change ind ω' ≤ bad (U ω)
  by_cases hb : E ω'
  · have hb' : B < ∑ x ∈ T, if accepted G ω' x = none then w v x else 0 := by simpa only [ω',Function.update_self] using hb.2
    simp [ind,bad,hb,hb'.trans_le hcmp]
  · simp only [ind,if_neg hb,bad]; split <;> norm_num
end Vu
