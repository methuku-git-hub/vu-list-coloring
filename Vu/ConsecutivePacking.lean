module
public import Vu.HardTests
namespace Vu.Revised
open Finset
variable {V : Type*} [DecidableEq V]

/-- Process a fixed list from right to left. Its first group is open and
receives the next part whenever the union still fits. -/
private theorem pack_list (s : ℝ) (L : List (Finset V)) (hL : ∀ U ∈ L, (U.card:ℝ) ≤ s) :
    ∃ B : List (Finset V), (∀ U ∈ L, ∃ T ∈ B, U ⊆ T) ∧
      B.toFinset.biUnion id = L.toFinset.biUnion id ∧
      (∀ U ∈ B, (U.card:ℝ) ≤ s) ∧ (B.map card).sum ≤ (L.map card).sum ∧
      B.IsChain (fun P Q => s < (P.card:ℝ)+Q.card) := by
  classical
  induction L with
  | nil => exact ⟨[],by simp⟩
  | cons A L ih =>
    obtain ⟨B,hcov,hu,hsize,hcost,hsep⟩ := ih (fun U h => hL U (List.mem_cons_of_mem _ h))
    have hA := hL A List.mem_cons_self
    cases B with
    | nil =>
      refine ⟨[A],?_,?_,by simpa using hA,by simp,by simp⟩
      · intro U h
        rcases List.mem_cons.mp h with rfl|h
        · exact ⟨_,by simp,Subset.rfl⟩
        · simpa using hcov U h
      · simpa [←hu]
    | cons T B =>
      by_cases hfit : ((A ∪ T).card:ℝ) ≤ s
      · refine ⟨(A ∪ T)::B,?_,?_,?_,?_,?_⟩
        · intro U h
          rcases List.mem_cons.mp h with rfl|h
          · exact ⟨_,List.mem_cons_self,subset_union_left⟩
          · obtain ⟨Z,hZ,hsub⟩ := hcov U h
            rcases List.mem_cons.mp hZ with rfl|hZ
            · exact ⟨_,List.mem_cons_self,hsub.trans subset_union_right⟩
            · exact ⟨_,List.mem_cons_of_mem _ hZ,hsub⟩
        · simpa [←hu,union_assoc]
        · intro U h
          rcases List.mem_cons.mp h with rfl|h
          · exact hfit
          · exact hsize _ (List.mem_cons_of_mem _ h)
        · simp only [List.map_cons,List.sum_cons] at hcost ⊢
          have := card_union_le A T
          omega
        · cases B with
          | nil => simp
          | cons Z B =>
            obtain ⟨ht,hB⟩ := List.isChain_cons_cons.mp hsep
            exact List.isChain_cons_cons.mpr ⟨ht.trans_le (add_le_add_left
              (Nat.cast_le.mpr (card_le_card (subset_union_right : T ⊆ A ∪ T))) _),hB⟩
      · refine ⟨A::T::B,?_,?_,?_,?_,?_⟩
        · intro U h
          rcases List.mem_cons.mp h with rfl|h
          · exact ⟨_,List.mem_cons_self,Subset.rfl⟩
          · obtain ⟨Z,hZ,hsub⟩ := hcov U h
            exact ⟨_,List.mem_cons_of_mem _ hZ,hsub⟩
        · simpa [←hu]
        · exact List.forall_mem_cons.mpr ⟨hA,hsize⟩
        · simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add_left hcost A.card
        · exact List.isChain_cons_cons.mpr ⟨(lt_of_not_ge hfit).trans_le
            (by exact_mod_cast card_union_le A T),hsep⟩

/-- Pair successive blocks. Every complete pair accounts for more than s
vertices, and one last block may be unpaired. -/
private theorem length_budget (s : ℝ) (hs : 0 < s) : ∀ (B : List (Finset V)),
    B.IsChain (fun P Q => s < (P.card:ℝ)+Q.card) →
    (B.length:ℝ)*s ≤ 2*((B.map card).sum:ℕ)+s
  | [], _ => by simp [hs.le]
  | [A], _ => by simp
  | A::T::B, h => by
    obtain ⟨hat,hrest⟩ := List.isChain_cons_cons.mp h
    have ih := length_budget s hs B hrest.tail
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one] at *
    linarith

public theorem pack_neighbor_groups (F : Finset (Finset V)) (D : ℕ) (s : ℝ)
    (hs : 0 < s) (hsize : ∀ S ∈ F, (S.card:ℝ) ≤ s) (htotal : ∑ S ∈ F, S.card ≤ D) :
    ∃ B : Finset (Finset V), (∀ S ∈ F, ∃ T ∈ B, S ⊆ T) ∧
      B.biUnion id = F.biUnion id ∧ (∀ S ∈ B, (S.card:ℝ) ≤ s) ∧ (B.card:ℝ) ≤ 2*D/s+1 := by
  classical
  obtain ⟨B,hcov,hu,hbound,hcost,hsep⟩ := pack_list s F.toList (by simpa using hsize)
  refine ⟨B.toFinset,by simpa using hcov,by simpa using hu,by simpa using hbound,?_⟩
  have cost : (B.map card).sum ≤ D := hcost.trans (by
    rw [←List.sum_toFinset _ F.nodup_toList,F.toList_toFinset]; exact htotal)
  have len := length_budget s hs B hsep
  have hc : B.toFinset.card ≤ B.length := List.toFinset_card_le ..
  have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc : (B.toFinset.card:ℝ) ≤ B.length) hs.le
  rw [←div_self hs.ne',←add_div,le_div_iff₀ hs]
  linarith [show ((B.map card).sum:ℝ) ≤ D from Nat.cast_le.mpr cost]
end Vu.Revised
