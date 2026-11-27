module

public import Vu.OmittedNeighbors

namespace Vu
open Finset

/-- Merge whole groups of neighbors into tests of size at most s.
The size budget D is the sum of the input group sizes. In particular the
number of tests is independent of the number of labels through a vertex. -/
public theorem pack_neighbor_groups {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (D : ℕ) (s : ℝ) (hs : 0 < s) (hsize : ∀ S ∈ F, (S.card : ℝ) ≤ s)
    (htotal : ∑ S ∈ F, S.card ≤ D) :
    ∃ B : Finset (Finset V), (∀ S ∈ F, ∃ T ∈ B, S ⊆ T) ∧
      B.biUnion id = F.biUnion id ∧ (∀ S ∈ B, (S.card : ℝ) ≤ s) ∧
      (B.card : ℝ) ≤ 2*D/s+1 := by
  classical
  -- Optimize over all feasible coarsenings, including the original family.
  let candidates := (F.biUnion id).powerset.powerset.filter fun B =>
    (∀ S ∈ F, ∃ T ∈ B, S ⊆ T) ∧ B.biUnion id = F.biUnion id ∧
    (∀ T ∈ B, (T.card : ℝ) ≤ s) ∧ ∑ T ∈ B, T.card ≤ D
  have eligible (B : Finset (Finset V)) (hh : (∀ S ∈ F, ∃ T ∈ B, S ⊆ T) ∧
      B.biUnion id = F.biUnion id ∧ (∀ T ∈ B, (T.card : ℝ) ≤ s) ∧ ∑ T ∈ B, T.card ≤ D) :
      B ∈ candidates := by
    apply mem_filter.mpr ⟨mem_powerset.mpr ?_, hh⟩
    intro T ht
    exact mem_powerset.mpr (fun x hx => hh.2.1 ▸ mem_biUnion.mpr ⟨T, ht, hx⟩)
  have hi : F ∈ candidates := eligible F ⟨fun S h => ⟨S,h,Subset.rfl⟩,rfl,hsize,htotal⟩
  obtain ⟨B, hB, hmin⟩ := candidates.exists_min_image card ⟨F,hi⟩
  obtain ⟨hcover, heq, hbound, hsum⟩ := (mem_filter.mp hB).2
  refine ⟨B,hcover,heq,hbound,?_⟩
  have separated (P Q : Finset V) (hp : P ∈ B) (hq : Q ∈ B) (hne : P ≠ Q) :
      s < (P.card : ℝ) + Q.card := by
    by_contra! small
    let R := (B.erase P).erase Q
    let U := P ∪ Q
    let C := insert U R
    have hq' := mem_erase.mpr ⟨Ne.symm hne,hq⟩
    have hrep : ∀ T ∈ B, ∃ S ∈ C, T ⊆ S := by
      intro T ht
      by_cases h₁ : T = P
      · exact ⟨U, mem_insert_self .., h₁ ▸ subset_union_left⟩
      by_cases h₂ : T = Q
      · exact ⟨U, mem_insert_self .., h₂ ▸ subset_union_right⟩
      exact ⟨T,mem_insert_of_mem (mem_erase.mpr ⟨h₂, mem_erase.mpr ⟨h₁,ht⟩⟩), Subset.rfl⟩
    have hc : C ∈ candidates := by
      apply eligible
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro S hs'
        obtain ⟨T, ht, hST⟩ := hcover S hs'
        obtain ⟨W, hw, hTW⟩ := hrep T ht
        exact ⟨W, hw, hST.trans hTW⟩
      · rw [← heq]
        ext x
        simp only [mem_biUnion, id_eq]
        constructor
        · rintro ⟨T,ht,hx⟩
          rcases mem_insert.mp ht with rfl | hT
          · exact (mem_union.mp hx).elim (fun h => ⟨P,hp,h⟩) (fun h => ⟨Q,hq,h⟩)
          · exact ⟨T, mem_of_mem_erase (mem_of_mem_erase hT),hx⟩
        · rintro ⟨T, ht, hx⟩
          obtain ⟨W, hw, hTW⟩ := hrep T ht
          exact ⟨W,hw,hTW hx⟩
      · intro T ht
        rcases mem_insert.mp ht with rfl | hT
        · exact (Nat.cast_le.mpr (card_union_le P Q)).trans (by simpa using small)
        · exact hbound T (mem_of_mem_erase (mem_of_mem_erase hT))
      · have h₁ := sum_erase_add B card hp
        have h₂ := sum_erase_add (B.erase P) card hq'
        have hu := card_union_le P Q
        by_cases hm : U ∈ R
        · simp only [C, insert_eq_of_mem hm]
          dsimp [R] at hm ⊢
          omega
        · rw [sum_insert hm]
          dsimp [U, R]
          omega
    have hlt : C.card < B.card := by
      have h₁ := card_erase_add_one hp
      have h₂ := card_erase_add_one hq'
      have hi := card_insert_le U R
      dsimp [C, R] at *
      omega
    exact (not_lt_of_ge (hmin C hc)) hlt
  let small := B.filter fun P => (P.card : ℝ) ≤ s/2
  have hsmall : small.card ≤ 1 := by
    apply card_le_one.mpr
    intro P hp Q hq
    by_contra hne
    have h := separated P Q (mem_filter.mp hp).1 (mem_filter.mp hq).1 hne
    linarith [(mem_filter.mp hp).2, (mem_filter.mp hq).2]
  have hlarge : ((B \ small).card : ℝ) * (s/2) ≤ (D : ℝ) := by
    have h := sum_le_sum (s := B \ small) (f := fun _ => s/2) (g := fun P => (P.card : ℝ)) (by
      intro P hP
      have hh := mem_sdiff.mp hP
      by_contra! hlt
      exact hh.2 (mem_filter.mpr ⟨hh.1,hlt.le⟩))
    have hsum' := sum_le_sum_of_subset (f := card) (sdiff_subset (s := B) (t := small))
    have htotal' : (∑ P ∈ B \ small, (P.card : ℝ)) ≤ D := by exact_mod_cast hsum'.trans hsum
    simpa using h.trans htotal'
  have hc := card_sdiff_add_card_eq_card (show small ⊆ B from filter_subset _ _)
  have hc' : ((B \ small).card : ℝ) + small.card = B.card := by exact_mod_cast hc
  have hm : ((B \ small).card : ℝ) ≤ 2*D/s := (le_div_iff₀ hs).mpr (by linarith)
  have h₁ : (small.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
  linarith

/-- The constants a, b, s, and R fixed at the start of Section 4 give (D1)
for the packed groups. Every original group stays inside one of the tests,
the property subsequently used to omit a whole group. -/
public theorem decomposition_neighbor_tests {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (D t : ℕ) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (ht : t ≤ D) (hD : 4 ≤ ε*D)
    (hgroup : ∀ S ∈ F, (S.card : ℝ) ≤ t+ε*D/2) (htotal : ∑ S ∈ F, S.card ≤ D) :
    let k := ⌊(t : ℝ)+ε*D⌋₊
    ε/2*D ≤ k ∧ (k : ℝ) ≤ 2*D ∧ ∃ B : Finset (Finset V),
      (∀ S ∈ F, ∃ U ∈ B, S ⊆ U) ∧ B.biUnion id = F.biUnion id ∧
      B.card ≤ ⌈4/ε⌉₊+2 ∧ ∀ U ∈ B, (U.card : ℝ) ≤ (1-ε/8)*k := by
  dsimp only
  let k := ⌊(t : ℝ)+ε*D⌋₊
  let s := (t : ℝ) + ε*D/2
  have hD₀ : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have ht₀ : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hfloor : (t : ℝ)+ε*D-1 < k := by
    have := Nat.lt_floor_add_one ((t : ℝ)+ε*D)
    dsimp [k]; linarith
  have htk : (t : ℝ) ≤ D := by exact_mod_cast ht
  have hk : (k : ℝ) ≤ 2*D := by
    have htop : (k : ℝ) ≤ (t : ℝ)+ε*D := Nat.floor_le (by positivity)
    linarith [mul_le_mul_of_nonneg_right hε₁ hD₀]
  have hs : 0 < s := by dsimp [s]; linarith
  obtain ⟨B, hb, hu, hcap, hcount⟩ := pack_neighbor_groups F D s hs hgroup htotal
  refine ⟨by change ε/2*D ≤ (k : ℝ); linarith, hk, B, hb, hu, ?_, ?_⟩
  · have ratio : 2*D/s ≤ 4/ε := by
      apply (div_le_div_iff₀ hs hε).mpr
      dsimp [s]
      linarith
    have hh : (B.card : ℝ) ≤ (⌈4/ε⌉₊ : ℝ)+2 :=
      hcount.trans (by linarith [ratio, Nat.le_ceil (4/ε)])
    exact_mod_cast hh
  · intro U hU
    apply (hcap U hU).trans
    have hb := mul_le_mul_of_nonneg_left hk hε.le
    dsimp [s]
    change _ ≤ (1-ε/8)*(k : ℝ)
    linarith

end Vu
