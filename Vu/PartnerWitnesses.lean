module
public import Vu.Estimates
public import Vu.RegularRows

namespace Vu
open Finset

/-- Row estimate in Lemma 4.4. Occurrences of partner classes are indexed
separately, so a neighbor can be counted more than once in the input sum.
The conclusion counts missing neighbors of the union only once. -/
public theorem partner_union_missing {I V : Type*} [DecidableEq V] (I₀ : Finset I)
    (B : I → Finset V) (N W : Finset V) (d : I → ℝ) (D δ : ℝ) (hD : 0 ≤ D)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/200) (hW : W ⊆ I₀.biUnion B)
    (hd : ∀ i ∈ I₀, 1-δ ≤ d i)
    (hrep : (∑ i ∈ I₀, ((B i ∩ N).card : ℝ)) ≤ (1+δ)*D)
    (herr : (∑ i ∈ I₀, |((B i ∩ N).card : ℝ) - d i * (B i).card|) ≤ δ*D/4) :
    ((W \ N).card : ℝ) ≤ 2*δ*D := by
  classical
  let m := ∑ i ∈ I₀, ((B i).card : ℝ)
  let e := ∑ i ∈ I₀, ((B i ∩ N).card : ℝ)
  have hm : 0 ≤ m := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hdef : (1-δ)*m - e ≤ δ*D/4 := by
    apply le_trans _ herr
    simp only [m,e,mul_sum,← sum_sub_distrib]
    apply sum_le_sum
    intro i hi
    rw [abs_sub_comm]
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_right (hd i hi) (Nat.cast_nonneg _)) _).trans (le_abs_self _)
  change e ≤ _ at hrep
  have hm' : m ≤ 7/4*D := by
    have hδm := mul_le_mul_of_nonneg_right hδ' hm
    have hδD := mul_le_mul_of_nonneg_right hδ' hD
    linarith
  have hsub : W \ N ⊆ I₀.biUnion (fun i => B i \ N) := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_biUnion.mp (hW (mem_sdiff.mp hx).1)
    exact mem_biUnion.mpr ⟨i,hi,mem_sdiff.mpr ⟨hxi,(mem_sdiff.mp hx).2⟩⟩
  have hcount : ((W \ N).card : ℝ) ≤ ∑ i ∈ I₀, ((B i \ N).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hsum : (∑ i ∈ I₀, ((B i \ N).card : ℝ)) + e = m := by
    dsimp [e,m]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact_mod_cast card_sdiff_add_card_inter (B i) N
  linarith [mul_le_mul_of_nonneg_left hm' hδ]

/-- Two-witness bound supplied to the hard test construction. This version
allows the row occurrences and their densities to depend on the vertex. -/
public theorem partner_family_witness_bound {V A I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset A) (W : A → Finset V)
    (rows : V → Finset I) (B : V → I → Finset V) (d : V → I → ℝ) (D t : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/200)
    (hcodeg : ∀ x y, x ≠ y → Fintype.card (G.commonNeighbors x y) ≤ t)
    (hcover : ∀ x, ∀ a ∈ L x, W a ⊆ (rows x).biUnion (B x))
    (hd : ∀ x i, i ∈ rows x → 1-δ ≤ d x i)
    (hrep : ∀ x, (∑ i ∈ rows x, ((B x i ∩ G.neighborFinset x).card : ℝ)) ≤ (1+δ)*D)
    (herr : ∀ x, (∑ i ∈ rows x, |((B x i ∩ G.neighborFinset x).card : ℝ) - d x i*(B x i).card|) ≤ δ*D/4)
    (x y : V) (hne : x ≠ y) (S : Finset A) (hx : S ⊆ L x) (hy : S ⊆ L y) :
    ((S.biUnion W).card : ℝ) ≤ t + 4*δ*D := by
  classical
  have hmiss (u : V) (hu : S ⊆ L u) : ((S.biUnion W) \ G.neighborFinset u).card ≤ ⌊2*δ*D⌋₊ := by
    apply Nat.le_floor
    apply partner_union_missing (rows u) (B u) _ _ (d u) D δ (Nat.cast_nonneg _) hδ hδ' _ (hd u) (hrep u) (herr u)
    intro z hz
    obtain ⟨a,ha,hz⟩ := mem_biUnion.mp hz
    exact hcover u a (hu ha) hz
  have hh := card_le_codegree_add_two_mul G x y _ t _ (hcodeg x y hne) (hmiss x hx) (hmiss y hy)
  have hreal := Nat.cast_le (α := ℝ) |>.mpr hh
  push_cast at hreal
  linarith [Nat.floor_le (show 0 ≤ 2*δ*(D : ℝ) by positivity)]
end Vu
