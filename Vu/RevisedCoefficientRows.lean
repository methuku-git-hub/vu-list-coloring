module
public import Vu.RevisedRowEstimates
public import Vu.RevisedBlockCut
namespace Vu.Revised.Classes
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)

public theorem beta_entries (x y : V) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    -1 ≤ d.beta x y ∧ d.beta x y ≤ 1/δ := by
  classical
  by_cases hg : G.Adj x y
  · simp [beta,hg]; linarith [inv_pos.mpr hδ]
  have lower i : 0 ≤ d.block i x y := by
    unfold block
    split
    next h =>
      have ht := h.2.2.2
      simpa [centeredEntry,hg] using div_nonneg (density_mem_unit G (d.part i x) (d.part i y)).1
        (by linarith : 0 ≤ 1-crossDensity G (d.part i x) (d.part i y))
    next => exact le_rfl
  rw [beta,if_neg hg]
  by_cases hc : (jointPieces d.piece x y).Nonempty
  · obtain ⟨i,hi,hu⟩ := least_joint_piece d.piece x y hc
    change d.first i x y at hi
    rw [sum_eq_single i (fun j _ hn => by simp [show ¬d.first j x y from fun hj => hn (hu j hj)]) (by simp),if_pos hi]
    exact ⟨(by norm_num : (-1:ℝ) ≤ 0).trans (lower i),(le_abs_self _).trans (d.block_bound i x y hδ)⟩
  · simp [show ∀ i, ¬d.first i x y from fun i h => hc ⟨i,h.1⟩,hδ.le]

public theorem beta_support (x : V) (hdeg : G.degree x ≤ D) (hD : 1+2*r ≤ D) :
    (by classical exact (univ.filter (fun y => d.beta x y ≠ 0)).card) ≤ D^2 := by
  classical
  let act := univ.filter fun i => x ∈ d.piece i
  let Q := act.biUnion d.piece
  have sub : univ.filter (fun y => d.beta x y ≠ 0) ⊆ G.neighborFinset x ∪ Q := by
    intro y hy
    by_contra! hn
    rw [mem_union,not_or] at hn
    have hg : ¬G.Adj x y := by simpa using hn.1
    have none (i : I) : ¬d.first i x y := by
      intro hf
      obtain ⟨hx,hy⟩ := (mem_filter.mp hf.1).2
      exact hn.2 (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hx⟩,hy⟩)
    exact (mem_filter.mp hy).2 (by simp [beta,hg,none])
  have bound : Q.card ≤ r*(2*D) := calc
    _ ≤ ∑ i ∈ act, (d.piece i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ act, 2*D := sum_le_sum fun i _ => d.size i
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (2*D) (d.multiplicity x)
  apply ((card_le_card sub).trans (card_union_le ..)).trans
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  nlinarith only [Nat.mul_le_mul_right D hD,bound,hdeg]

public theorem beta_row (x : V) (hω : 0 ≤ ω) (ho : (r:ℝ)^2*ω ≤ 1) (hρ : 0 ≤ ρ)
    (hs : 8*r*√ρ ≤ δ) (hd : 0 < δ) (hdeg : G.degree x ≤ D) : ∑ y, |d.beta x y| ≤ 4*D := by
  classical
  let N := G.neighborFinset x
  let dens i B := crossDensity G (d.part i x) B
  let sel i := (d.blocks i x).filter fun B => dens i B < 1-δ
  let price i B := dens i B/(1-dens i B)
  let pos i y := ∑ B ∈ sel i, if y ∈ B \ N then price i B else 0
  have hprice i B (hb : B ∈ sel i) : 0 ≤ price i B := div_nonneg (density_mem_unit G _ _).1
    (by have hh := (mem_filter.mp hb).2; linarith)
  have hterm i B (hb : B ∈ sel i) (y : V) : 0 ≤ (if y ∈ B \ N then price i B else 0) := by
    split <;> first | exact hprice i B hb | exact le_rfl
  have hpos i y : 0 ≤ pos i y := sum_nonneg (fun B hb => hterm _ _ hb _)
  have point y : |d.beta x y| ≤ (if G.Adj x y then 1 else 0)+∑ i, pos i y := by
    by_cases hg : G.Adj x y
    · simp [beta,hg,sum_nonneg (fun i _ => hpos i y)]
    simp only [beta,if_neg hg,zero_add]
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum; intro i _
    by_cases hf : d.first i x y
    · simp only [if_pos hf]
      by_cases hl : d.ordinary i x y
      · let B := d.part i y
        have hpy := d.good_subset i hl.2.1
        have hb : B ∈ sel i := mem_filter.mpr ⟨(d.mem_blocks ..).mpr ⟨(d.partition i).part_mem.mpr hpy,hl.1,hl.2.2.1⟩,hl.2.2.2⟩
        have hy : y ∈ B \ N := mem_sdiff.mpr ⟨(d.partition i).mem_part hpy,by simpa [N] using hg⟩
        calc
          _ = price i B := by simp [block,hl,centeredEntry,hg,price,dens,B,abs_of_nonneg (hprice i B hb)]
          _ = (if y ∈ B \ N then price i B else 0) := by simp [hy]
          _ ≤ pos i y := single_le_sum (fun b hb => hterm i b hb y) hb
      · simpa [block,hl] using hpos i y
    · simpa [hf] using hpos i y
  have row i : (∑ y, pos i y) ≤ ∑ B ∈ d.blocks i x, (count (G := G) x B+d.err i x B/δ) := by
    dsimp only [pos]
    rw [sum_comm]
    have bnd B (hb : B ∈ sel i) : (∑ y, if y ∈ B \ N then price i B else 0) ≤ count (G := G) x B+d.err i x B/δ := by
      simp only [←sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
      let n := count (G := G) x B
      let a := dens i B
      have hden : δ ≤ 1-a := by have hh := (mem_filter.mp hb).2; change a < 1-δ at hh; linarith
      have cardEq : ((B \ N).card:ℝ) = B.card-n := by
        apply eq_sub_of_add_eq
        dsimp [n,count,N]; rw [inter_comm (G.neighborFinset x) B]; exact_mod_cast card_sdiff_add_card_inter B (G.neighborFinset x)
      change _* (a/(1-a)) ≤ n+d.err i x B/δ
      rw [cardEq]
      have form : ((B.card:ℝ)-n)*(a/(1-a)) = n+(a*B.card-n)/(1-a) := by field_simp [(hd.trans_le hden).ne']; ring
      rw [form]
      apply add_le_add_right
      have hab : a*B.card-n ≤ d.err i x B := by simpa [err,n,a,dens,abs_sub_comm] using le_abs_self (a*B.card-n)
      exact (div_le_div_of_nonneg_right hab (hd.trans_le hden).le).trans (div_le_div_of_nonneg_left (abs_nonneg _) hd hden)
    exact (sum_le_sum (fun B hb => bnd B hb)).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun B _ _ =>
      add_nonneg (Nat.cast_nonneg _) (div_nonneg (abs_nonneg _) hd.le)))
  obtain ⟨h₁,h₂⟩ := d.row_estimates x hω ho hρ hs hdeg
  apply (sum_le_sum (fun y _ => point y)).trans
  rw [sum_add_distrib,sum_comm (s := univ) (t := univ) (f := fun y i => pos i y)]
  have hcost : (∑ y, if G.Adj x y then (1:ℝ) else 0) = G.degree x := by simp [SimpleGraph.degree,SimpleGraph.neighborFinset_def]
  rw [hcost]
  have hsum := sum_le_sum (s := univ) (fun i _ => row i)
  simp_rw [sum_add_distrib,←sum_div] at hsum
  linarith only [hsum,h₁,(div_le_iff₀ hd).mpr (by linarith only [h₂] : (∑ i, ∑ B ∈ d.blocks i x, d.err i x B) ≤ D*δ),Nat.cast_le (α := ℝ) |>.mpr hdeg]
end Vu.Revised.Classes
