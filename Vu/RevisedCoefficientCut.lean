module
public import Vu.RevisedErrors
namespace Vu.Revised.Classes
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)
@[expose] public noncomputable def omittedHard (x y : V) : ℝ := by
  classical exact if d.hardGraph.Adj x y then 0 else d.beta x y
@[expose] public noncomputable def earlierTerm (i : I) (x y : V) : ℝ := by
  classical exact if d.first i x y then 0 else d.block i x y
@[expose] public noncomputable def uncovered (x y : V) : ℝ := by
  classical exact if G.Adj x y ∧ ¬(jointPieces d.piece x y).Nonempty then 1 else 0
public theorem soft_identity (x y : V) (hδ : 0 < δ) :
    d.omittedHard x y = (∑ i, (d.block i x y + d.extra i x y)) - ∑ i, d.earlierTerm i x y - d.uncovered x y := by
  classical
  have decomp : (∑ i, (d.block i x y+d.extra i x y)) - ∑ i, d.earlierTerm i x y =
      ∑ i, if d.first i x y then d.block i x y+d.extra i x y else 0 := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl; intro i _
    by_cases hf : d.first i x y <;> simp [earlierTerm,extra,hf]
  rw [decomp]
  by_cases hc : (jointPieces d.piece x y).Nonempty
  · obtain ⟨j,hj,hu⟩ := least_joint_piece d.piece x y hc
    change d.first j x y at hj
    have huniq (i) (hn : i ≠ j) : ¬d.first i x y := fun h => hn (hu i h)
    rw [sum_eq_single j (fun i _ hn => by simp [huniq i hn]) (by simp),if_pos hj]
    have hhard : d.hardGraph.Adj x y ↔ G.Adj x y ∧ d.dense j x y := by
      constructor
      · rintro ⟨h,i,hf,hd⟩; exact ⟨h,(hu i hf) ▸ hd⟩
      · rintro ⟨h,hd⟩; exact ⟨h,j,hj,hd⟩
    by_cases hg : G.Adj x y
    · by_cases hd : d.dense j x y
      · have hlo : ¬ d.ordinary j x y := fun h => h.2.2.2.not_ge hd.2.2.2
        simp [omittedHard,hhard,hg,hd,block,hlo,extra,uncovered,hc]
      · by_cases hl : d.ordinary j x y
        · have hn : 1-crossDensity G (d.part j x) (d.part j y) ≠ 0 := by
            have h := hl.2.2.2
            linarith
          simp [omittedHard,hhard,hg,hd,beta,block,hl,extra,uncovered,hc,centeredEntry]
          field_simp
          <;> ring
        · simp [omittedHard,hhard,hg,hd,beta,block,hl,extra,hj,uncovered,hc]
    · simp only [omittedHard,hhard,hg,false_and,ite_false,beta,uncovered,hc,not_true_eq_false,and_false,sub_zero]
      rw [sum_eq_single j (fun i _ hn => by simp [huniq i hn]) (by simp),if_pos hj]
      simp [extra,hg]
  · have none (i : I) : ¬d.first i x y := fun h => hc ⟨i,h.1⟩
    have hh : ¬d.hardGraph.Adj x y := fun ⟨_,i,hf,_⟩ => none i hf
    by_cases hg : G.Adj x y <;> simp [omittedHard,hh,beta,hg,none,uncovered,hc]

public theorem earlier_cut (X Y : Finset V) (hX : X.card ≤ D) (hω : 0 ≤ ω) (hd : 0 < δ) :
    |∑ x ∈ X, ∑ y ∈ Y, ∑ i, d.earlierTerm i x y| ≤ r^2*ω/δ*D^2 := by
  classical
  let bad i x := univ.filter fun y => d.admissible i x y ∧ ¬d.first i x y
  have point i x y : |d.earlierTerm i x y| ≤ if y ∈ bad i x then 1/δ else 0 := by
    by_cases hf : d.first i x y
    · have hn : y ∉ bad i x := fun h => (mem_filter.mp h).2.2 hf
      simp [earlierTerm,hf,hn]
    by_cases hl : d.ordinary i x y
    · have hb : y ∈ bad i x := mem_filter.mpr ⟨mem_univ _,d.ordinary_admissible hl,hf⟩
      simpa [earlierTerm,hf,hb] using d.block_bound i x y hd
    · simp only [earlierTerm,if_neg hf,block,if_neg hl,abs_zero]; split <;> positivity
  have row x : |∑ y ∈ Y, ∑ i, d.earlierTerm i x y| ≤ (r:ℝ)^2*ω*D/δ := by
    rw [sum_comm]
    apply (abs_sum_le_sum_abs ..).trans
    apply (sum_le_sum (fun i _ => (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun y _ => point i x y)))).trans
    have bound i : (∑ y ∈ Y, if y ∈ bad i x then 1/δ else 0) ≤ (bad i x).card/δ := by
      rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one_div]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card (fun y hy => (mem_filter.mp hy).2))) hd.le
    apply (sum_le_sum (fun i _ => bound i)).trans
    rw [←sum_div]
    exact div_le_div_of_nonneg_right (d.earlier_occurrences x hω) hd.le
  apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun x _ => row x)).trans ?_)
  simp only [sum_const,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hX) (by positivity)).trans_eq (by ring)

public theorem local_terms_cut (X Y : Finset V) (hX : X.card ≤ D) (hY : Y.card ≤ D) (hd : 0 < δ) (hd₁ : δ ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    |∑ x ∈ X, ∑ y ∈ Y, ∑ i, (d.block i x y + d.extra i x y)| ≤ 2*r*D^2*√((ρ/δ+ρ+2*√ρ)/δ) := by
  classical
  let S i x y := d.block i x y+d.extra i x y
  let s i := ∑ x ∈ X, ∑ y ∈ Y, S i x y
  let c := ρ/δ+ρ+2*√ρ
  have localB i : |s i| ≤ c*((d.piece i).card:ℝ)^2 := by
    simp only [s,S,sum_add_distrib]
    apply (abs_add_le ..).trans ((add_le_add (d.regular_cut i X Y hρ hd) (d.extra_cut i X Y hρ hρ₁)).trans_eq ?_)
    dsimp [c]; ring
  have one i x y : |S i x y| ≤ 1/δ := by
    by_cases hl : d.ordinary i x y
    · simpa [S,extra,hl] using d.block_bound i x y hd
    · simp only [S,block,if_neg hl,zero_add,extra]; split
      · simpa using (le_div_iff₀ hd).mpr (by simpa using hd₁ : 1*δ ≤ 1)
      · simp [hd.le]
  have entry i : |s i| ≤ (1/δ)*((X ∩ d.piece i).card:ℝ)*(Y ∩ d.piece i).card := by
    have out x y (h : x ∉ d.piece i ∨ y ∉ d.piece i) : S i x y = 0 := by
      have he : d.extra i x y = 0 := by
        by_contra hn
        have hh := (mem_filter.mp (d.extra_cases i x y hn).1.1).2
        exact h.elim (fun hn => hn hh.1) (fun hn => hn hh.2)
      change d.block i x y + d.extra i x y = 0
      rw [he,add_zero]
      exact d.block_support i x y (h.imp (fun hn h => hn (d.good_subset i h)) (fun hn h => hn (d.good_subset i h)))
    dsimp only [s]
    rw [←sum_subset (s₁ := X ∩ d.piece i) inter_subset_left (fun x hx hn => sum_eq_zero fun y _ => out x y (Or.inl fun h => hn (mem_inter.mpr ⟨hx,h⟩)))]
    apply (abs_sum_le_sum_abs ..).trans
    have row x : |∑ y ∈ Y, S i x y| ≤ (Y ∩ d.piece i).card*(1/δ) := by
      rw [←sum_subset (s₁ := Y ∩ d.piece i) inter_subset_left (fun y hy hn => out x y (Or.inr fun h => hn (mem_inter.mpr ⟨hy,h⟩)))]
      exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun y _ => one i x y)).trans_eq (by simp))
    apply (sum_le_sum (fun x _ => row x)).trans_eq
    simp only [sum_const,nsmul_eq_mul]; ring
  have eq : (∑ x ∈ X, ∑ y ∈ Y, ∑ i, S i x y) = ∑ i, s i := by
    dsimp only [s]
    simp_rw [sum_comm (s := Y) (t := univ)]
    rw [sum_comm]
  change |∑ x ∈ X, ∑ y ∈ Y, ∑ i, S i x y| ≤ _
  rw [eq]
  exact (abs_sum_le_sum_abs ..).trans (by simpa [c,div_eq_mul_inv] using sum_piece_rectangles d.piece X Y D r c (1/δ) (by dsimp [c]; positivity) (by positivity) s hX hY d.size d.multiplicity localB entry)
end Vu.Revised.Classes
