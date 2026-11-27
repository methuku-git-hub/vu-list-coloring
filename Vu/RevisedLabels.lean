module
public import Vu.RevisedRowEstimates
public import Vu.PartnerWitnesses
namespace Vu.Revised.Classes
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)

@[expose] public noncomputable def labels := carriedLabels d.good d.part
@[expose] public noncomputable def highBlocks (i : I) (A : Finset V) : Finset (Finset V) := by
  classical exact (d.partition i).parts.filter fun B => d.high i A B
@[expose] public noncomputable def partners (x : V) :=
  (d.labels x).biUnion fun a => (d.highBlocks a.1 a.2).image (fun B => (a.1,B))
@[expose] public noncomputable def W (a : I × Finset V) : Finset V := by
  classical exact univ.filter fun y => y ∈ d.good a.1 ∧ d.high a.1 a.2 (d.part a.1 y)
public theorem labels_card (x : V) : (d.labels x).card ≤ r := by
  apply card_image_le.trans
  apply (card_le_card (t := univ.filter (fun i => x ∈ d.piece i)) ?_).trans (d.multiplicity x)
  exact fun i hi => mem_filter.mpr ⟨mem_univ _,d.good_subset i (mem_filter.mp hi).2⟩
public theorem partners_card (x : V) : (d.partners x).card ≤ r*K := by
  classical
  apply card_biUnion_le.trans
  apply (sum_le_sum (g := fun _ => K) (fun a _ => card_image_le.trans ((card_le_card (filter_subset _ _)).trans (d.num a.1)))).trans
  simpa using Nat.mul_le_mul_right K (d.labels_card x)
public theorem label_carriers (a : I × Finset V) : (univ.filter (fun x => a ∈ d.labels x)).card ≤ 2*D := by
  obtain ⟨i,A⟩ := a
  exact (card_le_card (fun x hx => d.good_subset i (((mem_carried ..).mp (mem_filter.mp hx).2).1))).trans (d.size i)
public theorem oriented_label (x y : V) (he : d.hardGraph.Adj x y) :
    ∃ a : ↥(d.labels x), a.val ∈ d.partners y ∧ y ∈ d.W a := by
  classical
  obtain ⟨_,i,_,hg⟩ := he
  have hx := (mem_carried d.good d.part x i _).mpr ⟨hg.1,rfl⟩
  have hy := (mem_carried d.good d.part y i _).mpr ⟨hg.2.1,rfl⟩
  have hw := d.dense_swap i x y hg
  refine ⟨⟨(i,d.part i x),hx⟩,mem_biUnion.mpr ⟨(i,d.part i y),hy,?_⟩,
    mem_filter.mpr ⟨mem_univ _,hg.2.1,hg.2.2⟩⟩
  exact mem_image.mpr ⟨d.part i x,mem_filter.mpr ⟨(d.partition i).part_mem.mpr (d.good_subset i hg.1),hw.2.2⟩,rfl⟩

/-- A good vertex misses at most 4δΔ vertices in the union of its partner classes. -/
public theorem missing_partners (x : V) (S : Finset (I × Finset V)) (hS : S ⊆ d.labels x)
    (hω : 0 ≤ ω) (ho : (r:ℝ)^2*ω ≤ 1) (hρ : 0 ≤ ρ) (hs : 8*r*√ρ ≤ δ)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1/4) (hdeg : G.degree x ≤ D) :
    (((S.biUnion d.W) \ G.neighborFinset x).card:ℝ) ≤ 4*δ*D := by
  classical
  let N := G.neighborFinset x
  let blocks i := (d.blocks i x).filter (fun B => 1-δ ≤ crossDensity G (d.part i x) B)
  let missing i := (blocks i).biUnion (fun B => B \ N)
  have sub : S.biUnion d.W \ N ⊆ univ.biUnion missing := by
    intro y hy
    obtain ⟨⟨i,A⟩,ha,hwy⟩ := mem_biUnion.mp (mem_sdiff.mp hy).1
    obtain ⟨hx,hA⟩ := (mem_carried ..).mp (hS ha)
    obtain ⟨hgy,hd⟩ := (mem_filter.mp hwy).2
    change y ∈ d.good i at hgy
    change d.high i A (d.part i y) at hd
    subst A
    have hpy := d.good_subset i hgy
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨d.part i y,mem_filter.mpr
      ⟨(d.mem_blocks ..).mpr ⟨(d.partition i).part_mem.mpr hpy,hx,hd.1⟩,hd.2⟩,
      mem_sdiff.mpr ⟨(d.partition i).mem_part hpy,(mem_sdiff.mp hy).2⟩⟩⟩
  let n B := count (G := G) x B
  have pt i B (hb : B ∈ blocks i) : (1-δ)*((B \ N).card:ℝ) ≤ δ*n B + d.err i x B := by
    have hh := (mem_filter.mp hb).2
    have hcard : ((B \ N).card:ℝ)+n B=B.card := by
      dsimp [n,count,N]; rw [inter_comm (G.neighborFinset x) B]; exact_mod_cast card_sdiff_add_card_inter B (G.neighborFinset x)
    have herr := neg_le_abs (n B-crossDensity G (d.part i x) B*B.card)
    change _ ≤ d.err i x B at herr
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg B.card),herr,hcard,
      congrArg (fun t : ℝ => δ*t) hcard |> Eq.le,congrArg (fun t : ℝ => δ*t) hcard |> Eq.ge]
  have hbnd i : (1-δ)*((missing i).card:ℝ) ≤ ∑ B ∈ d.blocks i x, (δ*n B+d.err i x B) := by
    have h : ((missing i).card:ℝ) ≤ ∑ B ∈ blocks i, ((B \ N).card:ℝ) := by exact_mod_cast card_biUnion_le
    apply (mul_le_mul_of_nonneg_left h (by linarith)).trans
    rw [mul_sum]
    exact (sum_le_sum (fun B hB => pt i B hB)).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun B _ _ => add_nonneg (mul_nonneg hδ (Nat.cast_nonneg _)) (abs_nonneg _)))
  have hcov : (((S.biUnion d.W) \ N).card:ℝ) ≤ ∑ i, ((missing i).card:ℝ) := by exact_mod_cast (card_le_card sub).trans card_biUnion_le
  have h := mul_le_mul_of_nonneg_left hcov (by linarith : 0 ≤ 1-δ)
  rw [mul_sum] at h
  have hh := h.trans (sum_le_sum fun i _ => hbnd i)
  simp_rw [sum_add_distrib,←mul_sum] at hh
  obtain ⟨hn,he⟩ := d.row_estimates x hω ho hρ hs hdeg
  change _ ≤ δ*(∑ i, ∑ B ∈ d.blocks i x, count (G := G) x B)+_ at hh
  have hh' := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hn hδ) he)
  change (((S.biUnion d.W) \ N).card:ℝ) ≤ _
  apply (mul_le_mul_iff_of_pos_left (by linarith : 0 < 1-δ)).mp
  exact hh'.trans (by nlinarith only [mul_le_mul_of_nonneg_right hδ₁ (mul_nonneg hδ (Nat.cast_nonneg D))])
public theorem common_witness (x y : V) (hne : x ≠ y) (S : Finset (I × Finset V))
    (hx : S ⊆ d.labels x) (hy : S ⊆ d.labels y) (hω : 0 ≤ ω) (ho : (r:ℝ)^2*ω ≤ 1)
    (hρ : 0 ≤ ρ) (hs : 8*r*√ρ ≤ δ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1/4)
    (hdeg : ∀ v, G.degree v ≤ D) :
    ((S.biUnion d.W).card:ℝ) ≤ maxCodegree G + 8*δ*D := by
  have miss u (hu : S ⊆ d.labels u) := Nat.le_floor (d.missing_partners u S hu hω ho hρ hs hδ hδ₁ (hdeg u))
  have h := card_le_codegree_add_two_mul G x y _ _ _ (((maxCodegree_le_iff G _).mp le_rfl) x y hne) (miss x hx) (miss y hy)
  have hh := Nat.cast_le (α := ℝ) |>.mpr h
  push_cast at hh
  linarith only [hh,Nat.floor_le (show 0 ≤ 4*δ*(D:ℝ) by positivity)]
end Vu.Revised.Classes
