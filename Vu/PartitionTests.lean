module
public import Vu.PartnerOccurrences
public import Vu.PartnerWitnesses
namespace Vu
open Finset

/-- Assemble the hard-neighbor part of Proposition 3.1 directly from
the class partitions and property (G). The numerical hypotheses are the
ones chosen in Section 4. No label assignment or partner-family bound is assumed. -/
public theorem partition_hard_tests (r K : ℕ) (hr : 0 < r) (η : ℝ) (he : 0 < η) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V] [LinearOrder I]
      (G : SimpleGraph V) [DecidableRel G.Adj] (P good : I → Finset V)
      (cls : I → V → Finset V) (parts : I → Finset (Finset V)) (t : ℕ) (ω ρ δ s : ℝ),
    0 < s → 0 ≤ ω → 0 ≤ δ → δ ≤ 1/200 → (r : ℝ)^3*ω ≤ δ → 8*r*√ρ ≤ δ/4 →
    (t : ℝ)+4*δ*D ≤ s → (∀ x, G.degree x ≤ D) →
    (∀ x y, x ≠ y → Fintype.card (G.commonNeighbors x y) ≤ t) →
    (∀ i, (P i).card ≤ 2*D) → (∀ i, (parts i).card ≤ K) → (∀ i, good i ⊆ P i) →
    (∀ x, (univ.filter fun i => x ∈ P i).card ≤ r) →
    (∀ i A, A ∈ parts i → ∀ y, y ∈ A ↔ y ∈ P i ∧ cls i y = A) →
    (∀ i A, A ∈ parts i → ∀ j < i, ω*D < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j)) →
    (∀ i x, x ∈ good i → ∃ y ≠ x, y ∈ good i ∧ cls i y = cls i x) →
    let J := fun i => partnerGraph G P i (parts i) (ω*D) ρ δ
    (∀ i x, x ∈ good i → (by classical exact ∑ B ∈ (J i).neighborFinset (cls i x),
      |((B ∩ G.neighborFinset x).card : ℝ) - crossDensity G (cls i x) B * B.card|) ≤ 4*√ρ*(P i).card) →
    let H := hardGraph G P good cls (ω*D) J
    ∃ U : V → Finset (Finset V),
      (∀ x, (U x).biUnion id = (by classical exact H.neighborFinset x)) ∧
      (∀ x, ∀ B ∈ U x, (B.card : ℝ) ≤ s) ∧ (∀ x, ((U x).card : ℝ) ≤ 2*D/s+1) ∧
      ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ U x) ∧
        (by classical exact RowNormLE (fun x z => if H.Adj x z ∧ z ∉ S x then 1 else 0) T (η*D)) := by
  classical
  obtain ⟨D₀,hD⟩ := hard_test_families r (r*K) hr η he
  refine ⟨D₀,?_⟩
  intro D hd V I _ _ _ _ G _ P good cls parts t ω ρ δ s hs hω hδ hδ' ho hsq hsave hdeg hcodeg
    hp hk hin hmul hclass href htwo J hdis H
  let L := carriedLabels good cls
  let act x := univ.filter fun i => x ∈ good i
  have hact (x : V) : (act x).card ≤ r := by
    apply (card_le_card (t := univ.filter fun i => x ∈ P i) ?_).trans (hmul x)
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,hin i (mem_filter.mp hi).2⟩
  obtain ⟨C,W,hC,hW,hlabels⟩ := dense_pair_hard_edges G P good cls parts (ω*D) ρ δ r K hact hk
  let rows (x : V) := (act x).sigma (fun i => (J i).neighborFinset (cls i x))
  let B (_ : V) (j : Σ _i : I, Finset V) := j.2
  let d (x : V) (j : Σ _i : I, Finset V) := crossDensity G (cls j.1 x) j.2
  have hcover (x : V) (a : I × Finset V) (ha : a ∈ L x) : W a ⊆ (rows x).biUnion (B x) := by
    intro y hy
    obtain ⟨⟨i,Y⟩,hb,hai,hadj⟩ := (hW a y).mp hy
    rcases a with ⟨j,A⟩
    change j = i at hai
    subst i
    obtain ⟨hx,hA⟩ := (mem_carried ..).mp ha
    obtain ⟨hy,hY⟩ := (mem_carried ..).mp hb
    have hparts : Y ∈ parts j := hadj.2.1
    refine mem_biUnion.mpr ⟨⟨j,Y⟩,mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,?_⟩,?_⟩
    · exact ((J j).mem_neighborFinset _ _).mpr (hA ▸ hadj)
    · exact (hclass j Y hparts y).mpr ⟨hin j hy,hY⟩
  have hden (x : V) (j : Σ _i : I, Finset V) (hj : j ∈ rows x) : 1-δ ≤ d x j :=
    (((J j.1).mem_neighborFinset _ _).mp (mem_sigma.mp hj).2).2.2.2.2.2
  have hrep (x : V) : (∑ j ∈ rows x, (((B x j) ∩ G.neighborFinset x).card : ℝ)) ≤ (1+δ)*D := by
    obtain ⟨E,hE,hEx⟩ := exceptional_occurrence_budget P r D ω δ hω ho x (hmul x)
    have hh := full_partner_degree_sum G P good cls parts (ω*D) ρ δ r hin hmul hclass href x E
      (fun y => (hE y).mpr)
    dsimp only at hh
    have hh' := (Nat.cast_le (α := ℝ)).mpr hh
    push_cast at hh'
    simp only [rows,B,sum_sigma]
    change (∑ i ∈ act x, ∑ b ∈ (J i).neighborFinset (cls i x), ((b ∩ G.neighborFinset x).card : ℝ)) ≤ _
    change (∑ i ∈ act x, ∑ b ∈ (J i).neighborFinset (cls i x), ((b ∩ G.neighborFinset x).card : ℝ)) ≤ _ at hh'
    linarith [Nat.cast_le (α := ℝ) |>.mpr (hdeg x)]
  have herr (x : V) : (∑ j ∈ rows x, |((B x j ∩ G.neighborFinset x).card : ℝ)-d x j*(B x j).card|) ≤ δ*D/4 := by
    simp only [rows,B,d,sum_sigma]
    have hp' (i : I) : ((P i).card : ℝ) ≤ 2*(D : ℝ) := by exact_mod_cast hp i
    apply (sum_le_sum (s := act x) (g := fun _ => 4*√ρ*(2*D)) (fun i hi =>
      (hdis i x (mem_filter.mp hi).2).trans (mul_le_mul_of_nonneg_left (hp' i) (by positivity)))).trans
    simp only [sum_const,nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr (hact x))
      (by positivity : 0 ≤ 4*√ρ*(2*(D : ℝ)))
    linarith only [hh,mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg D)]
  apply hD D hd V (I × Finset V) H L C W s hs
  · intro x
    apply (card_le_card (s := H.neighborFinset x) (t := G.neighborFinset x) ?_).trans (hdeg x)
    intro z hz
    exact (G.mem_neighborFinset x z).mpr (((H.mem_neighborFinset x z).mp hz).1)
  · exact fun x => card_image_le.trans (hact x)
  · exact hC
  · rintro ⟨i,A⟩
    apply (Nat.cast_le.mpr (card_le_card (t := P i) ?_)).trans (by exact_mod_cast hp i)
    intro x hx
    exact hin i ((mem_carried ..).mp (mem_filter.mp hx).2).1
  · rintro x ⟨⟨i,A⟩,ha⟩
    obtain ⟨hg,hA⟩ := (mem_carried ..).mp ha
    obtain ⟨y,hy,hyg,hyc⟩ := htwo i x hg
    exact ⟨y,hy,(mem_carried ..).mpr ⟨hyg,hyc.trans hA⟩⟩
  · intro x y hn S hx hy
    exact (partner_family_witness_bound G L W rows B d D t δ hδ hδ' hcodeg hcover hden hrep herr x y hn S hx hy).trans hsave
  · intro x y he
    obtain ⟨a,ha,hP,hw⟩ := hlabels x y he
    exact ⟨⟨a,ha⟩,hP,hw⟩
end Vu
