module
public import Vu.RevisedLabels
public import Vu.RevisedOmission
public import Vu.PieceFamily
namespace Vu.Revised
open Finset

/-- The threshold is chosen after the number of labels and partners is fixed.
Only D controls the rounding of the two frequency thresholds. -/
public theorem column_parameters (r k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ h : ℕ, 0 < h ∧ ∃ D₀ : ℕ, ∀ D ≥ D₀,
    let B := 2^(∑ n ∈ range r, (2*r*h^2)^n)
    (k*(B+(r+1)*(D/h)):ℕ) ≤ η*(D:ℝ)/2 := by
  let h := ⌈4*(k:ℝ)*(r+1)/η⌉₊+1
  let B := 2^(∑ n ∈ range r, (2*r*h^2)^n)
  have hh : 0 < h := Nat.zero_lt_succ _
  refine ⟨h,hh,⌈4*(k:ℝ)*B/η⌉₊,?_⟩
  intro D hD B'
  have hlarge := (div_le_iff₀ hη).mp ((Nat.le_ceil (4*(k:ℝ)*B/η)).trans (Nat.cast_le.mpr hD))
  have hchoice := (div_le_iff₀ hη).mp ((Nat.le_ceil (4*(k:ℝ)*(r+1)/η)).trans (Nat.cast_le.mpr (Nat.le_succ _)))
  change 4*(k:ℝ)*(r+1) ≤ (h:ℝ)*η at hchoice
  have hmul : ((D/h:ℕ):ℝ)*h ≤ D := by exact_mod_cast Nat.div_mul_le_self D h
  change ((k*(B+(r+1)*(D/h)):ℕ):ℝ) ≤ _
  push_cast
  nlinarith only [hlarge,mul_le_mul_of_nonneg_right hchoice (Nat.cast_nonneg (D/h)),mul_le_mul_of_nonneg_right hmul hη.le]

namespace Classes
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)

public theorem tests_and_omissions (s η : ℝ) (h : ℕ) (hh : 0 < h) (hD : 0 < D)
    (hsize : 1 ≤ s) (hω : 0 ≤ ω) (ho : (r:ℝ)^2*ω ≤ 1) (hρ : 0 ≤ ρ)
    (hs : 8*r*√ρ ≤ δ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1/4) (hdeg : ∀ v, G.degree v ≤ D)
    (hsave : (maxCodegree G:ℝ)+8*δ*D ≤ s)
    (budget : ((r*K)*((2^(∑ n ∈ range r, (2*r*h^2)^n))+(r+1)*(D/h)):ℕ) ≤ η*(D:ℝ)/2) :
    ∃ U : V → Finset (Finset V), (∀ x, (U x).biUnion id = (by classical exact d.hardGraph.neighborFinset x)) ∧
    (∀ x, ∀ B ∈ U x, (B.card:ℝ) ≤ s) ∧ (∀ x, ((U x).card:ℝ) ≤ 2*D/s+1) ∧
    ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ U x) ∧
      (by classical exact ∀ z, ((T.filter (fun x => d.hardGraph.Adj x z ∧ z ∉ S x)).card:ℝ) ≤ η*D/2) := by
  classical
  let L := d.labels
  let J := overlapGraph L ((D:ℝ)/(h:ℝ)^2)
  let carry (a : I × Finset V) := univ.filter fun x => a ∈ L x
  have hhR : 0 < (h:ℝ) := Nat.cast_pos.mpr hh
  have hdegJ : ∀ a, J.degree a ≤ 2*r*h^2 := by
    intro a
    have hh := overlap_degree_bound J carry r D h (Nat.cast_pos.mpr hD) hhR
      (fun a => by exact_mod_cast d.label_carriers a) (fun x => by simpa [carry,L] using d.labels_card x) (by
        intro a b hab
        have eq : carry a ∩ carry b = univ.filter (fun x => a ∈ L x ∧ b ∈ L x) := by ext; simp [carry]
        rw [eq]; exact hab.2) a
    exact_mod_cast hh
  let H := d.hardGraph
  have hH (x : V) : H.degree x ≤ D := (degree_subgraph (J := H) (G := G) (fun _ _ h => h.1) x).trans (hdeg x)
  obtain ⟨U,test,hcov,hb,hn,ht,he,heq⟩ := pack_components H J L d.partners d.W D s hsize hH
    (fun x y hxy S hx hy => (d.common_witness x y hxy S hx hy hω ho hρ hs hδ hδ₁ hdeg).trans hsave) d.oriented_label
  refine ⟨U,hcov,hb,hn,?_⟩
  intro T hT
  obtain ⟨S,hS,hcol⟩ := omit_columns H L d.partners U test T D r (r*K) h _ hh hT d.labels_card d.partners_card ht J
    (fun a => split_bound_fixed J L a r _ hdegJ d.labels_card) (by
      intro a b hab hcard
      refine ⟨hab,?_⟩
      have hcount := hcard.trans_le (card_le_card (filter_subset_filter _ (subset_univ T)))
      have hb : D < ((univ.filter (fun y => a ∈ L y ∧ b ∈ L y)).card)*(h*h) := by
        exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos hh hh)).mp hcount
      apply (div_le_iff₀ (sq_pos_of_pos hhR)).mpr
      exact_mod_cast (by simpa [pow_two,Nat.mul_assoc] using hb.le : D ≤ ((univ.filter (fun y => a ∈ L y ∧ b ∈ L y)).card)*h^2)) he heq
  exact ⟨S,hS,fun z => (Nat.cast_le.mpr (hcol z)).trans budget⟩
end Classes
end Vu.Revised
