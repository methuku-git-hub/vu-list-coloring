module
public import Vu.HardDecomposition
public import Vu.RevisedPieces
namespace Vu.Revised
open Finset
/-- The data for the hard part of Proposition 3.1, including the compatible
partitions, their irregular areas, and the rectangle bound on uncovered edges. -/
public structure HardDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D r k₀ K k Rmax : ℕ) (lam ω ρ δ b η : ℝ) where
  pieces : Finset (Finset V)
  extracted : PieceFamily G D (lam/8) (lam*D^2) pieces
  multiplicity : ∀ x : V, (pieces.filter fun P => x ∈ P).card ≤ r
  partition : ∀ i : ↥pieces, Finpartition i.val
  numClasses : ∀ i, (partition i).parts.card ≤ K
  maxClass : ∀ i A, A ∈ (partition i).parts → A.card ≤ i.val.card/k₀+1
  refines : ∀ i A, A ∈ (partition i).parts → ∀ Q ∈ pieces, ω*D < ((i.val ∩ Q).card : ℝ) →
    A ⊆ Q ∨ Disjoint A Q
  irregularArea : ∀ i : ↥pieces, (by classical exact ∑ e ∈ ((partition i).parts ×ˢ (partition i).parts).filter (fun e => e.1 ≠ e.2 ∧ irregularPair G ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) ≤ ρ*(i.val.card : ℝ)^2
  tests : V → Finset (Finset V)
  cover : ∀ x, (tests x).biUnion id = (by classical exact
    (partitionHardGraph G pieces partition K (ω*D) ρ δ).neighborFinset x)
  size : ∀ x U, U ∈ tests x → (U.card : ℝ) ≤ (1-b)*k
  count : ∀ x, (tests x).card ≤ Rmax
  omitted : ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ tests x) ∧
    (by classical exact RowNormLE (fun x z => if (partitionHardGraph G pieces partition K (ω*D) ρ δ).Adj x z ∧
      z ∉ S x then 1 else 0) T (η*D))

/-- Construct (D1) and (D2) for every input graph with the prescribed constants
b and R. The auxiliary parameters are left free within their bounds so that
the same family can subsequently be used for the matrix estimates. -/
public theorem hard_decomposition (ε η lam ω ρ : ℝ) (k₀ : ℕ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η) (hlam : 0 < lam)
    (hω : 0 < ω) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4) (hk₀ : 0 < k₀) :
    let q := lam/8
    let r := ⌈1/q⌉₊
    let δ := ε/200
    (r : ℝ)^3*ω ≤ δ → 8*r*√ρ ≤ δ/4 →
    ∃ K : ℕ, 0 < K ∧ ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], (∀ x, G.degree x ≤ D) →
      let k := ⌊(maxCodegree G : ℝ)+ε*D⌋₊
      ε/2*D ≤ k ∧ k ≤ 2*D ∧ Nonempty (HardDecomposition G D r k₀ K k (⌈4/ε⌉₊+2) lam ω ρ δ (ε/8) η) := by
  classical
  intro q r δ ho hs
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨K,hKpos,hK⟩ := ambient_regular_partitions ρ ω hρ hρ₁ hω r k₀ hk₀
  obtain ⟨D₁,hD₁⟩ := good_partition_hard_tests r K hr η hη
  have hrho : √ρ < 1 := by nlinarith [Real.sq_sqrt hρ.le]
  let c := (1-√ρ)*ρ*q
  have hc : 0 < c := mul_pos (mul_pos (sub_pos.mpr hrho) hρ) hq
  refine ⟨K,hKpos,max D₁ (max ⌈4/ε⌉₊ ⌈2*K/c⌉₊),?_⟩
  intro D hD V _ _ G _ hdeg k
  have hbase := le_max_right D₁ _ |>.trans hD
  have hfour : 4 ≤ ε*D := by
    have hh := (Nat.le_ceil (4/ε)).trans (Nat.cast_le.mpr ((le_max_left _ _).trans hbase))
    linarith only [(div_le_iff₀ hε).mp hh]
  have hDpos : 0 < D := by by_contra! h; norm_num [Nat.le_zero.mp h] at hfour
  have hlarge : 2*(K : ℝ) ≤ c*D := by
    have hh := (Nat.le_ceil (2*K/c)).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hbase))
    linarith only [(div_le_iff₀ hc).mp hh]
  obtain ⟨F,hF,hm⟩ := extracting_dense_pieces G D hdeg lam hlam
  have hp (i : ↥F) := hF.1 i.val i.property
  choose R hnum hmax hcut hir using fun i : ↥F => hK V G F D hDpos hm
    (fun P hP => (hF.1 P hP).2.2.1) i.val i.property
  letI := pieceOrder F
  let t := maxCodegree G
  have ht : t ≤ D := (maxCodegree_le_iff G D).mpr (fun x y _ =>
    (G.card_commonNeighbors_le_degree_left x y).trans (hdeg x))
  have hkreal : (k : ℝ) ≤ (t : ℝ)+ε*D := Nat.floor_le (by positivity)
  have hlow : (t : ℝ)+ε*D < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hkupper : (k : ℝ) ≤ 2*D := by
    linarith [mul_le_mul_of_nonneg_right hε₁ (Nat.cast_nonneg D),Nat.cast_le (α := ℝ) |>.mpr ht]
  have hklower : ε/2*D ≤ k := by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]
  let s := (t : ℝ)+ε*D/2
  have hsp : 0 < s := by dsimp [s]; positivity
  have hsize : s ≤ (1-ε/8)*k := by
    dsimp [s]
    linarith only [mul_le_mul_of_nonneg_left hkupper hε.le,hlow,hfour]
  obtain ⟨U,hcover,hcard,hcount,homit⟩ := hD₁ D ((le_max_left _ _).trans hD)
    V (↥F) G Subtype.val R t ω ρ δ s hsp hω.le (by dsimp [δ]; positivity)
    (by dsimp [δ]; linarith) ho hs (by dsimp [s,δ]; nlinarith)
    hdeg ((maxCodegree_le_iff G t).mp (le_refl _)) (fun i => (hp i).2.2.1) hnum
    (fun x => by rw [univ_eq_attach,filter_attach (fun P : Finset V => x ∈ P) F,card_map,card_attach]; exact hm x)
    (fun i A ha j _ => hcut i A ha j.val j.property) hρ (by linarith) (by
      intro i
      have hkp : 0 < (K : ℝ) := Nat.cast_pos.mpr hKpos
      rw [← mul_div_assoc,le_div_iff₀ hkp]
      have hh := mul_le_mul_of_nonneg_left (hp i).2.1 (mul_nonneg (sub_nonneg.mpr hrho.le) hρ.le)
      dsimp [c,q] at hlarge
      linarith only [hh,hlarge])
  refine ⟨hklower,by exact_mod_cast hkupper,⟨⟨F,hF,hm,R,hnum,hmax,hcut,hir,U,hcover,
    fun x B hb => (hcard x B hb).trans hsize,?_,homit⟩⟩⟩
  intro x
  have hdiv : 2*(D : ℝ)/s ≤ 4/ε := by
    apply (div_le_div_iff₀ hsp hε).mpr
    dsimp [s]
    linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]
  exact Nat.cast_le (α := ℝ) |>.mp (by
    push_cast
    linarith [hcount x,Nat.le_ceil (4/ε)])
end Vu.Revised
