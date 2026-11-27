module
public import Vu.ExceptionalNorm
public import Vu.FallbackNorm
public import Vu.SoftRowSum
namespace Vu
open Finset

/-- Lemma 4.6 for the actual completed matrix on the extracted pieces. -/
public theorem constructed_matrix_norm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D r k₀ K k Rmax : ℕ) (lam ω ρ δ b η : ℝ)
    (h : HardDecomposition G D r k₀ K k Rmax lam ω ρ δ b η)
    (hD : 0 < D) (hr : 0 < r) (hk : 0 < k₀) (hK : 0 < K)
    (hl : 0 ≤ lam) (hω : 0 ≤ ω) (hρ : 0 < ρ) (hrho : ρ ≤ 1) (hd : 0 < δ) (hd₁ : δ ≤ 1)
    (budget : lam + ((r:ℝ)^3/δ+r^2)*ω + 2*r/k₀ + (r+1)/(D:ℝ) +
      2*r*((4*ρ)^(1/3:ℝ)/δ+3*ρ^(1/4:ℝ)) ≤ η)
    (T : Finset V) (hT : T.card ≤ D) :
    RowNormLE (partitionSoftMatrix G h.pieces h.partition K (ω*D) ρ δ) T (η*D) := by
  classical
  letI := pieceOrder h.pieces
  let P (i : ↥h.pieces) := i.val
  let R := h.partition
  let z := ω*D
  let H := partitionHardGraph G h.pieces R K z ρ δ
  let A x y := ∑ i, regularPieceMatrix G P R K z ρ δ i x y
  let E := exceptionalCorrection G P R K z ρ δ
  let F x y := ∑ i, fallbackPiece G P R H K z ρ δ i x y
  let U (x y : V) : ℝ := if (uncoveredGraph G h.pieces).Adj x y then -1 else 0
  let diag (x y : V) : ℝ := if x=y then -1 else 0
  have hp (i : ↥h.pieces) := (h.extracted.1 i.val i.property).2.2.1
  have hm (x : V) : (univ.filter fun i => x ∈ P i).card ≤ r := by
    dsimp only [P]; rw [univ_eq_attach,filter_attach (fun Q : Finset V => x ∈ Q) h.pieces,card_map,card_attach]
    exact h.multiplicity x
  have ha := regular_piece_sum_norm G P R D r K z ρ δ hρ hd hp hm T
  have he := exceptional_correction_norm G P R D r K hr ω ρ δ hω hd hd₁ hm T
  have hf := fallback_sum_norm G P R D r k₀ K z ρ δ hρ hrho hK hk hp hm h.numClasses h.maxClass h.irregularArea T
  have hu : RowNormLE U T (lam*D) := by
    have hn := row_norm_neg (h.extracted.2.2 T hT)
    convert hn using 1
    funext x y
    by_cases hh : (uncoveredGraph G h.pieces).Adj x y <;> simp [U,hh]
  have hnA : RowNormLE A T _ := ha
  have hnE : RowNormLE E T _ := he
  have hnF : RowNormLE F T _ := hf
  have hn := row_norm_add (by positivity) (by positivity)
    (row_norm_add (by positivity) (by positivity)
      (row_norm_add (by positivity) (by positivity)
        (row_norm_add (by positivity) (by positivity) hnA hnE) hnF) hu)
    (row_norm_diagonal (V := V) T)
  have heq : partitionSoftMatrix G h.pieces R K z ρ δ =
      fun x y => A x y + E x y + F x y + U x y + diag x y := by
    funext x y
    have ident := matrix_assembly_identity G P R K z ρ δ hd
      (fun i A ha j _ => h.refines i A ha j.val j.property) x y
    have hunc : (uncoveredGraph G h.pieces).Adj x y ↔ G.Adj x y ∧ ¬(jointPieces P x y).Nonempty := by
      change (G.Adj x y ∧ ∀ Q ∈ h.pieces, x ∈ Q → y ∉ Q) ↔ _
      simp [jointPieces,P,Finset.filter_nonempty_iff,Subtype.exists]
      grind
    apply ident.trans
    simp only [A,E,F,U,diag,H,R,P,z,hunc]; rfl
  rw [heq]
  apply row_norm_mono hn (by positivity)
  apply le_trans _ (mul_le_mul_of_nonneg_right budget (Nat.cast_nonneg D))
  apply le_of_eq
  have hD' : (D:ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
  field_simp
  <;> ring

/-- Proposition 3.1, with b,R,C fixed before η and all four structural
conditions holding for the same graph, matrix and test family. -/
public theorem graph_decomposition : GraphDecompositionTheorem := by
  classical
  intro ε hε hε₁
  let δ := ε/200
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd₁ : δ ≤ 1/200 := by dsimp [δ]; linarith
  refine ⟨ε/2,ε/8,⌈4/ε⌉₊+2,max 10 (2/δ),⟨by positivity,by linarith⟩,⟨by positivity,by linarith⟩,
    le_trans (by norm_num : (2:ℝ) ≤ 10) (le_max_left _ _),?_⟩
  intro η hη
  let lam : ℝ := min (η/10) (1/2)
  let r := ⌈1/(lam^2/8)⌉₊
  have hl : 0 < lam := lt_min (by positivity) (by norm_num)
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨ω,ρ,k₀,K,D₀,hω,hρ,hrho,hk,hK,ho,hs,hD₀⟩ := partial_decomposition ε η hε hε₁ hη
  refine ⟨max 1 D₀,?_⟩
  intro D hD V _ G _ hdeg k
  have hpos : 0 < D := (le_max_left 1 _).trans hD
  obtain ⟨hbudget,hgraphs⟩ := hD₀ D ((le_max_right _ _).trans hD)
  obtain ⟨hlo,hhi,⟨h⟩⟩ := hgraphs V G hdeg
  refine ⟨hlo,hhi,?_⟩
  apply decomposition_of_soft_norm G D r k₀ K k _ lam ω ρ δ (ε/8) η hpos hd hd₁ hω.le ho hs hdeg h
  exact constructed_matrix_norm G D r k₀ K k _ lam ω ρ δ (ε/8) η h hpos hr hk hK hl.le hω.le hρ
    (by linarith) hd (by linarith) hbudget

/-- Theorem 1.1 now reduces to the coloring proposition alone. -/
public theorem main_of_coloring (hc : ColoringFromDecompositionTheorem) : FixedRatioBound :=
  main_of_decomposition_and_coloring graph_decomposition hc
end Vu
