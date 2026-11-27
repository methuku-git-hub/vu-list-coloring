module
public import Vu.RevisedPartial
public import Vu.RevisedCut
namespace Vu.Revised
open Finset
public theorem constructed_matrix_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D r k₀ K k Rmax : ℕ) (lam ω ρ δ b η : ℝ)
    (h : HardDecomposition G D r k₀ K k Rmax lam ω ρ δ b η)
    (hD : 0 < D) (hr : 0 < r) (hk : 0 < k₀) (hK : 0 < K)
    (hl : 0 ≤ lam) (hω : 0 ≤ ω) (hρ : 0 < ρ) (hrho : ρ ≤ 1) (hd : 0 < δ) (hd₁ : δ ≤ 1)
    (budget : lam + ((r:ℝ)^3/δ+r^2)*ω + 2*r/k₀ + (r+1)/(D:ℝ) +
      2*r*((4*ρ)^(1/3:ℝ)/δ+3*ρ^(1/4:ℝ)) ≤ η)
    (T X Y : Finset V) (hT : T.card ≤ D) (hX : X ⊆ T) (hY : Y.card ≤ D) :
    |∑ x ∈ X, ∑ y ∈ Y, partitionSoftMatrix G h.pieces h.partition K (ω*D) ρ δ x y| ≤ η*D^2 := by
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
  let N x y := A x y + E x y + F x y + diag x y
  have hn := row_norm_add (by positivity) (by positivity)
    (row_norm_add (by positivity) (by positivity)
      (row_norm_add (by positivity) (by positivity) ha he) hf)
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
  have hsum : (∑ x ∈ X, ∑ y ∈ Y, partitionSoftMatrix G h.pieces R K z ρ δ x y) =
      (∑ x ∈ X, ∑ y ∈ Y, N x y) + ∑ x ∈ X, ∑ y ∈ Y, U x y := by
    rw [heq,←sum_add_distrib]
    apply sum_congr rfl
    intro x _
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun y _ => by dsimp [N]; ring)
  have hnX := rectangle_of_rows N T X Y D _ (by positivity) hT hX hY hn
  have hu : |∑ x ∈ X, ∑ y ∈ Y, U x y| ≤ lam*D^2 := by
    let J := uncoveredGraph G h.pieces
    have he (x y : V) : U x y = -(if J.Adj x y then (1:ℝ) else 0) := by
      by_cases hg : J.Adj x y <;> simp [U,J] at hg ⊢ <;> simp [hg]
    simp_rw [he,sum_neg_distrib]
    rw [abs_neg,abs_of_nonneg (sum_nonneg fun x _ => sum_nonneg fun y _ => by split <;> norm_num)]
    exact h.extracted.2.2 X Y ((card_le_card hX).trans hT) hY
  rw [hsum]
  apply (abs_add_le ..).trans ((add_le_add hnX hu).trans ?_)
  apply le_trans _ (mul_le_mul_of_nonneg_right budget (sq_nonneg (D:ℝ)))
  apply le_of_eq
  have hD' : (D:ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
  field_simp
  <;> ring
end Vu.Revised
