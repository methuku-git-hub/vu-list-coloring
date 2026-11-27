module
public import Vu.GoodClasses
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] public noncomputable def regularPartners (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} (R : Finpartition P) (ρ : ℝ) (A : Finset V) : Finset (Finset V) := by
  classical exact R.parts.filter fun B => ¬ irregularPair G ρ A B

@[expose] public noncomputable def regularRowError (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} (R : Finpartition P) (ρ : ℝ) (A : Finset V) (x : V) : ℝ :=
  ∑ B ∈ regularPartners G R ρ A, |((G.neighborFinset x ∩ B).card : ℝ) - crossDensity G A B * B.card|

/-- The good-row bound applied to all regular classes of the actual partition. -/
public theorem irregular_row_count (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (R : Finpartition P) (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (A : Finset V) (ha : A ∈ R.parts) :
    ((A.filter fun x => 4*√ρ*P.card < regularRowError G R ρ A x).card : ℝ) ≤ √ρ*A.card := by
  classical
  let F := regularPartners G R ρ A
  have hsub : F ⊆ R.parts := filter_subset _ _
  have hsum : ∑ b : ↥F, ((b.val).card : ℝ) ≤ P.card := by
    rw [sum_coe_sort F (fun U : Finset V => (U.card : ℝ))]
    exact_mod_cast (sum_le_sum_of_subset (f := card) hsub).trans_eq R.sum_card_parts
  have hh := bad_rows_of_regular_pairs G A (fun b : ↥F => b.val) ρ P.card
    (nonempty_iff_ne_empty.mpr (R.ne_empty ha))
    (fun b => nonempty_iff_ne_empty.mpr (R.ne_empty (hsub b.property))) hρ hρ₁
    (Nat.cast_pos.mpr (card_pos.mpr ((nonempty_iff_ne_empty.mpr (R.ne_empty ha)).mono (R.le ha)))) hsum (by
      intro b X hx Y hy hX hY
      by_contra! h
      exact (mem_filter.mp b.property).2 ⟨X,hx,Y,hy,hX,hY,h⟩)
  have sum_eq (x : V) := sum_coe_sort F (fun b : Finset V => |((G.neighborFinset x ∩ b).card : ℝ) - crossDensity G A b * b.card|)
  simp_rw [sum_eq] at hh
  exact hh


@[expose] public noncomputable def goodVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} (R : Finpartition P) (ρ : ℝ) : Finset V := by
  classical exact P.filter fun x => regularRowError G R ρ (R.part x) x ≤ 4*√ρ*P.card

public theorem nongood_vertices_bound (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (R : Finpartition P) (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ((P \ goodVertices G R ρ).card : ℝ) ≤ √ρ*P.card := by
  classical
  let bad (A : Finset V) := A.filter fun x => 4*√ρ*P.card < regularRowError G R ρ A x
  have sub : P \ goodVertices G R ρ ⊆ R.parts.biUnion bad := by
    intro x hx
    obtain ⟨hp,hn⟩ := mem_sdiff.mp hx
    exact mem_biUnion.mpr ⟨R.part x,R.part_mem.mpr hp,mem_filter.mpr ⟨R.mem_part hp,
      lt_of_not_ge (fun h => hn (mem_filter.mpr ⟨hp,h⟩))⟩⟩
  apply (Nat.cast_le.mpr ((card_le_card sub).trans card_biUnion_le)).trans
  push_cast
  apply (sum_le_sum (fun A hA => irregular_row_count G P R ρ hρ hρ₁ A hA)).trans_eq
  rw [←mul_sum]
  congr 1
  exact_mod_cast R.sum_card_parts
end Vu.Revised
