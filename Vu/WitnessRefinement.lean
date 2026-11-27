module
public import Vu.PartitionEnergy
namespace Vu.Revised
open Finset Finpartition
variable {V : Type*} [Fintype V] [DecidableEq V] {S : Finset V}
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two subsets witnessing failure of regularity on an ordered cell. -/
@[expose] public def witness (ρ : ℝ) (A B X Y : Finset V) : Prop :=
  X ⊆ A ∧ Y ⊆ B ∧ ρ*A.card ≤ X.card ∧ ρ*B.card ≤ Y.card ∧
    ρ < |crossDensity G X Y-crossDensity G A B|

private theorem reverse_witness {ρ : ℝ} {A B X Y : Finset V}
    (h : witness G ρ A B X Y) : witness G ρ B A Y X :=
  ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,by
    simpa only [density_swap G Y X,density_swap G B A] using h.2.2.2.2⟩

private theorem exists_witness (ρ : ℝ) (A B : Finset V) :
    ∃ w : Finset V × Finset V, irregularPair G ρ A B → witness G ρ A B w.1 w.2 := by
  by_cases h : irregularPair G ρ A B
  · obtain ⟨X,hX,Y,hY,hs,ht,hb⟩ := h
    exact ⟨(X,Y),fun _ => ⟨hX,hY,hs,ht,hb⟩⟩
  · exact ⟨(∅,∅),fun hi => (h hi).elim⟩

omit [Fintype V] in
private theorem split_respects (R : Finpartition S) (cuts : Finset V → Finset (Finset V))
    {A X : Finset V} (hA : A ∈ R.parts) (hX : X ⊆ A) (hc : X ∈ cuts A) :
    respects (R.bind fun B _ => atomise B (cuts B)) X := by
  classical
  intro U hu
  obtain ⟨B,hB,hu⟩ := mem_bind.mp hu
  by_cases eq : B=A
  · subst B
    obtain ⟨F,_,rfl⟩ := (mem_atomise.mp hu).2
    by_cases hf : X ∈ F
    · exact Or.inl fun x hx => ((mem_filter.mp hx).2 X hc).mp hf
    · exact Or.inr (disjoint_left.mpr fun x hx h => hf (((mem_filter.mp hx).2 X hc).mpr h))
  · exact Or.inr ((R.supIndep.pairwiseDisjoint hB hA eq).mono ((atomise B (cuts B)).le hu) hX)

/-- Split each class at one witness per partner, with one extra witness for its
diagonal pair. The same two witnesses serve the reverse ordered pair. -/
public theorem witness_refinement (R : Finpartition S) (ρ : ℝ) :
    ∃ Q : Finpartition S, Q ≤ R ∧ Q.parts.card ≤ R.parts.card*2^(R.parts.card+1) ∧
    ∀ A ∈ R.parts, ∀ B ∈ R.parts, irregularPair G ρ A B →
      ∃ X Y, witness G ρ A B X Y ∧ respects Q X ∧ respects Q Y := by
  classical
  choose w hw using exists_witness G ρ
  let rank := Fintype.equivFin (Finset V)
  let row (A B : Finset V) := if rank A ≤ rank B then (w A B).1 else (w B A).2
  let cuts (A : Finset V) := insert (w A A).2 (R.parts.image (row A))
  let Q := R.bind fun A _ => atomise A (cuts A)
  have hrow A B (hb : B ∈ R.parts) : row A B ∈ cuts A :=
    mem_insert_of_mem (mem_image_of_mem _ hb)
  have hvalid A (hA : A ∈ R.parts) B (hB : B ∈ R.parts) (hle : rank A ≤ rank B)
      (hi : irregularPair G ρ A B) :
      witness G ρ A B (w A B).1 (w A B).2 ∧ respects Q (w A B).1 ∧ respects Q (w A B).2 := by
    have hwit := hw A B hi
    refine ⟨hwit,split_respects R cuts hA hwit.1 (by simpa [row,hle] using hrow A B hB),
      split_respects R cuts hB hwit.2.1 ?_⟩
    by_cases he : A=B
    · subst B; exact mem_insert_self ..
    · have hn : ¬rank B ≤ rank A := fun h => he (rank.injective (le_antisymm hle h))
      simpa [row,hn] using hrow B A hA
  refine ⟨Q,?_,?_,?_⟩
  · intro U hu
    obtain ⟨A,hA,hu⟩ := mem_bind.mp hu
    exact ⟨A,hA,(atomise A (cuts A)).le hu⟩
  · rw [show Q.parts.card = _ from card_bind ..]
    apply (sum_le_sum (g := fun _ => 2^(R.parts.card+1)) (fun A _ => ?_)).trans_eq
    · simp
    · exact (card_atomise_le ..).trans (Nat.pow_le_pow_right (by decide)
        ((card_insert_le ..).trans (Nat.add_le_add_right card_image_le 1)))
  · intro A hA B hB hi
    rcases le_total (rank A) (rank B) with h | h
    · exact ⟨_,_,hvalid A hA B hB h hi⟩
    · obtain ⟨hw,hx,hy⟩ := hvalid B hB A hA h (irregular_swap G ρ A B hi)
      exact ⟨_,_,reverse_witness G hw,hy,hx⟩

end Vu.Revised
