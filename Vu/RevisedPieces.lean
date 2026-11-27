module
public import Vu.PieceFamily
namespace Vu.Revised
open Finset
/-- The three properties in Lemma 4.1. The incidence budget is recorded
per vertex and is stronger than the uniform multiplicity bound. -/
@[expose] public def PieceFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : ℕ) (q K : ℝ) (F : Finset (Finset V)) : Prop := by
  classical
  exact
    (∀ P ∈ F, P.Nonempty ∧ q * D ≤ P.card ∧ P.card ≤ 2*D ∧
      ∀ x ∈ P, q * D ≤ ((P.filter (G.Adj x)).card : ℝ)) ∧
    (∀ x : V, q * D * ((F.filter fun P => x ∈ P).card : ℝ) ≤ G.degree x) ∧
    ∀ X Y : Finset V, X.card ≤ D → Y.card ≤ D →
      (∑ x ∈ X, ∑ y ∈ Y, if (uncoveredGraph G F).Adj x y then (1:ℝ) else 0) ≤ K

private theorem build_piece_family {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (hD : 0 < D) (lam : ℝ) (hlam : 0 < lam) (G : SimpleGraph V) :
    (by classical exact ∀ x, G.degree x ≤ D) →
      ∃ F, PieceFamily G D (lam/8) (lam*D^2) F := by
  classical
  let q := lam / 8
  have hq : 0 < q := by dsimp [q]; positivity
  induction G using WellFoundedLT.induction with
  | ind G ih =>
    intro hdeg
    by_cases stop : ∀ X Y : Finset V, X.card ≤ D → Y.card ≤ D →
        (∑ x ∈ X, ∑ y ∈ Y, if G.Adj x y then (1:ℝ) else 0) ≤ lam*D^2
    · refine ⟨∅, (by simp), (by simp), ?_⟩
      simpa [uncoveredGraph] using stop
    · push Not at stop
      obtain ⟨X,Y,hX,hY,hmass⟩ := stop
      let U := X ∪ Y
      have hU' : U.card ≤ 2*D := (card_union_le ..).trans (by omega)
      have hc : 2*(q*D)*U.card < internalMass G U := by
        have hm : (∑ x ∈ X, ∑ y ∈ Y, if G.Adj x y then (1:ℝ) else 0) ≤ internalMass G U := by
          apply le_trans (sum_le_sum (fun x _ => sum_le_sum_of_subset_of_nonneg (t := U) (f := fun y => if G.Adj x y then (1:ℝ) else 0)
            (show Y ⊆ U from subset_union_right) (fun y _ _ => by split <;> norm_num)))
          exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun x _ _ => sum_nonneg fun y _ => by split <;> norm_num)
        apply lt_of_le_of_lt _ (hmass.trans_le hm)
        have hu : (U.card:ℝ) ≤ 2*D := by exact_mod_cast hU'
        have hh := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2*(q*D))
        dsimp [q] at hh ⊢
        nlinarith only [hh,mul_nonneg hlam.le (sq_nonneg (D:ℝ))]
      obtain ⟨P, hPU, hp, hcore⟩ := exists_dense_core G (q*D) U hc
      let J := uncoveredGraph G {P}
      have hle : J ≤ G := fun _ _ h => h.1
      obtain ⟨u, hu⟩ := hp
      have hpos : 0 < q * (D : ℝ) := mul_pos hq (Nat.cast_pos.mpr hD)
      have hmany : 0 < (P.filter (G.Adj u)).card := by exact_mod_cast hpos.trans_le (hcore u hu)
      obtain ⟨z, hz⟩ := card_pos.mp hmany
      have hjlt : J < G := lt_of_le_not_ge hle (fun h =>
        (h (mem_filter.mp hz).2).2 P (mem_singleton_self _) hu (mem_filter.mp hz).1)
      obtain ⟨F, hF, hbudget, hnorm⟩ := ih J hjlt (fun x => (degree_subgraph hle x).trans (hdeg x))
      refine ⟨insert P F, ?_, ?_, ?_⟩
      · intro S hS
        rcases mem_insert.mp hS with rfl | hSF
        · exact ⟨⟨u, hu⟩, (hcore u hu).trans (Nat.cast_le.mpr (card_le_card (filter_subset _ _))),
            (card_le_card hPU).trans hU', hcore⟩
        · obtain ⟨hs,hlo,hhi,hmin⟩ := hF S hSF
          refine ⟨hs,hlo,hhi,?_⟩
          intro y hy
          apply (hmin y hy).trans (Nat.cast_le.mpr (card_le_card ?_))
          intro z hz
          exact mem_filter.mpr ⟨(mem_filter.mp hz).1, hle (mem_filter.mp hz).2⟩
      · intro x
        change q * D * _ ≤ _
        by_cases hx : x ∈ P
        · have hcard : (((insert P F).filter fun S => x ∈ S).card : ℝ) ≤
              ((F.filter fun S => x ∈ S).card : ℝ) + 1 := by
            rw [filter_insert, ite_eq_left_iff.mpr (fun h => False.elim (h hx))]
            exact_mod_cast card_insert_le P (F.filter fun S => x ∈ S)
          have hm := mul_le_mul_of_nonneg_left hcard hpos.le
          have hdel : (J.degree x : ℝ) + (P.filter (G.Adj x)).card = G.degree x := by
            exact_mod_cast degree_after_removal G P x hx
          have hb : q * D * ((F.filter fun S => x ∈ S).card : ℝ) ≤ J.degree x := by simpa only [q] using hbudget x
          rw [mul_add, mul_one] at hm
          exact hm.trans ((add_le_add hb (hcore x hx)).trans_eq hdel)
        · simp only [filter_insert, hx, ite_false]
          exact (hbudget x).trans (Nat.cast_le.mpr (degree_subgraph hle x))
      · intro X Y hX hY
        simpa only [uncovered_insert, J] using hnorm X Y hX hY


/-- Lemma 4.1, including the explicit bound on piece multiplicities, the
residual ordered-edge bound on every rectangle of side sizes at most D. -/
public theorem extracting_dense_pieces {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hdeg : ∀ x, G.degree x ≤ D)
    (lam : ℝ) (hlam : 0 < lam) :
    let q := lam/8
    ∃ F, PieceFamily G D q (lam*D^2) F ∧
      ∀ x : V, (F.filter fun P => x ∈ P).card ≤ ⌈1/q⌉₊ := by
  classical
  dsimp only
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hno (x y : V) : ¬ G.Adj x y := fun h =>
      (Nat.not_lt_of_ge (hdeg x)) h.degree_pos_left
    refine ⟨∅, ⟨by simp, by simp, ?_⟩, by simp⟩
    intro X Y _ _
    simp [uncoveredGraph, hno]
  · let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    have hd (x : V) : G.degree x ≤ D := by
      refine Eq.trans_le ?_ (hdeg x)
      congr 1
      exact Subsingleton.elim _ _
    obtain ⟨F, hF⟩ := build_piece_family D hD lam hlam G hd
    refine ⟨F, hF, ?_⟩
    intro x
    have hq : 0 < lam/8 := by positivity
    have hp : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
    have hb := (hF.2.1 x).trans (Nat.cast_le.mpr (hd x))
    have ha : ((F.filter fun P => x ∈ P).card : ℝ) ≤ 1/(lam/8) := by
      apply (le_div_iff₀ hq).mpr
      apply (mul_le_mul_iff_of_pos_right hp).mp
      simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using hb
    exact Nat.cast_le.mp (ha.trans (Nat.le_ceil _))

end Vu.Revised
