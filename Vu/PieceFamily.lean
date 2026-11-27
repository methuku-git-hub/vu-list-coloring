module

public import Vu.DensePieces
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

namespace Vu
open Finset

/-- The graph of edges whose endpoints are in no common member of F. -/
@[expose] public def uncoveredGraph {V : Type*} (G : SimpleGraph V) (F : Finset (Finset V)) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∀ P ∈ F, x ∈ P → y ∉ P
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun P hp hy hx => h.2 P hp hx hy⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

public theorem uncovered_insert {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (P : Finset V) (F : Finset (Finset V)) :
    uncoveredGraph G (insert P F) = uncoveredGraph (uncoveredGraph G {P}) F := by
  ext x y
  simp only [uncoveredGraph, mem_insert, mem_singleton, forall_eq, or_imp, forall_and]
  tauto

public theorem degree_subgraph {V : Type*} [Fintype V] {J G : SimpleGraph V}
    [DecidableRel J.Adj] [DecidableRel G.Adj] (h : J ≤ G) (x : V) : J.degree x ≤ G.degree x := by
  apply card_le_card (s := J.neighborFinset x) (t := G.neighborFinset x)
  intro z hz
  exact (G.mem_neighborFinset x z).mpr (h ((J.mem_neighborFinset x z).mp hz))

/-- The local degree budget used in the extraction. -/
public theorem degree_after_removal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) (x : V) (hx : x ∈ P) :
    (by classical exact (uncoveredGraph G {P}).degree x) + (P.filter (G.Adj x)).card = G.degree x := by
  classical
  let N := G.neighborFinset x
  have hout : (uncoveredGraph G {P}).neighborFinset x = N.filter (fun y => y ∉ P) := by
    ext y
    rw [(uncoveredGraph G {P}).mem_neighborFinset x y, mem_filter]
    change (G.Adj x y ∧ ∀ S ∈ ({P} : Finset (Finset V)), x ∈ S → y ∉ S) ↔ y ∈ G.neighborFinset x ∧ y ∉ P
    simp [hx]
  have hin : P.filter (G.Adj x) = N.filter (fun y => y ∈ P) := by
    ext y
    simp [N, and_comm]
  change ((uncoveredGraph G {P}).neighborFinset x).card + _ = N.card
  rw [hout, hin, add_comm]
  exact card_filter_add_card_filter_not _

/-- The three properties in Lemma 4.1. The incidence budget is recorded
per vertex and is stronger than the uniform multiplicity bound. -/
@[expose] public def PieceFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : ℕ) (q K : ℝ) (F : Finset (Finset V)) : Prop := by
  classical
  exact
    (∀ P ∈ F, P.Nonempty ∧ q * D ≤ P.card ∧ P.card ≤ 2*D ∧
      (∃ x : V, ∀ y ∈ P, ∃ p : G.Walk x y, p.length ≤ 2) ∧
      ∀ x ∈ P, q * D ≤ ((P.filter (G.Adj x)).card : ℝ)) ∧
    (∀ x : V, q * D * ((F.filter fun P => x ∈ P).card : ℝ) ≤ G.degree x) ∧
    ∀ T : Finset V, T.card ≤ D →
      RowNormLE (fun x y => if (uncoveredGraph G F).Adj x y then 1 else 0) T K

private theorem build_piece_family {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (hD : 0 < D) (lam : ℝ) (hlam : 0 < lam) (G : SimpleGraph V) :
    (by classical exact ∀ x, G.degree x ≤ D) →
      ∃ F, PieceFamily G D (lam^2/8) (lam*D) F := by
  classical
  let q := lam^2 / 8
  have hq : 0 < q := by dsimp [q]; positivity
  induction G using WellFoundedLT.induction with
  | ind G ih =>
    intro hdeg
    by_cases stop : ∀ T : Finset V, T.card ≤ D →
        RowNormLE (fun x y => if G.Adj x y then 1 else 0) T (lam*D)
    · refine ⟨∅, (by simp), (by simp), ?_⟩
      simpa [uncoveredGraph] using stop
    · push Not at stop
      obtain ⟨T, hT, hTfail⟩ := stop
      obtain ⟨v, _, U, hU, hball, hmass⟩ := exists_dense_ball_of_norm_failure G T (lam*D) hTfail
      have hU' : U.card ≤ 2*D := by have := hdeg v; omega
      have hU'' : (U.card : ℝ) ≤ 2 * D := by exact_mod_cast hU'
      have hc : 2 * (q * D) * U.card < internalMass G U := by
        have hm := mul_le_mul_of_nonneg_left hU'' (by positivity : 0 ≤ 2 * (q * D))
        dsimp [q] at hm ⊢
        nlinarith [sq_nonneg (lam * (D : ℝ))]
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
            (card_le_card hPU).trans hU', ⟨v, fun y hy => hball y (hPU hy)⟩, hcore⟩
        · obtain ⟨hs, hlo, hhi, ⟨v', hloc⟩, hmin⟩ := hF S hSF
          refine ⟨hs, hlo, hhi, ⟨v', ?_⟩, ?_⟩
          · intro y hy
            obtain ⟨p, hlen⟩ := hloc y hy
            exact ⟨p.mapLe hle, (p.length_mapLe hle).le.trans hlen⟩
          · intro y hy
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
      · intro T hT
        simpa only [uncovered_insert, J] using hnorm T hT


/-- Lemma 4.1, including the explicit bound on piece multiplicities, the
radius-two witnesses, and the rooted norm bound for every row set of size at most D. -/
public theorem extracting_dense_pieces {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hdeg : ∀ x, G.degree x ≤ D)
    (lam : ℝ) (hlam : 0 < lam) :
    let q := lam^2/8
    ∃ F, PieceFamily G D q (lam*D) F ∧
      ∀ x : V, (F.filter fun P => x ∈ P).card ≤ ⌈1/q⌉₊ := by
  classical
  dsimp only
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hno (x y : V) : ¬ G.Adj x y := fun h =>
      (Nat.not_lt_of_ge (hdeg x)) h.degree_pos_left
    refine ⟨∅, ⟨by simp, by simp, ?_⟩, by simp⟩
    intro T _ f
    simp [uncoveredGraph, hno]
  · let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    have hd (x : V) : G.degree x ≤ D := by
      refine Eq.trans_le ?_ (hdeg x)
      congr 1
      exact Subsingleton.elim _ _
    obtain ⟨F, hF⟩ := build_piece_family D hD lam hlam G hd
    refine ⟨F, hF, ?_⟩
    intro x
    have hq : 0 < lam^2/8 := by positivity
    have hp : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
    have hb := (hF.2.1 x).trans (Nat.cast_le.mpr (hd x))
    have ha : ((F.filter fun P => x ∈ P).card : ℝ) ≤ 1/(lam^2/8) := by
      apply (le_div_iff₀ hq).mpr
      apply (mul_le_mul_iff_of_pos_right hp).mp
      simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using hb
    exact Nat.cast_le.mp (ha.trans (Nat.le_ceil _))

end Vu
