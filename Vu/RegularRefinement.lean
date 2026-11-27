module
public import Vu.RegularRows
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

namespace Vu
open Finset

/-- Conversion of the ordered-incidence density used in Section 4 to the
density of mathlib's Szemerédi regularity lemma. -/
public theorem crossDensity_eq_edgeDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    crossDensity G A B = (G.edgeDensity A B : ℝ) := by
  classical
  rw [crossDensity,G.edgeDensity_def]
  push_cast
  congr 1
  have edges : (G.interedges A B).card = ∑ x ∈ A, (G.neighborFinset x ∩ B).card := by
    rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion, card_biUnion]
    · apply sum_congr rfl
      intro x _
      rw [card_map]
      congr 1
      ext y
      simp [and_comm]
    · intro x _ y _ hne
      apply Finset.disjoint_left.mpr
      intro z hx hy
      obtain ⟨i,_,rfl⟩ := mem_map.mp hx
      obtain ⟨j,_,he⟩ := mem_map.mp hy
      exact hne (congrArg Prod.fst he.symm)
  exact_mod_cast edges.symm

/-- Inherit the regularity estimate after intersecting a uniform pair
with the prescribed initial partition. Both refined cells must occupy
at least a γ fraction of their parent. -/
public theorem uniform_pair_slicing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B C E : Finset V) (ε γ ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hsmall : ε ≤ γ*ρ) (hdist : 2*ε ≤ ρ)
    (h : G.IsUniform ε A B) (hC : C ⊆ A) (hE : E ⊆ B)
    (hc : γ*A.card ≤ C.card) (he : γ*B.card ≤ E.card) :
    ∀ X ⊆ C, ∀ Y ⊆ E, ρ*C.card ≤ X.card → ρ*E.card ≤ Y.card →
      |crossDensity G X Y - crossDensity G C E| ≤ ρ := by
  intro X hx Y hy hX hY
  have trans_size {p c x : ℕ} (hc : γ*p ≤ c) (hx : ρ*c ≤ x) :
      (p : ℝ)*ε ≤ x := by
    calc
      _ ≤ (p : ℝ)*(γ*ρ) := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
      _ = ρ*(γ*p) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hc hρ).trans hx
  have hcX := trans_size hc hX
  have heY := trans_size he hY
  have hc' := trans_size hc (x := C.card) (by simpa using mul_le_mul_of_nonneg_right hρ₁ (Nat.cast_nonneg C.card))
  have he' := trans_size he (x := E.card) (by simpa using mul_le_mul_of_nonneg_right hρ₁ (Nat.cast_nonneg E.card))
  simp only [crossDensity_eq_edgeDensity]
  have h₁ := h (hx.trans hC) (hy.trans hE) hcX heY
  have h₂ := h hC hE hc' he'
  exact (abs_sub_le _ (G.edgeDensity A B : ℝ) _).trans (by rw [abs_sub_comm (G.edgeDensity A B : ℝ)]; linarith)

/-- Intersecting a partition of bounded size with an arbitrary prescribed
partition gives a common refinement with at most the product of the sizes. -/
public theorem common_refinement_size {V : Type*} [DecidableEq V] (S : Finset V)
    (P Q : Finpartition S) : (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card := by
  rw [Finpartition.parts_inf, ← card_product]
  exact (card_le_card (erase_subset ..)).trans card_image_le


/-- Vertices in small cells of the common refinement occupy at most
γ times the size of the ground set times the number of initial classes. -/
public theorem small_refinement_cells {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (univ : Finset V)) (γ : ℝ) (hγ : 0 ≤ γ) :
    let small := univ.filter fun x : V => (((P.part x) ∩ (Q.part x)).card : ℝ) < γ*(P.part x).card
    (small.card : ℝ) ≤ (Q.parts.card : ℝ)*γ*Fintype.card V := by
  classical
  intro small
  let tiny (p q : Finset V) := if ((p ∩ q).card : ℝ) < γ*p.card then p ∩ q else ∅
  have cover : small ⊆ P.parts.biUnion (fun p => Q.parts.biUnion (tiny p)) := by
    intro x hx
    have h := (mem_filter.mp hx).2
    apply mem_biUnion.mpr ⟨P.part x,P.part_mem.mpr (mem_univ x),?_⟩
    apply mem_biUnion.mpr ⟨Q.part x,Q.part_mem.mpr (mem_univ x),?_⟩
    simp [tiny,h]
  have child (p q : Finset V) : ((tiny p q).card : ℝ) ≤ γ*p.card := by
    dsimp [tiny]; split
    next h => exact h.le
    next => simp [mul_nonneg hγ (Nat.cast_nonneg _)]
  have row (p : Finset V) : ((Q.parts.biUnion (tiny p)).card : ℝ) ≤ (Q.parts.card : ℝ)*γ*p.card := by
    have hh : ((Q.parts.biUnion (tiny p)).card : ℝ) ≤ ∑ q ∈ Q.parts, ((tiny p q).card : ℝ) := by exact_mod_cast card_biUnion_le
    exact (hh.trans (sum_le_sum (fun q _ => child p q))).trans_eq (by simp [mul_assoc])
  have htop : (small.card : ℝ) ≤ ∑ p ∈ P.parts, ((Q.parts.biUnion (tiny p)).card : ℝ) := by
    exact_mod_cast (card_le_card cover).trans card_biUnion_le
  apply (htop.trans (sum_le_sum (fun p _ => row p))).trans_eq
  rw [← mul_sum]
  congr 1
  exact_mod_cast P.sum_card_parts.trans card_univ

/-- The contribution from a family of parent rectangles is bounded by its
cardinality times the square of the largest parent size. -/
public theorem parent_rectangle_bound {V : Type*} [DecidableEq V]
    (E : Finset (Finset V × Finset V)) (m : ℕ)
    (hE : ∀ e ∈ E, e.1.card ≤ m ∧ e.2.card ≤ m) :
    (E.biUnion fun e => e.1 ×ˢ e.2).card ≤ E.card*m^2 := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _e ∈ E, m^2 := by
      apply sum_le_sum
      intro e he
      simpa [pow_two] using Nat.mul_le_mul (hE e he).1 (hE e he).2
    _ = _ := by simp

/-- The only ordered vertex pairs that can lie in an irregular refined
rectangle are incident to a small refined cell, have the same parent, or
come from an irregular parent pair. This controls their actual total weight. -/
public theorem irregular_refined_vertex_pairs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P Q : Finpartition (univ : Finset V))
    (ε γ ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hsmall : ε ≤ γ*ρ) (hdist : 2*ε ≤ ρ)
    (m : ℕ) (hm : ∀ U ∈ P.parts, U.card ≤ m) :
    let cell x := P.part x ∩ Q.part x
    let small := univ.filter fun x => ((cell x).card : ℝ) < γ*(P.part x).card
    let irregular (x y : V) := ∃ X ⊆ cell x, ∃ Y ⊆ cell y,
      ρ*(cell x).card ≤ X.card ∧ ρ*(cell y).card ≤ Y.card ∧
      ρ < |crossDensity G X Y - crossDensity G (cell x) (cell y)|
    (by classical exact (univ.filter fun e : V × V => irregular e.1 e.2).card) ≤
      2*small.card*Fintype.card V + (P.parts.card + (P.nonUniforms G ε).card)*m^2 := by
  classical
  intro cell small irregular
  let diagonal := P.parts.image (fun p => (p,p))
  let bad := P.nonUniforms G ε
  let E := diagonal ∪ bad
  let rect := E.biUnion (fun e => e.1 ×ˢ e.2)
  have hrect : rect.card ≤ (P.parts.card + bad.card)*m^2 := by
    apply (parent_rectangle_bound E m ?_).trans
      (Nat.mul_le_mul_right _ ((card_union_le _ _).trans (Nat.add_le_add_right card_image_le _)))
    intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp he
      exact ⟨hm p hp,hm p hp⟩
    · have he' : e.1 ∈ P.parts ∧ e.2 ∈ P.parts ∧ e.1 ≠ e.2 ∧ ¬ G.IsUniform ε e.1 e.2 := by cases e; simpa [bad] using he
      obtain ⟨hp,hq,_⟩ := he'
      exact ⟨hm _ hp,hm _ hq⟩
  have cover : (univ.filter fun e : V × V => irregular e.1 e.2) ⊆
      ((small ×ˢ univ) ∪ (univ ×ˢ small)) ∪ rect := by
    rintro ⟨x,y⟩ hxy
    by_cases hx : x ∈ small
    · exact mem_union_left _ (mem_union_left _ (mem_product.mpr ⟨hx,mem_univ _⟩))
    by_cases hy : y ∈ small
    · exact mem_union_left _ (mem_union_right _ (mem_product.mpr ⟨mem_univ _,hy⟩))
    have hcx : γ*(P.part x).card ≤ (cell x).card := by simpa [small] using hx
    have hcy : γ*(P.part y).card ≤ (cell y).card := by simpa [small] using hy
    have hp (z : V) := P.part_mem.mpr (mem_univ z)
    have hpair : (P.part x,P.part y) ∈ E := by
      by_cases heq : P.part x = P.part y
      · exact mem_union_left _ (mem_image.mpr ⟨P.part x,hp x,by simp [heq]⟩)
      apply mem_union_right _
      simp only [bad, Finpartition.mk_mem_nonUniforms]
      refine ⟨hp x,hp y,heq,?_⟩
      intro hreg
      obtain ⟨X,hX,Y,hY,hx',hy',hf⟩ := (mem_filter.mp hxy).2
      exact (not_lt_of_ge (uniform_pair_slicing G _ _ _ _ ε γ ρ hρ hρ₁ hsmall hdist hreg
        inter_subset_left inter_subset_left hcx hcy X hX Y hY hx' hy')) hf
    exact mem_union_right _ (mem_biUnion.mpr ⟨_,hpair,mem_product.mpr
      ⟨P.mem_part (mem_univ x),P.mem_part (mem_univ y)⟩⟩)
  apply (card_le_card cover).trans ((card_union_le _ _).trans ?_)
  apply Nat.add_le_add _ hrect
  apply (card_union_le _ _).trans
  simp [two_mul,add_mul,Nat.mul_comm]
/-- Numerical estimate for the weighted irregular pairs in a common
refinement. Here t is the number of equitable parent classes, m their
maximum size, and b the number of ordered nonuniform parent pairs. -/
private theorem refinement_error (N t m b small : ℕ) (ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 ≤ ε) (ht : 16/ρ ≤ t) (hm : t*m ≤ 2*N)
    (hb : (b : ℝ) ≤ t^2*ε) (hs : (small : ℝ) ≤ ρ*N/8) (he : ε ≤ ρ/16) :
    ((2*small*N + (t+b)*m^2 : ℕ) : ℝ) ≤ ρ*(N : ℝ)^2 := by
  have ht' : 0 < (t : ℝ) := (div_pos (by norm_num) hρ).trans_le ht
  have hmt : (t : ℝ)*m ≤ 2*N := by exact_mod_cast hm
  have hsq : (t : ℝ)^2*m^2 ≤ 4*(N : ℝ)^2 := by
    have H := pow_le_pow_left₀ (show 0 ≤ (t : ℝ)*m by positivity) hmt 2
    nlinarith only [H]
  have htρ : 16 ≤ (t : ℝ)*ρ := (div_le_iff₀ hρ).mp ht
  have hdiag : (t : ℝ)*m^2 ≤ ρ*(N : ℝ)^2/4 := by
    apply (mul_le_mul_iff_of_pos_right ht').mp
    have H := mul_le_mul_of_nonneg_right htρ (sq_nonneg (N : ℝ))
    nlinarith only [hsq,H]
  have hirr : (b : ℝ)*m^2 ≤ ρ*(N : ℝ)^2/4 := by
    have H := mul_le_mul_of_nonneg_right hb (sq_nonneg (m : ℝ))
    have H' := mul_le_mul_of_nonneg_left hsq hε
    have H'' := mul_le_mul_of_nonneg_right he (sq_nonneg (N : ℝ))
    nlinarith only [H,H',H'']
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg N),hdiag,hirr,
    mul_nonneg hρ.le (sq_nonneg (N : ℝ))]

/-- Uniform refinement, in the equivalent form counting ordered pairs of
vertices. The auxiliary equitable partition may cut across the initial
partition Q. Its intersections with Q are the actual refinement R. -/
public theorem regular_refinement_vertices (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Q : Finpartition (univ : Finset V)), Q.parts.card ≤ m₀ →
      ∃ R : Finpartition (univ : Finset V), R ≤ Q ∧ R.parts.card ≤ K ∧
      (by classical exact ((univ.filter fun e : V × V => ∃ X ⊆ R.part e.1, ∃ Y ⊆ R.part e.2,
        ρ*(R.part e.1).card ≤ X.card ∧ ρ*(R.part e.2).card ≤ Y.card ∧
        ρ < |crossDensity G X Y - crossDensity G (R.part e.1) (R.part e.2)|).card : ℝ)) ≤
        ρ*(Fintype.card V : ℝ)^2 := by
  classical
  let γ := ρ/(8*m₀)
  let ε := min (γ*ρ) (ρ/16)
  let l := ⌈16/ρ⌉₊
  have h₀ : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have hγ : 0 < γ := div_pos hρ (by positivity)
  have he : 0 < ε := lt_min (mul_pos hγ hρ) (by positivity)
  refine ⟨max l (SzemerediRegularity.bound ε l * m₀), ?_⟩
  intro V _ _ G _ Q hQ
  let N := Fintype.card V
  by_cases hn : l ≤ N
  · obtain ⟨P,heq,hl,hbound,hu⟩ := szemeredi_regularity G he hn
    refine ⟨P ⊓ Q,inf_le_right,(common_refinement_size _ P Q).trans
      ((Nat.mul_le_mul hbound hQ).trans (le_max_right ..)),?_⟩
    let t := P.parts.card
    let m := N/t+1
    have hcell (x : V) : (P ⊓ Q).part x = P.part x ∩ Q.part x := by
      apply (P ⊓ Q).part_eq_of_mem _ (mem_inter.mpr ⟨P.mem_part (mem_univ _),Q.mem_part (mem_univ _)⟩)
      rw [Finpartition.parts_inf]
      apply mem_erase.mpr ⟨?_,mem_image.mpr ⟨(P.part x,Q.part x),mem_product.mpr
        ⟨P.part_mem.mpr (mem_univ _),Q.part_mem.mpr (mem_univ _)⟩,rfl⟩⟩
      exact ne_empty_of_mem (mem_inter.mpr ⟨P.mem_part (mem_univ x),Q.mem_part (mem_univ x)⟩)
    simp_rw [hcell]
    have hm (p : Finset V) (hp : p ∈ P.parts) : p.card ≤ m := by
      simpa [m,N,t] using heq.card_part_le_average_add_one hp
    have hε₁ : 2*ε ≤ ρ := by have := min_le_right (γ*ρ) (ρ/16); dsimp [ε]; linarith
    have hcount := irregular_refined_vertex_pairs G P Q ε γ ρ hρ.le (by linarith) (min_le_left ..) hε₁ m hm
    apply (Nat.cast_le (α := ℝ) |>.mpr hcount).trans
    apply refinement_error _ t m _ _ ρ ε hρ he.le ((Nat.le_ceil _).trans (Nat.cast_le.mpr hl))
    · have hp : t ≤ N := by simpa [t,N] using P.card_parts_le_card
      have := Nat.div_mul_le_self N t
      dsimp [m]
      rw [Nat.mul_add, Nat.mul_comm t (N/t), Nat.mul_one]
      omega
    · have hub := hu
      change ((P.nonUniforms G ε).card : ℝ) ≤ ((t*(t-1) : ℕ) : ℝ)*ε at hub
      apply hub.trans (mul_le_mul_of_nonneg_right _ he.le)
      exact_mod_cast (show t*(t-1) ≤ t^2 by rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.sub_le ..))
    · have hh := small_refinement_cells P Q γ hγ.le
      apply hh.trans
      have H := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hQ) hγ.le
      have H' := mul_le_mul_of_nonneg_right H (Nat.cast_nonneg (Fintype.card V))
      apply H'.trans_eq
      dsimp [γ]; field_simp
    · exact min_le_right .. 
  · refine ⟨⊥,bot_le,?_,?_⟩
    · rw [Finpartition.card_bot, card_univ]
      exact (Nat.le_of_not_ge hn).trans (le_max_left ..)
    · have singleton (x : V) : (⊥ : Finpartition (univ : Finset V)).part x = {x} :=
        (⊥ : Finpartition (univ : Finset V)).part_eq_of_mem
          (Finpartition.mem_bot_iff.mpr ⟨x,mem_univ _,rfl⟩) (mem_singleton_self _)
      simp_rw [singleton]
      have only (X : Finset V) (x : V) (hx : X ⊆ {x}) (hs : ρ*({x} : Finset V).card ≤ X.card) : X = {x} := by
        rcases subset_singleton_iff.mp hx with h | h
        · subst X; simp at hs; linarith
        · exact h
      have no (e : V × V) : ¬ ∃ X ⊆ ({e.1} : Finset V), ∃ Y ⊆ ({e.2} : Finset V),
          ρ*({e.1} : Finset V).card ≤ X.card ∧ ρ*({e.2} : Finset V).card ≤ Y.card ∧
          ρ < |crossDensity G X Y - crossDensity G {e.1} {e.2}| := by
        rintro ⟨X,hX,Y,hY,hs,ht,hbad⟩
        rw [only X _ hX hs,only Y _ hY ht,sub_self,abs_zero] at hbad
        exact (not_lt_of_ge hρ.le) hbad
      have empty := filter_false_of_mem (s := (univ : Finset (V × V))) (fun e _ => no e)
      rw [empty]
      simp [mul_nonneg hρ.le (sq_nonneg _)]
/-- Failure of the manuscript's weak density inequality, with its exact
relative-size thresholds. -/
@[expose] public def irregularPair {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ρ : ℝ) (A B : Finset V) : Prop :=
  ∃ X ⊆ A, ∃ Y ⊆ B, ρ*A.card ≤ X.card ∧ ρ*B.card ≤ Y.card ∧
    ρ < |crossDensity G X Y - crossDensity G A B|

/-- Lemma 4.2, with the exact sum over ordered distinct classes. Take the
vertex type to be the vertices of the piece and G its induced graph. -/
public theorem regular_refinement (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Q : Finpartition (univ : Finset V)), Q.parts.card ≤ m₀ →
      ∃ R : Finpartition (univ : Finset V), R ≤ Q ∧ R.parts.card ≤ K ∧
      (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧ irregularPair G ρ e.1 e.2),
        (e.1.card : ℝ)*e.2.card) ≤ ρ*(Fintype.card V : ℝ)^2 := by
  classical
  obtain ⟨K,hK⟩ := regular_refinement_vertices ρ hρ hρ₁ m₀ hm₀
  refine ⟨K,?_⟩
  intro V _ _ G _ Q hQ
  obtain ⟨R,href,hsize,hbad⟩ := hK V G Q hQ
  refine ⟨R,href,hsize,?_⟩
  let bad := (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧ irregularPair G ρ e.1 e.2)
  let parents (p : V × V) := (R.part p.1,R.part p.2)
  have fiber (e : Finset V × Finset V) (he : e ∈ bad) :
      univ.filter (fun p => parents p = e) = e.1 ×ˢ e.2 := by
    obtain ⟨h₁,h₂⟩ := mem_product.mp (mem_filter.mp he).1
    ext ⟨x,y⟩
    simp only [mem_filter,mem_univ,true_and,parents,Prod.ext_iff,mem_product,
      R.part_eq_iff_mem h₁,R.part_eq_iff_mem h₂]
  have coeff : (∑ e ∈ bad, e.1.card*e.2.card) =
      (univ.filter fun p : V × V => parents p ∈ bad).card := by
    rw [← sum_card_fiberwise_eq_card_filter]
    exact sum_congr rfl (fun e he => by rw [fiber e he,card_product])
  calc
    _ = ((∑ e ∈ bad, e.1.card*e.2.card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ _ := ?_
  apply le_trans _ hbad
  apply Nat.cast_le.mpr
  apply coeff.le.trans (card_le_card ?_)
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp he).2).2.2⟩
end Vu
