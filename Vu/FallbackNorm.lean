module
public import Vu.AssignedMatrix
public import Vu.PieceErrors
namespace Vu
open Finset

/-- Bound all assigned covered edges not handled by the regular blocks.
The three masked matrices partition these edges even when an edge belongs
to more than one exceptional category. -/
public theorem fallback_sum_norm {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i))
    (D r k₀ K : ℕ) (z ρ δ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1) (hK : 0 < K) (hk₀ : 0 < k₀)
    (hp : ∀ i, (P i).card ≤ 2*D) (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (hk : ∀ i, (R i).parts.card ≤ K)
    (hsize : ∀ i A, A ∈ (R i).parts → A.card ≤ (P i).card/k₀+1)
    (hirr : ∀ i, (by classical exact ∑ e ∈ ((R i).parts ×ˢ (R i).parts).filter (fun e => e.1 ≠ e.2 ∧
      irregularPair G ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) ≤ ρ*((P i).card:ℝ)^2)
    (T : Finset V) :
    let H := hardGraph G P (fun j => goodVertices G (R j) ρ K) (fun j => (R j).part) z
      (fun j => partnerGraph G P j (largeClasses (R j) ρ K) z ρ δ)
    RowNormLE (fun x y => ∑ i, fallbackPiece G P R H K z ρ δ i x y) T
      (r*(2*D/(k₀:ℝ)+1+3*ρ^(1/4:ℝ)*(2*D))) := by
  classical
  intro H
  let L := 2*D/(k₀:ℝ)+1
  let t := ρ^(1/4:ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg hρ.le _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let F := fallbackPiece G P R H K z ρ δ
  have hc := fallback_classification G P R K z ρ δ
  have supp (i : I) (x y : V) (hn : F i x y ≠ 0) : x ∈ P i ∧ y ∈ P i :=
    ⟨(hc i x y hn).1,(hc i x y hn).2.1⟩
  apply sum_piece_matrix_bound P F r _ hm (fun i x y hx => by by_contra hn; exact hx (supp i x y hn).1)
  intro i f
  let P₁ := P i
  let R₁ := R i
  let bad := P₁ \ goodVertices G R₁ ρ K
  let same x y := R₁.part x = R₁.part y
  let touch x y := x ∈ bad ∨ y ∈ bad
  let A x y := if same x y then F i x y else 0
  let B x y := if ¬same x y ∧ touch x y then F i x y else 0
  let C x y := if ¬same x y ∧ ¬touch x y then F i x y else 0
  have splitF (x y : V) : F i x y = A x y + B x y + C x y := by
    by_cases ha : same x y <;> by_cases hb : touch x y <;> simp [A,B,C,ha,hb]
  have absF (x y : V) : |F i x y| ≤ 1 := by dsimp [F,fallbackPiece]; split <;> norm_num
  have ab (p : Prop) [Decidable p] (x y : V) : |if p then F i x y else 0| ≤ 1 := by split <;> simp [absF]
  have keep (p : Prop) [Decidable p] (x y : V) (hn : (if p then F i x y else 0) ≠ 0) : p ∧ F i x y ≠ 0 := by
    by_cases h : p <;> simp_all
  have ha : RowNormLE A univ L := by
    refine same_class_norm P₁ R₁ A L hL ?_ (fun x y => ab _ x y) ?_
    · intro U hu
      have hh := Nat.cast_le (α := ℝ) |>.mpr (hsize i U hu)
      push_cast at hh
      have hfloor : (((P i).card/k₀ : ℕ):ℝ) ≤ (P i).card/(k₀:ℝ) := by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hk₀)).mpr
        exact_mod_cast Nat.div_mul_le_self (P i).card k₀
      have hd := div_le_div_of_nonneg_right (show ((P i).card:ℝ) ≤ 2*D by exact_mod_cast hp i) (Nat.cast_nonneg k₀)
      dsimp [L]; linarith
    · intro x y hn
      have hh := keep (same x y) x y hn
      exact ⟨(supp i x y hh.2).1,(supp i x y hh.2).2,hh.1⟩
  have fromMass (M : V → V → ℝ) (L' : ℝ) (ms : ∀ x y, M x y ≠ 0 → F i x y ≠ 0)
      (hmass : (∑ x ∈ P₁, ∑ y ∈ P₁, M x y^2) ≤ L'^2) : RowNormLE M univ L' := by
    intro g
    have hh := piece_frobenius P₁ M (L'^2) (by
      intro x y h; by_contra hn
      exact h.elim (fun h => h (supp i x y (ms x y hn)).1) (fun h => h (supp i x y (ms x y hn)).2)) hmass g
    exact hh.trans (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)) (sq_nonneg _))
  have hP : (P₁.card:ℝ) ≤ 2*D := by exact_mod_cast hp i
  obtain ⟨hr₁,hr₂⟩ := fourth_root_errors ρ hρ.le hr
  have hp2 : (P₁.card:ℝ)^2 ≤ (2*(D:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hP 2
  have hb : RowNormLE B univ (2*t*(2*D)) := by
    apply fromMass B _ (fun x y hn => (keep (¬same x y ∧ touch x y) x y hn).2)
    apply (bad_vertex_frobenius P₁ bad sdiff_subset B (fun x y => ab _ x y)
      (fun x _ y _ hn => (keep (¬same x y ∧ touch x y) x y hn).1.2)).trans
    have hbad := nongood_vertices_bound G P₁ R₁ ρ K hρ hr hK (hk i)
    change (bad.card : ℝ) ≤ _ at hbad
    calc
      _ ≤ (2*(ρ+√ρ))*(P₁.card:ℝ)^2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hbad (Nat.cast_nonneg P₁.card)]
      _ ≤ (2*t)^2*(2*(D:ℝ))^2 := mul_le_mul hr₂ hp2 (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hi : RowNormLE C univ (t*(2*D)) := by
    apply fromMass C _ (fun x y hn => (keep (¬same x y ∧ ¬touch x y) x y hn).2)
    apply (irregular_edge_frobenius G P₁ R₁ ρ C (fun x y => ab _ x y) ?_).trans
    · apply (hirr i).trans
      exact (mul_le_mul hr₁ hp2 (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring)
    · intro x hx y hy hn
      obtain ⟨⟨hneq,hnt⟩,hF⟩ := keep (¬same x y ∧ ¬touch x y) x y hn
      refine ⟨hneq,?_⟩
      rcases (hc i x y hF).2.2 with he | hg | hg | hir
      · exact (hneq he).elim
      · exact (hnt (Or.inl (mem_sdiff.mpr ⟨hx,hg⟩))).elim
      · exact (hnt (Or.inr (mem_sdiff.mpr ⟨hy,hg⟩))).elim
      · exact hir
  have hboth := row_norm_add (add_nonneg hL (by positivity)) (by positivity)
    (row_norm_add hL (by positivity) ha hb) hi
  have hnorm : RowNormLE (F i) univ (L+3*t*(2*D)) := by
    have eq : F i = fun x y => A x y + B x y + C x y := funext (fun x => funext (splitF x))
    rw [eq,show L+3*t*(2*D) = (L+2*t*(2*D))+t*(2*D) by ring]
    exact hboth
  exact localize_norm P₁ (F i) _ hnorm (fun x y h => by by_contra hn; exact h (supp i x y hn).2) f
end Vu
