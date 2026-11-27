module
public import Vu.RevisedReduction
public import Vu.RevisedMatrixCut
public import Vu.RevisedSupport
namespace Vu.Revised
open Finset
/-- Combine the signed contribution on sparse regular pairs with the indicator
of the remaining hard edges after each row's prescribed omission. -/
public theorem graph_decomposition : GraphDecompositionTheorem := by
  classical
  intro ε hε hε₁
  let δ := ε/200
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd₁ : δ ≤ 1/200 := by dsimp [δ]; linarith
  let M : ℝ := 2/δ + 1
  have hM : 2 ≤ M := by dsimp [M]; have := (le_div_iff₀ hd).mpr (show 1*δ ≤ 2 by linarith); linarith
  refine ⟨ε/2,ε/8,⌈4/ε⌉₊+2,M,⟨by positivity,by linarith⟩,⟨by positivity,by linarith⟩,hM,?_⟩
  intro η hη
  let e := η/2
  have he : 0 < e := by dsimp [e]; positivity
  let lam : ℝ := min (e/10) (1/2)
  let r := ⌈1/(lam/8)⌉₊
  have hl : 0 < lam := lt_min (by positivity) (by norm_num)
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨ω,ρ,k₀,K,D₀,hω,hρ,hrho,hk,hK,ho,hs,hD₀⟩ := partial_decomposition ε e hε hε₁ he
  refine ⟨max (2*r+2) D₀,?_⟩
  intro D hD V _ _ G _ hdeg k
  have hsupp := (le_max_left _ _).trans hD
  have hpos : 0 < D := by omega
  obtain ⟨budget,graphs⟩ := hD₀ D ((le_max_right _ _).trans hD)
  obtain ⟨hlo,hhi,⟨h⟩⟩ := graphs V G hdeg
  letI := pieceOrder h.pieces
  let P (i : ↥h.pieces) := i.val
  let R := h.partition
  let good i := goodVertices G (R i) ρ K
  let cls i := (R i).part
  let z := ω*D
  let H := partitionHardGraph G h.pieces R K z ρ δ
  let B := partitionSoftMatrix G h.pieces R K z ρ δ
  let β (x y : V) : ℝ := if H.Adj x y then -1 else B x y
  have sub : H ≤ G := fun _ _ h => h.1
  have hp (i : ↥h.pieces) := (h.extracted.1 i.val i.property).2.2.1
  have hm (x : V) : (univ.filter fun i => x ∈ P i).card ≤ r := by
    dsimp only [P]; rw [univ_eq_attach,filter_attach (fun Q : Finset V => x ∈ Q) h.pieces,card_map,card_attach]
    exact h.multiplicity x
  have tests (x U) (hu : U ∈ h.tests x) (y) (hy : y ∈ U) : H.Adj x y := by
    apply (H.mem_neighborFinset x y).mp
    rw [show H.neighborFinset x = (h.tests x).biUnion id from (h.cover x).symm]
    exact mem_biUnion.mpr ⟨U,hu,hy⟩
  have hv := soft_matrix_edge_values G P good cls H z ρ δ
  refine ⟨hlo,hhi,⟨{
    tests := h.tests, test_count := h.count, test_size := h.size,
    test_subset := fun x U hu y hy => (G.mem_neighborFinset x y).mpr (sub (tests x U hu y hy)),
    beta := β, symm := ?_, edges := ?_, bounds := ?_, row_sum := ?_, support := ?_, omitted := ?_}⟩⟩
  · intro x y
    by_cases hh : H.Adj x y
    · simp [β,hh,hh.symm]
    · simp only [β,if_neg hh,if_neg (fun (h : H.Adj y x) => hh h.symm)]
      exact soft_matrix_symmetric G P good cls H z ρ δ x y
  · intro x y hg
    by_cases hh : H.Adj x y <;> simp only [β,hh,ite_true,ite_false]
    exact (hv x y).2.2 hg hh
  · intro x y
    by_cases hh : H.Adj x y
    · simp [β,hh]; linarith
    · simp only [β,if_neg hh]
      obtain ⟨h₀,h₁⟩ := soft_matrix_entry_bounds G P good cls H z ρ δ hd x y
      exact ⟨h₀,h₁.trans (by dsimp [M]; linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 1) hd.le,
        show 2/δ = 1/δ+1/δ by ring])⟩
  · intro x
    have hrw := soft_matrix_row_sum G H P R D r K ω ρ δ hpos hd hd₁ hω.le ho hs hdeg hp hm
      (fun i A ha j _ => h.refines i A ha j.val j.property) x
    have hb (y : V) : |β x y| ≤ |B x y| + (if G.Adj x y then 1 else 0) := by
      by_cases hh : H.Adj x y
      · simp [β,hh,sub hh]
      · simp only [β,if_neg hh]; split <;> linarith
    apply (sum_le_sum (fun y _ => hb y)).trans
    rw [sum_add_distrib]
    have hsum : (∑ y, if G.Adj x y then (1:ℝ) else 0) = G.degree x := by
      simp [SimpleGraph.degree,SimpleGraph.neighborFinset_def]
    rw [hsum]
    change (∑ y, |B x y|) ≤ 2/δ*D at hrw
    dsimp only [M]; linarith only [hrw,Nat.cast_le (α := ℝ) |>.mpr (hdeg x)]
  · exact support_card G H P good cls D r z ρ δ hsupp hdeg hp hm sub
  · intro T hT
    obtain ⟨S,hS,hN⟩ := h.omitted T hT
    refine ⟨S,hS,?_⟩
    intro X hX Y hY
    let A (x y : V) : ℝ := if H.Adj x y ∧ y ∉ S x then 1 else 0
    have cut := constructed_matrix_cut G D r k₀ K k _ lam ω ρ δ (ε/8) e h hpos hr hk hK
      hl.le hω.le hρ (by linarith) hd (by linarith) budget T X Y hT hX hY
    have hardcut := rectangle_of_rows A T X Y D (e*D) (by positivity) hT hX hY hN
    have ident (x : V) (hx : x ∈ X) (y : V) : (if y ∈ S x then 0 else β x y) = B x y - A x y := by
      by_cases hy : y ∈ S x
      · have hh : H.Adj x y := by
          rcases hS x (hX hx) with he|hh
          · simp [he] at hy
          · exact tests x (S x) hh y hy
        have hb : B x y = 0 := (hv x y).2.1 hh
        simp [A,hy,hb]
      · by_cases hh : H.Adj x y
        · have hb : B x y = 0 := (hv x y).2.1 hh
          simp [A,β,hy,hh,hb]
        · simp [A,β,hy,hh]
    rw [sum_congr rfl (fun x hx => sum_congr rfl (fun y _ => ident x hx y))]
    simp_rw [sum_sub_distrib]
    apply (abs_sub ..).trans
    change |∑ x ∈ X, ∑ y ∈ Y, B x y| ≤ e*D^2 at cut
    linarith only [add_le_add cut hardcut,show e*D^2+e*D*D = η*D^2 by dsimp [e]; ring]
end Vu.Revised
