module
public import Vu.DecompositionParameters
namespace Vu
open Finset

/-- The matrix attached to the same pieces and partitions as the hard graph. -/
@[expose] public noncomputable def partitionSoftMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Finset V)) (R : ∀ i : ↥F, Finpartition i.val)
    (K : ℕ) (z ρ δ : ℝ) : V → V → ℝ := by
  letI := pieceOrder F
  exact softMatrix G Subtype.val (fun i => goodVertices G (R i) ρ K) (fun i => (R i).part)
    (partitionHardGraph G F R K z ρ δ) z ρ δ

/-- For arbitrary ε and η in Proposition 3.1, construct the actual common
witness for (D1), (D2), (D4), all entry conditions, and the parameter
budget in Lemma 4.6. Only the two analytic bounds on this particular
matrix remain to obtain a full Decomposition. -/
public theorem partial_decomposition (ε η : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η) :
    let lam := min (η/10) (1/2)
    let r := ⌈1/(lam^2/8)⌉₊
    let δ := ε/200
    let Rmax := ⌈4/ε⌉₊+2
    ∃ (ω ρ : ℝ) (k₀ K D₀ : ℕ), 0 < ω ∧ 0 < ρ ∧ ρ < 1/4 ∧ 0 < k₀ ∧ 0 < K ∧
      (r : ℝ)^3*ω ≤ δ ∧ 8*r*√ρ ≤ δ/4 ∧ ∀ (D : ℕ), D ≥ D₀ →
      lam + ((r:ℝ)^3/δ+r^2)*ω + 2*r/k₀ + (r+1)/(D:ℝ) +
        2*r*((4*ρ)^(1/3:ℝ)/δ+3*ρ^(1/4:ℝ)) ≤ η ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ x, G.degree x ≤ D) →
        let k := ⌊(maxCodegree G : ℝ)+ε*D⌋₊
        ε/2*D ≤ k ∧ k ≤ 2*D ∧
        Nonempty (HardDecomposition G D r k₀ K k Rmax lam ω ρ δ (ε/8) η) := by
  classical
  intro lam r δ Rmax
  obtain ⟨ω,ρ,k₀,D₂,hω,hρ,hρ₁,hk₀,ho,hs,hbudget⟩ := choose_decomposition_parameters ε η hε hη
  have hl : 0 < lam := lt_min (by positivity) (by norm_num)
  have hd : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,D₁,hD₁⟩ := hard_decomposition ε η lam ω ρ k₀ hε hε₁ hη hl hω hρ hρ₁ hk₀ ho hs
  refine ⟨ω,ρ,k₀,K,max D₁ D₂,hω,hρ,hρ₁,hk₀,hK,ho,hs,?_⟩
  intro D hD
  refine ⟨hbudget D ((le_max_right _ _).trans hD),?_⟩
  intro V _ _ G _ hdeg k
  obtain ⟨hlo,hhi,⟨h⟩⟩ := hD₁ D ((le_max_left _ _).trans hD) V G hdeg
  exact ⟨hlo,hhi,⟨h⟩⟩

/-- For this explicit matrix, the absolute row sum and the restricted norm
are sufficient to complete Proposition 3.1. -/
public theorem decomposition_of_soft_matrix_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D r k₀ K k Rmax : ℕ) (lam ω ρ δ b η : ℝ)
    (hd : 0 < δ) (h : HardDecomposition G D r k₀ K k Rmax lam ω ρ δ b η) :
    let C : ℝ := max 10 (2/δ)
    let B := partitionSoftMatrix G h.pieces h.partition K (ω*D) ρ δ
    (∀ x, ∑ y, |B x y| ≤ C*D) →
    (∀ T : Finset V, T.card ≤ D → RowNormLE B T (η*D)) →
    Nonempty (Decomposition G D k Rmax b C η) := by
  classical
  intro C B hrow hnorm
  letI := pieceOrder h.pieces
  let P (i : ↥h.pieces) := i.val
  let good i := goodVertices G (h.partition i) ρ K
  let cls i := (h.partition i).part
  let H := partitionHardGraph G h.pieces h.partition K (ω*D) ρ δ
  have hsub (x y : V) (ha : H.Adj x y) : G.Adj x y := ha.1
  have hv := soft_matrix_edge_values G P good cls H (ω*D) ρ δ
  refine ⟨{
    H := H, F := G \ H, edge_iff := ?_, disjoint_edges := ?_, tests := h.tests, matrix := B,
    symmetric := soft_matrix_symmetric G P good cls H (ω*D) ρ δ, tests_cover := ?_,
    test_count := h.count, test_size := h.size, omitted := ?_, entry_bounds := ?_,
    row_sum := hrow, diagonal := fun x => (hv x x).1, soft := ?_, hard := fun x y => (hv x y).2.1,
    norm_bound := hnorm, local_support := ?_}⟩
  · intro x y
    change G.Adj x y ↔ H.Adj x y ∨ G.Adj x y ∧ ¬ H.Adj x y
    by_cases he : H.Adj x y
    · simp [he,hsub x y he]
    · simp [he]
  · exact fun _ _ he hF => hF.2 he
  · intro x y
    rw [← H.mem_neighborFinset,← h.cover x,mem_biUnion]; rfl
  · intro T hT
    obtain ⟨S,hS,hN⟩ := h.omitted T hT
    refine ⟨S,hS,?_⟩
    convert hN using 1
    funext x y
    by_cases he : H.Adj x y ∧ y ∉ S x <;> simp only [H] at he ⊢ <;> simp [he]
  · intro x y
    obtain ⟨hlo,hhi⟩ := soft_matrix_entry_bounds G P good cls H (ω*D) ρ δ hd x y
    exact ⟨hlo,hhi.trans ((div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) hd.le).trans (le_max_right _ _))⟩
  · exact fun x y he => (hv x y).2.2 he.1 he.2
  · exact soft_matrix_local G P good cls H (ω*D) ρ δ
      (fun i => (h.extracted.1 i.val i.property).2.2.2.1)
end Vu
