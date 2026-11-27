module
public import Vu.PartitionMatrix
public import Vu.MatrixAssembly
namespace Vu
open Finset

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i))

/-- The full collection of selected sparse regular blocks of piece i, before
removing exceptional vertex pairs. Both coordinates are restricted to good rows. -/
@[expose] public noncomputable def regularPieceMatrix (K : ℕ) (z ρ δ : ℝ) (i : I) (x y : V) : ℝ := by
  classical
  let A := (R i).part x
  let B := (R i).part y
  exact if x ∈ goodVertices G (R i) ρ K ∧ y ∈ goodVertices G (R i) ρ K ∧
    A ≠ B ∧ eligibleClasses P z i A B ∧ ¬ irregularPair G ρ A B ∧ crossDensity G A B < 1-δ then
    centeredEntry G (crossDensity G A B) x y else 0

public theorem regular_piece_supported (K : ℕ) (z ρ δ : ℝ) (i : I) (x y : V) (h : x ∉ P i ∨ y ∉ P i) :
    regularPieceMatrix G P R K z ρ δ i x y = 0 := by
  classical
  have hin : goodVertices G (R i) ρ K ⊆ P i := filter_subset _ _
  rcases h with hx | hy
  · simp [regularPieceMatrix,show x ∉ goodVertices G (R i) ρ K from fun h => hx (hin h)]
  · simp [regularPieceMatrix,show y ∉ goodVertices G (R i) ρ K from fun h => hy (hin h)]

/-- The first term in the per-piece norm estimate of Lemma 4.6, summed
over all actual pieces. The bound is valid on any row set. -/
public theorem regular_piece_sum_norm (D r K : ℕ) (z ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hp : ∀ i, (P i).card ≤ 2*D) (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (T : Finset V) :
    RowNormLE (fun x y => ∑ i, regularPieceMatrix G P R K z ρ δ i x y) T
      (r * (((4*ρ)^(1/3:ℝ)/δ)*(2*D))) := by
  classical
  let c := (4*ρ)^(1/3:ℝ)/δ
  have hc : 0 ≤ c := by dsimp [c]; positivity
  apply sum_piece_matrix_bound P _ r (c*(2*D)) hm
    (fun i x y h => regular_piece_supported G P R K z ρ δ i x y (Or.inl h))
  intro i f
  let sel (A B : Finset V) := A ≠ B ∧ eligibleClasses P z i A B ∧ ¬ irregularPair G ρ A B ∧ crossDensity G A B < 1-δ
  have hh := regular_partition_matrix G (P i) (goodVertices G (R i) ρ K) (R i) sel ρ δ hρ hδ
    (filter_subset _ _) (fun _ _ h => h.2.2) f
  have hm' : (∑ x, (∑ y, regularPieceMatrix G P R K z ρ δ i x y * f y)^2) ≤
      (c*(P i).card)^2*∑ y ∈ P i, f y^2 := by
    convert hh using 1
    apply sum_congr rfl
    intro x _
    congr 1
    apply sum_congr rfl
    intro y _
    dsimp only [regularPieceMatrix,sel]
    split <;> rename_i h <;> simp [h]
  apply hm'.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact pow_le_pow_left₀ (mul_nonneg hc (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left (by exact_mod_cast hp i) hc) 2
end Vu
