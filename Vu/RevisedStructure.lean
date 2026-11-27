module
public import Vu.RevisedSigned
namespace Vu.Revised
open Finset

/-- The graph decomposition of the revised proof with the manuscript's choices
a = ε/2, b = ε/8, R = ⌈4/ε⌉+2, δ = ε/200 and C = max 10 (2/δ). -/
public theorem graph_structure : GraphDecompositionTheorem := by
  classical
  intro ε hε hε₁
  let δ := ε/200
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd₁ : δ ≤ 1/4 := by dsimp [δ]; linarith
  let M : ℝ := max 10 (2/δ)
  have hM : 4 ≤ M := (by norm_num : (4:ℝ) ≤ 10).trans (le_max_left ..)
  have hm : 1/δ ≤ M := (div_le_div_of_nonneg_right (by norm_num) hd.le).trans (le_max_right ..)
  refine ⟨ε/2,ε/8,⌈4/ε⌉₊+2,M,⟨by positivity,by linarith⟩,⟨by positivity,by linarith⟩,by linarith,?_⟩
  intro η hη
  let lam : ℝ := min (η/10) (1/2)
  let r := ⌈1/(lam/8)⌉₊
  have hl : 0 < lam := lt_min (by positivity) (by norm_num)
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨ω,ρ,hω,hρ,hrho,ho,hs,hbudget⟩ := cut_parameters r δ η lam hr hd hη (min_le_left ..)
  obtain ⟨K,_,hpart⟩ := ambient_regular_partitions ρ ω hρ hrho hω r 1 (by decide)
  obtain ⟨h,hh,D₀,hcol⟩ := column_parameters r (r*K) η hη
  refine ⟨max (max (1+2*r) ⌈4/ε⌉₊) D₀,?_⟩
  intro D hD V _ _ G _ hdeg k
  have hbase := (le_max_left _ _).trans hD
  have hD₁ : 1+2*r ≤ D := (le_max_left ..).trans hbase
  have hDpos : 0 < D := by omega
  have hfour : 4 ≤ ε*D := by
    have h := (Nat.le_ceil (4/ε)).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hbase))
    linarith only [(div_le_iff₀ hε).mp h]
  obtain ⟨F,hF,hinc⟩ := extracting_dense_pieces G D hdeg lam hl
  letI := pieceOrder F
  choose R hnum _ href hir using fun i : ↥F => hpart V G F D hDpos hinc (fun P hp => (hF.1 P hp).2.2.1) i.val i.property
  let d : Classes G D r K ω ρ δ (↥F) := {
    piece := Subtype.val, partition := R, size := fun i => (hF.1 i.val i.property).2.2.1,
    multiplicity := fun x => by
      rw [univ_eq_attach,filter_attach (fun P : Finset V => x ∈ P) F,card_map,card_attach]; exact hinc x
    num := hnum, refines := fun i A ha j _ => href i A ha j.val j.property, irregular := hir }
  let t := maxCodegree G
  let s := (t:ℝ)+ε*D/2
  have ht : t ≤ D := (maxCodegree_le_iff G D).mpr (fun x y _ => (G.card_commonNeighbors_le_degree_left x y).trans (hdeg x))
  have hf : (k:ℝ) ≤ t+ε*D := Nat.floor_le (by positivity)
  have hk : (t:ℝ)+ε*D < k+1 := Nat.lt_floor_add_one _
  have hu : (k:ℝ) ≤ 2*D := by
    linarith only [hf,Nat.cast_le (α := ℝ) |>.mpr ht,mul_le_mul_of_nonneg_right hε₁ (Nat.cast_nonneg D)]
  have hsize : s ≤ (1-ε/8)*k := by
    dsimp [s]
    nlinarith only [hfour,hk,mul_le_mul_of_nonneg_left hu hε.le]
  have hs1 : 1 ≤ s := by dsimp [s]; linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]
  obtain ⟨U,hcov,hsize',hcnt,hom⟩ := d.tests_and_omissions s η h hh hDpos hs1 hω.le ho hρ.le hs hd.le hd₁ hdeg
    (by dsimp [δ,s,t]; nlinarith [mul_nonneg hε.le (Nat.cast_nonneg D)]) (hcol D ((le_max_right ..).trans hD))
  refine ⟨by linarith only [hfour,hk,(Nat.cast_nonneg t : (0:ℝ) ≤ t)],by exact_mod_cast hu,?_⟩
  apply d.signed_of_tests k (⌈4/ε⌉₊+2) (ε/8) M η lam U hω.le ho hρ (by linarith) hs hd (by linarith)
    hM hm hD₁ hdeg _ hbudget hcov _ (fun x B hb => (hsize' x B hb).trans hsize) hom hη.le
  · intro X Y hX hY
    have he (x y : V) : d.uncovered x y = if (uncoveredGraph G F).Adj x y then 1 else 0 := by
      have eq : ¬(jointPieces d.piece x y).Nonempty ↔ ∀ Q ∈ F, x ∈ Q → y ∉ Q := by
        simp [jointPieces,d,Finset.filter_nonempty_iff,Subtype.exists]
        grind
      simp only [Classes.uncovered,eq,uncoveredGraph]
      congr
    simp_rw [he]
    exact hF.2.2 X Y hX hY
  · intro x
    have hdiv : 2*(D:ℝ)/s ≤ 4/ε := by
      apply (div_le_div_iff₀ (by linarith) hε).mpr
      dsimp [s]; linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]
    apply Nat.cast_le (α := ℝ) |>.mp
    push_cast
    linarith only [hcnt x,hdiv,Nat.le_ceil (4/ε)]
end Vu.Revised
