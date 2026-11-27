module
public import Vu.RevisedTests
public import Vu.RevisedCoefficientRows
public import Vu.RevisedCoefficientCut
public import Vu.RevisedReduction
public import Vu.RevisedPieces
namespace Vu.Revised
open Finset

public theorem cut_parameters (r : ℕ) (δ η lam : ℝ) (hr : 0 < r) (hd : 0 < δ)
    (hη : 0 < η) (hl : lam ≤ η/10) :
    ∃ ω ρ : ℝ, 0 < ω ∧ 0 < ρ ∧ ρ < 1/4 ∧ (r:ℝ)^2*ω ≤ 1 ∧ 8*r*√ρ ≤ δ ∧
      2*r*√((ρ/δ+ρ+2*√ρ)/δ)+(r:ℝ)^2*ω/δ+lam ≤ η/2 := by
  let ω := min (1/(r:ℝ)^2) (δ*η/(10*(r:ℝ)^2))
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hω : 0 < ω := lt_min (by positivity) (by positivity)
  let f (x : ℝ) := 2*r*√((x/δ+x+2*√x)/δ)+8*r*√x
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  let tol := min δ (η/10)
  obtain ⟨a,ha,hs⟩ := Metric.continuousAt_iff.mp hf tol (lt_min hd (by positivity))
  let ρ := min (a/2) (1/8)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hnear : dist ρ 0 < a := by rw [Real.dist_eq,sub_zero,abs_of_pos hρ]; exact (min_le_left _ _).trans_lt (by linarith)
  have h := hs hnear
  have he : f 0 = 0 := by simp [f]
  rw [he,Real.dist_eq,sub_zero] at h
  have hh := (le_abs_self _).trans h.le
  dsimp only [f] at hh
  have hn : 0 ≤ 2*r*√((ρ/δ+ρ+2*√ρ)/δ) := by positivity
  have ht : 0 ≤ 8*r*√ρ := by positivity
  have h₁ := (le_div_iff₀ (sq_pos_of_pos hr')).mp (min_le_left (1/(r:ℝ)^2) (δ*η/(10*(r:ℝ)^2)))
  have h₂ := (le_div_iff₀ (by positivity : 0 < 10*(r:ℝ)^2)).mp (min_le_right (1/(r:ℝ)^2) (δ*η/(10*(r:ℝ)^2)))
  change ω*_ ≤ _ at h₁ h₂
  refine ⟨ω,ρ,hω,hρ,(min_le_right ..).trans_lt (by norm_num),by linarith only [h₁],?_,?_⟩
  · linarith only [hh.trans (min_le_left ..),hn]
  · have hfrac : (r:ℝ)^2*ω/δ ≤ η/10 := (div_le_iff₀ hd).mpr (by linarith only [h₂])
    linarith only [hh.trans (min_le_right ..),ht,hfrac,hl,hη]

namespace Classes
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)
public theorem coefficient_cut (X Y : Finset V) (hX : X.card ≤ D) (hY : Y.card ≤ D)
    (lam η : ℝ) (hω : 0 ≤ ω) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hd : 0 < δ) (hd₁ : δ ≤ 1)
    (hu : (∑ x ∈ X, ∑ y ∈ Y, d.uncovered x y) ≤ lam*D^2)
    (budget : 2*r*√((ρ/δ+ρ+2*√ρ)/δ)+(r:ℝ)^2*ω/δ+lam ≤ η/2) :
    |∑ x ∈ X, ∑ y ∈ Y, d.omittedHard x y| ≤ η/2*D^2 := by
  simp_rw [fun x y => d.soft_identity x y hd,sum_sub_distrib]
  have h := abs_sub (∑ x ∈ X, ∑ y ∈ Y, ∑ i, (d.block i x y+d.extra i x y)) (∑ x ∈ X, ∑ y ∈ Y, ∑ i, d.earlierTerm i x y)
  apply (abs_sub ..).trans
  have hnn : 0 ≤ ∑ x ∈ X, ∑ y ∈ Y, d.uncovered x y := sum_nonneg fun x _ => sum_nonneg fun y _ => by unfold uncovered; split <;> norm_num
  rw [abs_of_nonneg hnn]
  apply (add_le_add (h.trans (add_le_add (d.local_terms_cut X Y hX hY hd hd₁ hρ hρ₁) (d.earlier_cut X Y hX hω hd))) hu).trans
  linarith only [mul_le_mul_of_nonneg_right budget (sq_nonneg (D:ℝ))]

public theorem signed_of_tests (k R : ℕ) (b M η lam : ℝ) (U : V → Finset (Finset V))
    (hω : 0 ≤ ω) (ho : (r:ℝ)^2*ω ≤ 1) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hs : 8*r*√ρ ≤ δ)
    (hd : 0 < δ) (hd₁ : δ ≤ 1) (hM : 4 ≤ M) (hm : 1/δ ≤ M)
    (hD : 1+2*r ≤ D) (hdeg : ∀ x, G.degree x ≤ D)
    (hu : ∀ X Y : Finset V, X.card ≤ D → Y.card ≤ D → (∑ x ∈ X, ∑ y ∈ Y, d.uncovered x y) ≤ lam*D^2)
    (budget : 2*r*√((ρ/δ+ρ+2*√ρ)/δ)+(r:ℝ)^2*ω/δ+lam ≤ η/2)
    (cov : ∀ x, (U x).biUnion id = (by classical exact d.hardGraph.neighborFinset x))
    (cnt : ∀ x, (U x).card ≤ R) (size : ∀ x B, B ∈ U x → (B.card:ℝ) ≤ (1-b)*k)
    (om : ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ U x) ∧
      (by classical exact ∀ z, ((T.filter (fun x => d.hardGraph.Adj x z ∧ z ∉ S x)).card:ℝ) ≤ η*D/2))
    (hη : 0 ≤ η) : Nonempty (SignedDecomposition G D k R b M η) := by
  classical
  have sub x B (hb : B ∈ U x) y (hy : y ∈ B) : d.hardGraph.Adj x y := by
    apply (d.hardGraph.mem_neighborFinset x y).mp
    rw [←cov]; exact mem_biUnion.mpr ⟨_,hb,hy⟩
  refine ⟨{ tests := U, test_count := cnt, test_size := size,
            test_subset := fun x B hb y hy => (G.mem_neighborFinset x y).mpr (sub x B hb y hy).1,
            beta := d.beta, symm := d.beta_symm, edges := fun x y h => by simp [beta,h],
            bounds := fun x y => ⟨(d.beta_entries x y hd hd₁).1,(d.beta_entries x y hd hd₁).2.trans hm⟩,
            support := fun x => d.beta_support x (hdeg x) hD,
            row_sum := fun x => (d.beta_row x hω ho hρ.le hs hd (hdeg x)).trans (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg D)),
            omitted := ?_ }⟩
  intro T hT
  obtain ⟨S,hS,hcol⟩ := om T hT
  refine ⟨S,hS,?_⟩
  intro X hX Y hY
  let missed x z : ℝ := if d.hardGraph.Adj x z ∧ z ∉ S x then 1 else 0
  have eq x (hx : x ∈ X) z :
      (if z ∈ S x then 0 else d.beta x z) = d.omittedHard x z - missed x z := by
    by_cases hy : z ∈ S x
    · have hh : d.hardGraph.Adj x z := by
        rcases hS x (hX hx) with he|hb
        · simp [he] at hy
        · exact sub x _ hb z hy
      simp [omittedHard,missed,hy,hh]
    · by_cases hh : d.hardGraph.Adj x z
      · simp [omittedHard,missed,hy,hh,beta,hh.1]
      · simp [omittedHard,missed,hy,hh]
  rw [sum_congr rfl (fun x hx => sum_congr rfl (fun z _ => eq x hx z))]
  simp_rw [sum_sub_distrib]
  apply (abs_sub ..).trans
  have hcut := d.coefficient_cut X Y ((card_le_card hX).trans hT) hY lam η hω hρ hρ₁ hd hd₁
    (hu X Y ((card_le_card hX).trans hT) hY) budget
  have hnn : 0 ≤ ∑ x ∈ X, ∑ z ∈ Y, missed x z := sum_nonneg fun x _ => sum_nonneg fun z _ => by dsimp [missed]; split <;> norm_num
  rw [abs_of_nonneg hnn,sum_comm (s := X) (t := Y) (f := missed)]
  have hz (z : V) : ∑ x ∈ X, missed x z ≤ η*D/2 := by
    apply le_trans _ (hcol z)
    simp [missed,←sum_filter]
    exact card_le_card (filter_subset_filter _ hX)
  have hh := sum_le_sum (s := Y) (fun z _ => hz z)
  simp only [sum_const,nsmul_eq_mul] at hh
  linarith only [hcut,hh,mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hY) (by positivity : 0 ≤ η*D/2)]
end Classes
end Vu.Revised
