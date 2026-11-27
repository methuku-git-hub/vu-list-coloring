module
public import Vu.HardNeighbors
public import Vu.GroupPacking
namespace Vu
open Finset

public theorem pack_fibers_using {V A : Type*} [DecidableEq V] [DecidableEq A]
    (grouping : ∀ (F : Finset (Finset V)) (D : ℕ) (s : ℝ), 0 < s →
      (∀ S ∈ F, (S.card:ℝ) ≤ s) → (∑ S ∈ F, S.card ≤ D) →
      ∃ B : Finset (Finset V), (∀ S ∈ F, ∃ T ∈ B, S ⊆ T) ∧
        B.biUnion id = F.biUnion id ∧ (∀ S ∈ B, (S.card:ℝ) ≤ s) ∧ (B.card:ℝ) ≤ 2*D/s+1)
    (N : Finset V) (g : V → A) (D : ℕ) (s : ℝ) (hs : 0 < s) (hN : N.card ≤ D)
    (hsize : ∀ a, ((N.filter fun z => g z = a).card : ℝ) ≤ s) :
    ∃ (B : Finset (Finset V)) (pack : A → Finset V),
      B.biUnion id = N ∧ (∀ U ∈ B, (U.card : ℝ) ≤ s) ∧ (B.card : ℝ) ≤ 2*D/s+1 ∧
      (∀ a, pack a = ∅ ∨ pack a ∈ B) ∧ ∀ z ∈ N, z ∈ pack (g z) := by
  classical
  let fiber a := N.filter fun z => g z = a
  let F := (N.image g).image fiber
  have inj : Set.InjOn fiber (N.image g) := by
    intro a ha b _ heq
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    have hm : x ∈ fiber (g x) := mem_filter.mpr ⟨hx,rfl⟩
    have hb : x ∈ fiber b := heq ▸ hm
    exact (mem_filter.mp hb).2
  have hcount : ∑ S ∈ F, S.card ≤ D := by
    change ∑ S ∈ (N.image g).image fiber, S.card ≤ D
    rw [sum_image inj]
    exact (card_eq_sum_card_image g N).symm.le.trans hN
  have hunion : F.biUnion id = N := by
    ext x
    constructor
    · intro hx
      obtain ⟨_,hS,hx⟩ := mem_biUnion.mp hx
      obtain ⟨a,_,rfl⟩ := mem_image.mp hS
      exact (mem_filter.mp hx).1
    · intro hx
      exact mem_biUnion.mpr ⟨_,mem_image_of_mem fiber (mem_image_of_mem g hx),mem_filter.mpr ⟨hx,rfl⟩⟩
  obtain ⟨B,hcover,hu,hb,hc⟩ := grouping F D s hs (fun S hS => by
    obtain ⟨a,_,rfl⟩ := mem_image.mp hS; exact hsize a) hcount
  let pack a := if h : ∃ U ∈ B, fiber a ⊆ U then h.choose else ∅
  refine ⟨B,pack,hu.trans hunion,hb,hc,?_,?_⟩
  · intro a; dsimp [pack]; split
    next h => exact Or.inr h.choose_spec.1
    next => exact Or.inl rfl
  · intro z hz
    have he := hcover _ (mem_image_of_mem fiber (mem_image_of_mem g hz))
    simpa [pack,he] using he.choose_spec.2 (mem_filter.mpr ⟨hz,rfl⟩)

public theorem pack_fibers {V A : Type*} [DecidableEq V] [DecidableEq A]
    (N : Finset V) (g : V → A) (D : ℕ) (s : ℝ) (hs : 0 < s) (hN : N.card ≤ D)
    (hsize : ∀ a, ((N.filter fun z => g z = a).card : ℝ) ≤ s) :
    ∃ (B : Finset (Finset V)) (pack : A → Finset V),
      B.biUnion id = N ∧ (∀ U ∈ B, (U.card : ℝ) ≤ s) ∧ (B.card : ℝ) ≤ 2*D/s+1 ∧
      (∀ a, pack a = ∅ ∨ pack a ∈ B) ∧ ∀ z ∈ N, z ∈ pack (g z) :=
  pack_fibers_using pack_neighbor_groups N g D s hs hN hsize

/-- Construct the tests and their group-to-test mapping from the oriented
label witnesses. The two common witnesses give the size bound on each fiber. -/
public theorem hard_tests_from_witnesses {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    (H : SimpleGraph V) [DecidableRel H.Adj] (J : SimpleGraph A) (L P : V → Finset A)
    (W : A → Finset V) (D : ℕ) (s : ℝ) (hs : 0 < s) (hdeg : ∀ x, H.degree x ≤ D)
    (htwo : ∀ x (a : ↥(L x)), ∃ y ≠ x, a.val ∈ L y)
    (hwitness : ∀ x y : V, x ≠ y → ∀ g : Finset A, g ⊆ L x → g ⊆ L y → ((g.biUnion W).card : ℝ) ≤ s)
    (hlabel : ∀ x z, H.Adj x z → ∃ a : ↥(L x), a.val ∈ P z ∧ z ∈ W a) :
    ∃ (tests : V → Finset (Finset V)) (packed : V → Finset A → Finset V),
      (∀ x, (tests x).biUnion id = H.neighborFinset x) ∧ (∀ x, ∀ U ∈ tests x, (U.card : ℝ) ≤ s) ∧
      (∀ x, ((tests x).card : ℝ) ≤ 2*D/s+1) ∧
      (∀ x (a : ↥(L x)), packed x (labelGroup J L x a) = ∅ ∨ packed x (labelGroup J L x a) ∈ tests x) ∧
      (∀ x z, H.Adj x z → ∃ a : ↥(L x), a.val ∈ P z ∧ z ∈ packed x (labelGroup J L x a)) := by
  classical
  let a (x z : V) (h : H.Adj x z) := (hlabel x z h).choose
  let g (x z : V) := if h : H.Adj x z then labelGroup J L x (a x z h) else ∅
  have hsize (x : V) (G : Finset A) :
      (((H.neighborFinset x).filter fun z => g x z = G).card : ℝ) ≤ s := by
    let F := (H.neighborFinset x).filter fun z => g x z = G
    rcases F.eq_empty_or_nonempty with h | ⟨z,hz⟩
    · change (F.card : ℝ) ≤ s
      simpa [h] using hs.le
    obtain ⟨hz',heq⟩ := mem_filter.mp hz
    have hzadj := (H.mem_neighborFinset x z).mp hz'
    have hgroup : labelGroup J L x (a x z hzadj) = G := by simpa [g,hzadj] using heq
    obtain ⟨_,hG,⟨y,hy,hY⟩⟩ := labelGroup_witnesses J L x _ (htwo x (a x z hzadj))
    rw [hgroup] at hG hY
    apply (Nat.cast_le.mpr (card_le_card ?_)).trans (hwitness x y hy.symm G hG hY)
    intro u hu
    obtain ⟨hu',hug⟩ := mem_filter.mp hu
    have hadj := (H.mem_neighborFinset x u).mp hu'
    have hgu : labelGroup J L x (a x u hadj) = G := by simpa [g,hadj] using hug
    have hmem := (labelGroup_witnesses J L x _ (htwo x (a x u hadj))).1
    exact mem_biUnion.mpr ⟨_,hgu ▸ hmem,(hlabel x u hadj).choose_spec.2⟩
  choose B pack hcov hb hc hp hg using fun x => pack_fibers (H.neighborFinset x) (g x) D s hs
    (by simpa using hdeg x) (hsize x)
  refine ⟨B,pack,hcov,hb,hc,fun x _ => hp x _,?_⟩
  intro x z hz
  exact ⟨a x z hz,(hlabel x z hz).choose_spec.1,by
    simpa [g,hz] using hg x z ((H.mem_neighborFinset x z).mpr hz)⟩

/-- Simultaneous construction of the test families in (D1) and (D2).
The test family is fixed before T is chosen. Its size bound is independent
of the overlap parameters r and K. -/
public theorem hard_test_families (r K : ℕ) (hr : 0 < r) (η : ℝ) (he : 0 < η) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V A : Type*) [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
      (H : SimpleGraph V) [DecidableRel H.Adj] (L P : V → Finset A) (W : A → Finset V)
      (s : ℝ), 0 < s → (∀ x, H.degree x ≤ D) →
    (∀ x, (L x).card ≤ r) → (∀ x, (P x).card ≤ K) →
    (∀ a, ((univ.filter fun x => a ∈ L x).card : ℝ) ≤ 2*D) →
    (∀ x (a : ↥(L x)), ∃ y ≠ x, a.val ∈ L y) →
    (∀ x y : V, x ≠ y → ∀ g : Finset A, g ⊆ L x → g ⊆ L y → ((g.biUnion W).card : ℝ) ≤ s) →
    (∀ x z, H.Adj x z → ∃ a : ↥(L x), a.val ∈ P z ∧ z ∈ W a) →
    ∃ U : V → Finset (Finset V),
      (∀ x, (U x).biUnion id = H.neighborFinset x) ∧ (∀ x, ∀ B ∈ U x, (B.card : ℝ) ≤ s) ∧
      (∀ x, ((U x).card : ℝ) ≤ 2*D/s+1) ∧
      ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ U x) ∧
        RowNormLE (fun x z => if H.Adj x z ∧ z ∉ S x then 1 else 0) T (η*D) := by
  obtain ⟨D₀,h₀⟩ := hard_neighbor_omission r K hr η he
  refine ⟨D₀,?_⟩
  intro D hd V A _ _ _ _ H _ L P W s hs hdeg hL hP hsize htwo hw hlabel
  let h := (D : ℝ)^(1/(2*(r : ℝ)) : ℝ)
  let J := overlapGraph L (D/h^2)
  obtain ⟨U,pack,hu,hcap,hnum,ht,he'⟩ := hard_tests_from_witnesses H J L P W D s hs hdeg htwo hw hlabel
  exact ⟨U,hu,hcap,hnum,h₀ D hd V A H L P U pack hdeg hL hP hsize ht he'⟩
end Vu
