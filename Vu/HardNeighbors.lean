module
public import Vu.LabelComponents

namespace Vu
open Finset

/-- Graph on labels used in the manuscript, with threshold t for the
number of common carriers. -/
@[expose] public noncomputable def overlapGraph {A V : Type*} [Fintype V] [DecidableEq A]
    (L : V → Finset A) (t : ℝ) : SimpleGraph A := by
  classical
  exact {
    Adj := fun a b => a ≠ b ∧ t ≤ ((univ.filter fun x => a ∈ L x ∧ b ∈ L x).card : ℝ)
    symm := ⟨fun a b h => ⟨h.1.symm, by simpa [and_comm] using h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }

/-- After the bounded-multiplicity labels and packed neighbor groups have
been constructed, (D2) holds for the actual overlap components with
h = D^(1/(2r)). The proof supplies the split exceptions and their bound. -/
public theorem hard_neighbor_omission (r K : ℕ) (hr : 0 < r) (η : ℝ) (he : 0 < η) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, let h := (D : ℝ)^(1/(2*(r : ℝ)) : ℝ)
    ∀ (V A : Type*) [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
      (H : SimpleGraph V) [DecidableRel H.Adj] (L partners : V → Finset A),
    let J := overlapGraph L (D/h^2)
    ∀ (tests : V → Finset (Finset V)) (packed : V → Finset A → Finset V),
    (∀ x, H.degree x ≤ D) → (∀ x, (L x).card ≤ r) → (∀ x, (partners x).card ≤ K) →
    (∀ a, ((univ.filter fun x => a ∈ L x).card : ℝ) ≤ 2*D) →
    (∀ x (a : ↥(L x)), packed x (labelGroup J L x a) = ∅ ∨ packed x (labelGroup J L x a) ∈ tests x) →
    (∀ x z, H.Adj x z → ∃ a : ↥(L x), a.val ∈ partners z ∧ z ∈ packed x (labelGroup J L x a)) →
    ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ tests x) ∧
      RowNormLE (fun x z => if H.Adj x z ∧ z ∉ S x then 1 else 0) T (η*D) := by
  let c := (r : ℝ) * (r.factorial : ℝ) * (2*r : ℝ)^(r-1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨D₀,h₀⟩ := omit_hard_neighbors r K hr c η hc he
  refine ⟨max 1 D₀, ?_⟩
  intro D hd h V A _ _ _ _ H _ L P J U pack hdeg hL hP hsize ht hedge
  classical
  let S (x : V) (a : A) := if ha : a ∈ L x then pack x (labelGroup J L x ⟨a,ha⟩) else ∅
  have hD : 0 < D := (le_max_left 1 D₀).trans hd
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hp : 0 < h := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hD) _
  have hh : 1 ≤ h := Real.one_le_rpow ((Nat.one_le_cast).mpr hD) (by positivity)
  have hpow : h^(2*r) = D := by
    dsimp [h]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    push_cast
    rw [one_div_mul_cancel (by positivity : (2*(r : ℝ)) ≠ 0), Real.rpow_one]
  let carry (a : A) := univ.filter fun x => a ∈ L x
  have havg : ∀ a b, J.Adj a b → D/h^2 ≤ ((carry a ∩ carry b).card : ℝ) := by
    intro a b hab
    have heq : carry a ∩ carry b = univ.filter fun x => a ∈ L x ∧ b ∈ L x := by ext; simp [carry]
    rw [heq]; exact hab.2
  have hjdeg := overlap_degree_bound J carry r D h (Nat.cast_pos.mpr hD) hp hsize
    (by intro x; simpa [carry] using hL x) havg
  apply h₀ D ((le_max_right _ _).trans hd) V A H L P U S (splitRows J L) hdeg hL hP
  · intro x a ha
    simpa [S,ha] using ht x ⟨a,ha⟩
  · intro x z hx
    obtain ⟨a,ha,hz⟩ := hedge x z hx
    exact ⟨a,a.property,ha,by simpa [S,a.property] using hz⟩
  · intro a
    exact actual_split_bound J L a r h D hr hh hpow hjdeg hL
  · intro x a ha b hb hne
    by_cases hs : x ∈ splitRows J L a
    · exact Or.inl hs
    apply Or.inr
    by_contra! hlarge
    have hab : J.Adj a b := ⟨fun heq => hne (heq ▸ rfl),hlarge.le⟩
    have hg := equal_group_of_adj J L x ⟨a,ha⟩ ⟨b,hb⟩ hab hs
    exact hne (by simpa [S,ha,hb] using congrArg (pack x) hg)
end Vu
