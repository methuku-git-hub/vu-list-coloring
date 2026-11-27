module

public import Vu.OmittedNeighbors
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Vu
open Finset

/-- The number of labels occurring on more than l rows is bounded by the
total number of row-label memberships divided by l+1. -/
public theorem frequent_label_count {V A : Type*} [Fintype A] [DecidableEq A]
    (T : Finset V) (labels : V → Finset A) (r l : ℕ) (h : ∀ x ∈ T, (labels x).card ≤ r) :
    (univ.filter fun a => l < (T.filter fun x => a ∈ labels x).card).card * (l+1) ≤ T.card*r := by
  let F := univ.filter fun a => l < (T.filter fun x => a ∈ labels x).card
  have ht : ∑ a, (T.filter fun x => a ∈ labels x).card = ∑ x ∈ T, (labels x).card := by
    simp only [card_filter]
    rw [sum_comm]
    simp
  calc
    _ = ∑ _a ∈ F, (l+1) := by simp [F]
    _ ≤ ∑ a ∈ F, (T.filter fun x => a ∈ labels x).card :=
      by
      apply sum_le_sum
      intro a ha
      exact Nat.succ_le_of_lt (mem_filter.mp ha).2
    _ ≤ ∑ a, (T.filter fun x => a ∈ labels x).card := sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := by rw [ht]; simpa using sum_le_sum h

/-- The row choices in Lemma 4.8. A carried label has a test containing
its assigned neighbors. Two carried labels lying in different tests either
meet in at most q rows or the first label's component was split there.
The choice is made once for each row and works simultaneously for all columns. -/
public theorem choose_omissions {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (T : Finset V) (N : V → Finset V) (labels : V → Finset A) (tests : V → Finset (Finset V))
    (test : V → A → Finset V) (partners : V → Finset A) (split : A → Finset V)
    (D r l q s k : ℕ)
    (hN : ∀ x ∈ T, (N x).card ≤ D) (hr : ∀ x ∈ T, (labels x).card ≤ r)
    (htest : ∀ x ∈ T, ∀ a ∈ labels x, test x a = ∅ ∨ test x a ∈ tests x)
    (hedge : ∀ x ∈ T, ∀ z ∈ N x, ∃ a ∈ labels x, a ∈ partners z ∧ z ∈ test x a)
    (hpartners : ∀ z, (partners z).card ≤ k) (hsplit : ∀ a, (split a).card ≤ s)
    (hsep : ∀ x ∈ T, ∀ a ∈ labels x, ∀ b ∈ labels x, test x a ≠ test x b →
      x ∈ split a ∨ (T.filter fun y => a ∈ labels y ∧ b ∈ labels y).card ≤ q) :
    ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ tests x) ∧
      RowNormLE (fun x z => if z ∈ N x ∧ z ∉ S x then 1 else 0) T
        (Real.sqrt ((D * (k * max l (s + (T.card*r/(l+1))*q)) : ℕ) : ℝ)) := by
  classical
  let F := univ.filter fun a => l < (T.filter fun x => a ∈ labels x).card
  have hf : F.card ≤ T.card*r/(l+1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (frequent_label_count T labels r l hr)
  let has x := ∃ a ∈ labels x, a ∈ F
  let S x := if h : has x then test x h.choose else ∅
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    by_cases h : has x
    · simpa [S,h] using htest x hx h.choose h.choose_spec.1
    · simp [S,h]
  let miss a := T.filter fun x => a ∈ labels x ∧ test x a ≠ S x
  have hmiss (a : A) : (miss a).card ≤ max l (s + (T.card*r/(l+1))*q) := by
    by_cases ha : a ∈ F
    · let overlap b := T.filter fun y => a ∈ labels y ∧ b ∈ labels y
      let small b := if (overlap b).card ≤ q then overlap b else ∅
      apply (missed_label_card_le (miss a) (split a) F small q ?_ ?_).trans
        ((Nat.add_le_add (hsplit a) (Nat.mul_le_mul_right q hf)).trans (le_max_right ..))
      · intro x hx
        obtain ⟨hxt,hax,hne⟩ := mem_filter.mp hx
        have hh : has x := ⟨a,hax,ha⟩
        have hb := hh.choose_spec
        have hd : test x a ≠ test x hh.choose := by simpa [S,hh] using hne
        rcases hsep x hxt a hax hh.choose hb.1 hd with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hh.choose, hb.2, by
            have hm : x ∈ overlap hh.choose := mem_filter.mpr ⟨hxt,hax,hb.1⟩
            simpa [small, show (overlap hh.choose).card ≤ q from h] using hm⟩
      · intro b _
        dsimp [small]; split <;> simp_all
    · apply le_trans (b := (T.filter fun x => a ∈ labels x).card)
      · apply card_le_card
        intro x hx
        exact mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.1⟩
      · apply le_trans _ (le_max_left ..)
        simpa [F] using ha
  let residual x := N x \ S x
  have hcols z : (T.filter fun x => z ∈ residual x).card ≤ k * max l (s + T.card*r/(l+1)*q) := by
    apply residual_column_card_le _ (partners z) miss _ _ ?_ (hpartners z) (fun a _ => hmiss a)
    intro x hx
    obtain ⟨hxt,hz⟩ := mem_filter.mp hx
    obtain ⟨hzn,hzs⟩ := mem_sdiff.mp hz
    obtain ⟨a,ha,hp,hza⟩ := hedge x hxt z hzn
    exact ⟨a,hp,mem_filter.mpr ⟨hxt,ha,fun he => hzs (he ▸ hza)⟩⟩
  simpa only [residual, mem_sdiff] using residual_rowNormLE T residual D _ (fun x hx =>
    (card_le_card sdiff_subset).trans (hN x hx)) hcols

/-- The square-root bound in the row selection is at most ηD at the
thresholds used in the manuscript. All three integer roundings are explicit. -/
public theorem omission_norm_budget (D n r k s : ℕ) (h c η : ℝ)
    (hn : n ≤ D) (hD : 0 < D) (hh : 1 ≤ h) (hc : 0 ≤ c) (he : 0 < η)
    (hs : (s : ℝ) ≤ c*(D/h^2)) (hlarge : k*(1+c+r) ≤ η^2*h) :
    let l := ⌊(D : ℝ)/h⌋₊
    let q := ⌊(D : ℝ)/h^2⌋₊
    √((D*(k*max l (s+(n*r/(l+1))*q)) : ℕ) : ℝ) ≤ η*D := by
  dsimp only
  let l := ⌊(D : ℝ)/h⌋₊
  let q := ⌊(D : ℝ)/h^2⌋₊
  let f := n*r/(l+1)
  have hh₀ : 0 < h := zero_lt_one.trans_le hh
  have hD₀ : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hl : (l : ℝ) ≤ D/h := Nat.floor_le (by positivity)
  have hq : (q : ℝ) ≤ D/h^2 := Nat.floor_le (by positivity)
  have hl' : (D : ℝ)/h ≤ (l : ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hmul : (f : ℝ)*((l : ℝ)+1) ≤ (D : ℝ)*r := by
    exact_mod_cast (Nat.div_mul_le_self (n*r) (l+1)).trans (Nat.mul_le_mul_right r hn)
  have hf : (f : ℝ) ≤ r*h := by
    apply (mul_le_mul_iff_of_pos_right (div_pos hD₀ hh₀)).mp
    calc
      _ ≤ (f : ℝ)*((l : ℝ)+1) := mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg _)
      _ ≤ _ := hmul.trans_eq (by field_simp)
  have hm : ((max l (s+f*q) : ℕ) : ℝ) ≤ (1+c+r)*(D/h) := by
    have hratio : (D : ℝ)/h^2 ≤ D/h := div_le_div_of_nonneg_left hD₀.le hh₀ (by nlinarith)
    have hprod := mul_le_mul hf hq (Nat.cast_nonneg _) (by positivity)
    have hEq : ((r : ℝ)*h)*(D/h^2) = r*(D/h) := by field_simp
    rw [hEq] at hprod
    push_cast
    apply max_le
    · nlinarith [mul_nonneg hc (div_pos hD₀ hh₀).le, mul_nonneg (Nat.cast_nonneg r) (div_pos hD₀ hh₀).le]
    · linarith [hs.trans (mul_le_mul_of_nonneg_left hratio hc), div_pos hD₀ hh₀]
  have hk := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg k)
  have hlrg := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ (D : ℝ)/h by positivity)
  have heq : η^2*h*(D/h) = η^2*D := by field_simp
  rw [heq, mul_assoc] at hlrg
  have htop := mul_le_mul_of_nonneg_left (hk.trans hlrg) hD₀.le
  apply Real.sqrt_le_iff.mpr ⟨mul_nonneg he.le hD₀.le, ?_⟩
  simp only [Nat.cast_mul]
  change (D : ℝ)*((k : ℝ)*((max l (s+f*q) : ℕ) : ℝ)) ≤ _
  nlinarith only [htop]

/-- Uniform degree threshold for the last inequality of (D2), with
h^(2r)=D. This fixes the threshold before any graph or row set is chosen. -/
public theorem omission_degree_threshold (r k : ℕ) (hr : 0 < r) (c η : ℝ) (he : 0 < η) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, 0 < D ∧ ∀ h : ℝ, 0 ≤ h → h^(2*r) = D →
      1 ≤ h ∧ k*(1+c+r) ≤ η^2*h := by
  let H : ℝ := max 1 (k*(1+c+r)/η^2)
  refine ⟨max 1 ⌈H^(2*r)⌉₊, ?_⟩
  intro D hd
  refine ⟨(le_max_left _ _).trans hd, ?_⟩
  intro h hh hpow
  have hle : H^(2*r) ≤ h^(2*r) := hpow ▸ (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hd))
  have hH := le_of_pow_le_pow_left₀ (by omega : 2*r ≠ 0) hh hle
  refine ⟨(le_max_left _ _).trans hH, ?_⟩
  have := (div_le_iff₀ (sq_pos_of_pos he)).mp ((le_max_right _ _).trans hH)
  simpa [mul_comm] using this
/-- Lemma 4.8 applied to the hard-edge graph. The hypotheses describe its
oriented edge labels, the packed tests, and the split exceptional vertices.
The omitted test may depend on T. The degree threshold depends only on the
four numerical parameters and the resulting bound is precisely (D2). -/
public theorem omit_hard_neighbors (r k : ℕ) (hr : 0 < r) (c η : ℝ) (hc : 0 ≤ c) (he : 0 < η) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, let h := (D : ℝ) ^ (1/(2*(r : ℝ)) : ℝ)
    ∀ (V A : Type*) [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
      (H : SimpleGraph V) [DecidableRel H.Adj] (labels partners : V → Finset A)
      (tests : V → Finset (Finset V)) (test : V → A → Finset V) (split : A → Finset V),
    (∀ x, H.degree x ≤ D) → (∀ x, (labels x).card ≤ r) → (∀ z, (partners z).card ≤ k) →
    (∀ x, ∀ a ∈ labels x, test x a = ∅ ∨ test x a ∈ tests x) →
    (∀ x z, H.Adj x z → ∃ a ∈ labels x, a ∈ partners z ∧ z ∈ test x a) →
    (∀ a, ((split a).card : ℝ) ≤ c*(D/h^2)) →
    (∀ x, ∀ a ∈ labels x, ∀ b ∈ labels x, test x a ≠ test x b →
      x ∈ split a ∨ ((univ.filter fun y => a ∈ labels y ∧ b ∈ labels y).card : ℝ) ≤ D/h^2) →
    ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ tests x) ∧
      RowNormLE (fun x z => if H.Adj x z ∧ z ∉ S x then 1 else 0) T (η*D) := by
  obtain ⟨D₀, thresh⟩ := omission_degree_threshold r k hr c η he
  refine ⟨D₀, ?_⟩
  intro D hd h V A _ _ _ _ H _ L P U test split hdeg hlabels hp htest hedge hsplit hsep T hT
  classical
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hpow : h^(2*r) = D := by
    dsimp [h]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    push_cast
    rw [one_div_mul_cancel (by positivity : (2*(r : ℝ)) ≠ 0), Real.rpow_one]
  obtain ⟨hD, hh⟩ := thresh D hd
  obtain ⟨hh, hbig⟩ := hh h (Real.rpow_nonneg (Nat.cast_nonneg _) _) hpow
  let l := ⌊(D : ℝ)/h⌋₊
  let q := ⌊(D : ℝ)/h^2⌋₊
  let s := ⌊c*(D/h^2)⌋₊
  obtain ⟨S, hs, hnorm⟩ := choose_omissions T (fun x => H.neighborFinset x) L U test P split
    D r l q s k (fun x _ => by simpa using hdeg x) (fun x _ => hlabels x)
    (fun x _ => htest x) (fun x _ z hz => hedge x z ((H.mem_neighborFinset x z).mp hz))
    hp (fun a => Nat.le_floor (hsplit a)) (by
      intro x _ a ha b hb hne
      apply (hsep x a ha b hb hne).imp_right
      intro hsmall
      apply (card_le_card (filter_subset_filter _ (subset_univ T))).trans (Nat.le_floor hsmall))
  have hbudget := omission_norm_budget D T.card r k s h c η hT hD hh hc he (Nat.floor_le (by positivity)) hbig
  refine ⟨S,hs,?_⟩
  intro f
  apply le_trans (by simpa only [H.mem_neighborFinset] using hnorm f)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hbudget 2)
    (sum_nonneg fun _ _ => sq_nonneg _)
end Vu
