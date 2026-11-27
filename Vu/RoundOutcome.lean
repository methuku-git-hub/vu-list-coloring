module
public import Vu.RoundWeights
public import Vu.MarkLaw
namespace Vu
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {L : V → Finset C} (s : ColoringState G L k)

/-- The nonempty offer sets receive a color using one fixed order. -/
@[expose] public noncomputable def accepted (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : C → V → Bool) (x : V) : Option C := by
  classical
  letI : LinearOrder C := (Fintype.equivFin C).linearOrder
  let O := univ.filter fun c => x ∈ offerSet G univ (ω c)
  exact if h : O.Nonempty then some (O.min' h) else none

public theorem accepted_mem (ω : C → V → Bool) (x : V) (c : C) (hc : accepted G ω x = some c) :
    x ∈ offerSet G univ (ω c) := by
  classical
  letI : LinearOrder C := (Fintype.equivFin C).linearOrder
  dsimp only [accepted] at hc
  split at hc
  next h =>
    have hh := Finset.min'_mem _ h
    obtain rfl := Option.some.inj hc
    exact (mem_filter.mp hh).2
  next => contradiction

public theorem no_accept_iff (ω : C → V → Bool) (x : V) :
    accepted G ω x = none ↔ ∀ c, x ∉ offerSet G univ (ω c) := by
  classical
  dsimp only [accepted]
  split
  next h =>
    obtain ⟨c,hc⟩ := h
    simp only [Option.some_ne_none,false_iff]
    exact fun hh => hh c (mem_filter.mp hc).2
  next h => simpa using h

/-- For an arbitrary outcome of the marks, an already fixed color takes
precedence; an uncolored vertex receiving an offer accepts one. -/
@[expose] public noncomputable def extendedColor (ω : C → V → Bool) (x : V) : Option C :=
  (s.color x).orElse (fun _ => accepted G ω x)

public theorem extended_none_iff (ω : C → V → Bool) (x : V) :
    extendedColor s ω x = none ↔ s.color x = none ∧ accepted G ω x = none := by
  cases h : s.color x <;> simp [extendedColor,h]

/-- Deterministic update of properness, eligibility and weight normalization.
The hypotheses on retained weights are exactly those proved for (W2)-(W3)
and the lower bound on the normalization denominator. -/
public theorem extend_coloring_state (ω : C → V → Bool) (w : V → C → ℝ)
    (hmark : ∀ x c, ω c x = true → 0 < s.weight x c)
    (hw : ∀ x c, 0 ≤ w x c) (hold : ∀ x c, s.weight x c = 0 → w x c = 0)
    (hkill : ∀ x y c, G.Adj x y → ω c y = true → w x c = 0)
    (hden : ∀ x, extendedColor s ω x = none → 0 < ∑ c, w x c) :
    ∃ s' : ColoringState G L k, s'.color = extendedColor s ω ∧
      (∀ x c, s'.weight x c = if extendedColor s ω x = none then k*w x c/(∑ e, w x e) else 0) ∧
      ∀ x c, s.color x = some c → s'.color x = some c := by
  classical
  let col := extendedColor s ω
  let val (x : V) (c : C) : ℝ := if col x = none then k*w x c/(∑ e, w x e) else 0
  have prior (x : V) (c : C) (h : s.color x = some c) : col x = some c := by simp [col,extendedColor,h]
  have cases' (x : V) (c : C) (h : col x = some c) : s.color x = some c ∨ x ∈ offerSet G univ (ω c) := by
    cases hx : s.color x with
    | none => exact Or.inr (accepted_mem ω x c (by simpa [col,extendedColor,hx] using h))
    | some a =>
      simp only [col,extendedColor,hx,Option.orElse_some,Option.some.injEq] at h
      simp [h]
  have hnew x c (h : x ∈ offerSet G univ (ω c)) := (mem_filter.mp h).2
  refine ⟨{
    color := col
    weight := val
    listed := ?_
    proper := ?_
    nonneg := ?_
    outside := ?_
    painted := ?_
    blocked := ?_
    total := ?_},rfl,fun _ _ => rfl,prior⟩
  · intro x c hc
    rcases cases' x c hc with old | new
    · exact s.listed x c old
    · by_contra hn
      exact (hmark x c (hnew x c new).1).ne' (s.outside x c hn)
  · intro x y c hxy hx hy
    rcases cases' x c hx with a | a <;> rcases cases' y c hy with b | b
    · exact s.proper x y c hxy a b
    · exact (hmark y c (hnew y c b).1).ne' (s.blocked y x c hxy.symm a)
    · exact (hmark x c (hnew x c a).1).ne' (s.blocked x y c hxy b)
    · have h := (hnew x c a).2 y ((G.mem_neighborFinset _ _).mpr hxy)
      simp [(hnew y c b).1] at h
  · intro x c
    dsimp [val]; split
    next h => exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _ _)) (hden x h).le
    next => exact le_rfl
  · intro x c hn
    simp [val,hold x c (s.outside x c hn)]
  · intro x c hn
    simp [val,hn]
  · intro x y c ha hy
    rcases cases' y c hy with old | new
    · simp [val,hold x c (s.blocked x y c ha old)]
    · simp [val,hkill x y c ha (hnew y c new).1]
  · intro x hx
    simp [val,hx,←sum_div,←mul_sum,(hden x hx).ne']

end Vu
