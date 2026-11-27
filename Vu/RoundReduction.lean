module
public import Vu.ColoringState
public import Vu.Decomposition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace Vu
open Finset

@[expose] public noncomputable def roundNu (b : ℝ) : ℝ := min (b/80) (1/200)
@[expose] public noncomputable def roundTau (b p : ℝ) (j : ℕ) := Real.exp (-b*p*j/2)
@[expose] public noncomputable def clipCap (a C ν p K : ℝ) :=
  (8*K^2/(ν*p))*Real.exp (2*p*K*(C+1)^2/a)
@[expose] public noncomputable def roundCap (a C ν p : ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 => 2*clipCap a C ν p (roundCap a C ν p j)

/-- A finite number of rounds suffices. Stopping at equality is permitted
by the checked local-lemma completion. -/
public theorem exists_last_round (a b p : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) :
    ∃ J : ℕ, roundTau b p J/a ≤ 1/20 := by
  let J := ⌈2*Real.log (20/a)/(b*p)⌉₊
  have h := (div_le_iff₀ (mul_pos hb hp)).mp (Nat.le_ceil (2*Real.log (20/a)/(b*p)))
  change 2*Real.log (20/a) ≤ (J:ℝ)*(b*p) at h
  have ht : roundTau b p J ≤ Real.exp (-Real.log (20/a)) := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg,Real.exp_log (by positivity)] at ht
  exact ⟨J,(div_le_iff₀ ha).mpr (ht.trans_eq (by ring_nf; simp))⟩

/-- The one-round obligation of Lemma 5.1 on a finite palette. η and the
degree threshold are uniform over rounds j < J, input states, and graphs.
The coloring produced by the round extends all previously assigned colors. -/
@[expose] public def ColoringRoundTheorem : Prop :=
  ∀ (a b : ℝ) (R : ℕ) (C : ℝ), (0 < a ∧ a < 1) → (0 < b ∧ b < 1) → 2 ≤ C →
    let ν := roundNu b
    let p := a*ν
    ∀ J : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V P : Type)
      [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset P) (k : ℕ)
      (d : Decomposition G D k R b C η), (∀ x, G.degree x ≤ D) → a*D ≤ k → k ≤ 2*D →
      (∀ x, (L x).card = k) → ∀ j < J, ∀ s : ColoringState G L k,
      RoundBounds s d.tests a b (roundTau b p j) (roundCap a C ν p j) →
      ∃ s' : ColoringState G L k, (∀ x c, s.color x = some c → s'.color x = some c) ∧
        RoundBounds s' d.tests a b (roundTau b p (j+1)) (roundCap a C ν p (j+1))

/-- Proposition 3.2 from the one-round lemma. The finite palette consists
of exactly those colors appearing in the given lists, with no finiteness
assumed on the type of colors in the Challenge. -/
public theorem coloring_of_round (step : ColoringRoundTheorem) : ColoringFromDecompositionTheorem := by
  classical
  intro a b R C ha hb hC
  let ν := roundNu b
  let p := a*ν
  have hν : 0 < ν := lt_min (by linarith [hb.1]) (by norm_num)
  have hp : 0 < p := mul_pos ha.1 hν
  obtain ⟨J,hstop⟩ := exists_last_round a b p ha.1 hb.1 hp
  obtain ⟨η,hη,D₀,hstep⟩ := step a b R C ha hb hC J
  refine ⟨η,hη,max 1 D₀,?_⟩
  intro D hD V P _ G _ hdeg k hak hk ⟨d⟩ L hL
  let palette := univ.biUnion L
  let embed (x : V) : ↥(L x) ↪ ↥palette := {
    toFun := fun c => ⟨c.val,mem_biUnion.mpr ⟨x,mem_univ _,c.property⟩⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun d : ↥palette => d.val) h) }
  let L' (x : V) := (L x).attach.map (embed x)
  have hL' (x : V) : (L' x).card = k := by simp [L',hL]
  have hstate (j : ℕ) (hj : j ≤ J) : ∃ s : ColoringState G L' k,
      RoundBounds s d.tests a b (roundTau b p j) (roundCap a C ν p j) := by
    induction j with
    | zero =>
      exact ⟨initial_state G L' k hL',by simpa [roundTau,roundCap] using initial_round_bounds G L' D k R a b C η d ha.1 hdeg hak hL'⟩
    | succ j ih =>
      obtain ⟨s,hs⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨s',_,hs'⟩ := hstep D ((le_max_right _ _).trans hD) V (↥palette) G L' k d hdeg hak hk hL' j hj s hs
      exact ⟨s',hs'⟩
  obtain ⟨s,hs⟩ := hstate J le_rfl
  have hposD : 0 < D := (le_max_left 1 _).trans hD
  have hpos : 0 < (k:ℝ) := (mul_pos ha.1 (Nat.cast_pos.mpr hposD)).trans_le hak
  obtain ⟨f,hl,_,hprop⟩ := finish_state G L' k (Nat.cast_pos.mp hpos) s _ _ _ _ _ hs hstop
  refine ⟨fun x => (f x).val,?_,?_⟩
  · intro x
    obtain ⟨c,_,he⟩ := mem_map.mp (hl x)
    change (f x).val ∈ L x
    rw [← he]; exact c.property
  · intro x y hxy he; exact hprop hxy (Subtype.ext he)

/-- The unchanged Challenge follows from Lemma 5.1 alone. -/
public theorem main_of_round (step : ColoringRoundTheorem) : FixedRatioBound :=
  main_of_coloring (coloring_of_round step)
end Vu
