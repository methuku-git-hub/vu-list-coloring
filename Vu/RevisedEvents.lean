module
public import Vu.RevisedPretest
public import Vu.SuccessfulRound
public import Vu.LocalBalls
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

@[expose] public noncomputable def badTotal (a ν p τ cap : ℝ) (x : V) (ω : C → V → Bool) : Prop :=
  (∑ c ∈ L x, kept d s a ν p τ cap c (ω c) x) < k*(1-ν*p)

@[expose] public noncomputable def badTest (a ν p τ cap : ℝ) (x : V) (c : C) (i : Option (Finset V))
    (ω : C → V → Bool) : Prop :=
  let T := testSet G x i
  let Lₜ := threshold (testCoeff V a b i) k τ p b ν
  let w := fun y e => kept d s a ν p τ cap e (ω e) y
  (∑ y ∈ T, raw d s p c (ω c) y) ≤ Lₜ ∧
    (1-(1-4*ν)*p)*Lₜ < ∑ y ∈ T, remainingWeight (G := G) w ω c y

@[expose] public noncomputable def badAt (a ν p τ cap : ℝ) (x : V) (ω : C → V → Bool) : Prop :=
  (s.color x = none ∧ badTotal d s a ν p τ cap x ω) ∨
    ∃ c ∈ L x, 0 < s.weight x c ∧ ∃ i ∈ indices d x, badTest d s a ν p τ cap x c i ω

/-- The dependency graph joins distinct vertices with a nonzero coefficient.
Every original edge is already present because its coefficient is -1. -/
@[expose] public def influence : SimpleGraph V where
  Adj x y := x ≠ y ∧ d.beta x y ≠ 0
  symm := by constructor; intro x y h; exact ⟨Ne.symm h.1,by rw [d.symm y x]; exact h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

public noncomputable instance : DecidableRel (influence d).Adj := Classical.decRel _

public theorem influence_edge {x y : V} (h : G.Adj x y) : (influence d).Adj x y :=
  ⟨h.ne,by rw [d.edges x y h]; norm_num⟩

public theorem influence_degree (x : V) : (by classical exact (influence d).degree x) ≤ D^2 := by
  classical
  apply le_trans _ (d.support x)
  apply card_le_card (s := (influence d).neighborFinset x)
  intro y hy
  exact mem_filter.mpr ⟨mem_univ _,((SimpleGraph.mem_neighborFinset _ _ _).mp hy).2⟩

private theorem raw_local (p : ℝ) (x : V) (c : C) (u v : V → Bool)
    (he : ∀ y ∈ roundBall (influence d) x 1, u y = v y) :
    raw d s p c u x = raw d s p c v x := by
  classical
  unfold raw; congr 1
  apply prod_congr rfl
  intro y _
  by_cases hy : y ∈ roundBall (influence d) x 1
  · rw [he y hy]
  · have hxy : x ≠ y := by rintro rfl; exact hy ((roundBall_walk _ _ _ _).mpr ⟨.nil,by simp⟩)
    have hz : d.beta x y = 0 := by by_contra hn; exact hy (roundBall_neighbor _ (show (influence d).Adj x y from ⟨hxy,hn⟩))
    cases hu : u y <;> cases hv : v y <;> simp [Bernoulli.factor,hz]
private theorem kept_local (a ν p τ cap : ℝ) (x : V) (c : C) (u v : V → Bool)
    (he : ∀ y ∈ roundBall (influence d) x 2, u y = v y) :
    kept d s a ν p τ cap c u x = kept d s a ν p τ cap c v x := by
  classical
  have hpass : passes d s a ν p τ c u x ↔ passes d s a ν p τ c v x := by
    unfold passes
    apply forall_congr'; intro i
    by_cases hi : i ∈ indices d x
    · have hh : (∑ y ∈ testSet G x i, raw d s p c u y) = ∑ y ∈ testSet G x i, raw d s p c v y := by
        apply sum_congr rfl
        intro y hy
        have hxy := roundBall_neighbor (influence d) (influence_edge d ((G.mem_neighborFinset _ _).mp (index_subset d x i hi hy)))
        exact raw_local d s p y c u v (fun z hz => he z (roundBall_comp (influence d) hxy hz))
      simp [hh]
    · simp [hi]
  simp only [kept,hpass,raw_local d s p x c u v (fun y hy => he y (roundBall_mono (influence d) x (by decide : 1 ≤ 2) hy))]

private theorem no_offer_local (x : V) (u v : C → V → Bool)
    (he : ∀ y ∈ roundBall (influence d) x 1, ∀ c, u c y = v c y) :
    accepted G u x = none ↔ accepted G v x = none := by
  rw [no_accept_iff,no_accept_iff]
  apply forall_congr'; intro c
  have hx := he x ((roundBall_walk (influence d) x x 1).mpr ⟨.nil,by simp⟩) c
  have hn : (∀ y ∈ G.neighborFinset x, u c y = false) ↔ ∀ y ∈ G.neighborFinset x, v c y = false := by
    apply forall_congr'; intro y
    by_cases hy : y ∈ G.neighborFinset x
    · rw [he y (roundBall_neighbor (influence d) (influence_edge d ((G.mem_neighborFinset _ _).mp hy))) c]
    · simp [hy]
  simp only [offerSet,mem_filter,hx,hn]

/-- Both kinds of bad event at a vertex are determined by marks within
distance three in the coefficient graph. This is a statement about the joint law before any color
has been exposed. -/
public theorem bad_at_local (a ν p τ cap : ℝ) (x : V) :
    FiniteLaw.determinedBy (roundBall (influence d) x 3) (fun f : V → C → Bool => badAt d s a ν p τ cap x (fun c y => f y c)) := by
  classical
  intro f g hfg
  let u (c : C) (y : V) := f y c
  let v (c : C) (y : V) := g y c
  have he y (hy : y ∈ roundBall (influence d) x 3) (c : C) : u c y = v c y := congrFun (hfg y hy) c
  have htot : badTotal d s a ν p τ cap x u ↔ badTotal d s a ν p τ cap x v := by
    unfold badTotal
    rw [sum_congr rfl (fun c (_ : c ∈ L x) => kept_local d s a ν p τ cap x c (u c) (v c)
      (fun y hy => he y (roundBall_mono (influence d) x (by decide : 2 ≤ 3) hy) c))]
  have htest (c : C) (i : Option (Finset V)) (hi : i ∈ indices d x) :
      badTest d s a ν p τ cap x c i u ↔ badTest d s a ν p τ cap x c i v := by
    let T := testSet G x i
    have hb y (hy : y ∈ T) := roundBall_neighbor (influence d) (influence_edge d ((G.mem_neighborFinset _ _).mp (index_subset d x i hi hy)))
    have near y (hy : y ∈ T) z (hz : z ∈ roundBall (influence d) y 2) (e : C) := he z (roundBall_comp (influence d) (hb y hy) hz) e
    have hpre y (hy : y ∈ T) := raw_local d s p y c (u c) (v c) (fun z hz => near y hy z
      (roundBall_mono (influence d) y (by decide : 1 ≤ 2) hz) c)
    have hrem y (hy : y ∈ T) : remainingWeight (G := G) (fun z e => kept d s a ν p τ cap e (u e) z) u c y =
        remainingWeight (G := G) (fun z e => kept d s a ν p τ cap e (v e) z) v c y := by
      have hnil := no_offer_local d (G := G) y u v (fun z hz => near y hy z (roundBall_mono (influence d) y (by decide : 1 ≤ 2) hz))
      simp only [remainingWeight,hnil,kept_local d s a ν p τ cap y c (u c) (v c) (fun z hz => near y hy z hz c)]
    dsimp only [badTest]
    rw [sum_congr rfl hpre,sum_congr rfl hrem]
  apply propext
  change badAt d s a ν p τ cap x u ↔ badAt d s a ν p τ cap x v
  unfold badAt
  rw [htot]
  constructor <;> rintro (h|⟨c,hc,hw,i,hi,hh⟩)
  · exact Or.inl h
  · exact Or.inr ⟨c,hc,hw,i,hi,(htest c i hi).mp hh⟩
  · exact Or.inl h
  · exact Or.inr ⟨c,hc,hw,i,hi,(htest c i hi).mpr hh⟩
end Vu.Revised
