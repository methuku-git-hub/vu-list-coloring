module
public import Vu.SuccessfulRound
public import Vu.LocalBalls
namespace Vu
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {b M η : ℝ}
  (d : Decomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

@[expose] public noncomputable def badTotal (a ν p τ cap : ℝ) (x : V) (ω : C → V → Bool) : Prop :=
  (∑ c ∈ L x, keptWeight d s a ν p τ cap c (ω c) x) < k*(1-ν*p)

@[expose] public noncomputable def badTest (a ν p τ cap : ℝ) (x : V) (c : C) (i : Option (Finset V))
    (ω : C → V → Bool) : Prop :=
  let T := testSet G x i
  let Lₜ := testThreshold (testCoeff V a b i) k τ ν p b
  let w := fun y e => keptWeight d s a ν p τ cap e (ω e) y
  (∑ y ∈ T, preWeight d s p cap c (ω c) y) ≤ Lₜ ∧
    (1-(1-5*ν)*p)*Lₜ < ∑ y ∈ T, remainingWeight (G := G) w ω c y

@[expose] public noncomputable def badAt (a ν p τ cap : ℝ) (x : V) (ω : C → V → Bool) : Prop :=
  (s.color x = none ∧ badTotal d s a ν p τ cap x ω) ∨
    ∃ c ∈ L x, 0 < s.weight x c ∧ ∃ i ∈ testIndices d x, badTest d s a ν p τ cap x c i ω

private theorem pre_local (p cap : ℝ) (x : V) (c : C) (u v : V → Bool)
    (he : ∀ y ∈ roundBall G x 4, u y = v y) :
    preWeight d s p cap c u x = preWeight d s p cap c v x := by
  unfold preWeight; congr 2
  apply prod_congr rfl
  intro y _
  by_cases hy : y ∈ roundBall G x 4
  · rw [he y hy]
  · have hh : ¬d.H.Adj x y := fun h => hy (roundBall_mono G x (by decide : 1 ≤ 4)
        (roundBall_neighbor G ((d.edge_iff x y).mpr (Or.inl h))))
    have hz : d.matrix x y = 0 := by by_contra h; exact hy ((roundBall_walk G x y 4).mpr (d.local_support x y h))
    cases h1 : u y <;> cases h2 : v y <;> simp [Bernoulli.factor,updateEntry,h1,h2,hh,hz]

private theorem kept_local (a ν p τ cap : ℝ) (x : V) (c : C) (u v : V → Bool)
    (he : ∀ y ∈ roundBall G x 5, u y = v y) :
    keptWeight d s a ν p τ cap c u x = keptWeight d s a ν p τ cap c v x := by
  classical
  have hpass : passes d s a ν p τ cap c u x ↔ passes d s a ν p τ cap c v x := by
    unfold passes
    apply forall_congr'; intro i
    by_cases hi : i ∈ testIndices d x
    · have hh : (∑ y ∈ testSet G x i, preWeight d s p cap c u y) = ∑ y ∈ testSet G x i, preWeight d s p cap c v y := by
        apply sum_congr rfl
        intro y hy
        have hxy := roundBall_neighbor G ((G.mem_neighborFinset _ _).mp (indexed_test_subset d x i hi hy))
        exact pre_local d s p cap y c u v (fun z hz => he z (roundBall_comp G hxy hz))
      simp [hh]
    · simp [hi]
  simp only [keptWeight,hpass,pre_local d s p cap x c u v (fun y hy => he y (roundBall_mono G x (by decide : 4 ≤ 5) hy))]

private theorem no_offer_local (x : V) (u v : C → V → Bool)
    (he : ∀ y ∈ roundBall G x 1, ∀ c, u c y = v c y) :
    accepted G u x = none ↔ accepted G v x = none := by
  rw [no_accept_iff,no_accept_iff]
  apply forall_congr'; intro c
  have hx := he x ((roundBall_walk G x x 1).mpr ⟨.nil,by simp⟩) c
  have hn : (∀ y ∈ G.neighborFinset x, u c y = false) ↔ ∀ y ∈ G.neighborFinset x, v c y = false := by
    apply forall_congr'; intro y
    by_cases hy : y ∈ G.neighborFinset x
    · rw [he y (roundBall_neighbor G ((G.mem_neighborFinset _ _).mp hy)) c]
    · simp [hy]
  simp only [offerSet,mem_filter,hx,hn]

/-- Both kinds of bad event at a vertex are determined by marks within
distance six. This is a statement about the joint law before any color
has been exposed. -/
public theorem bad_at_local (a ν p τ cap : ℝ) (x : V) :
    FiniteLaw.determinedBy (roundBall G x 6) (fun f : V → C → Bool => badAt d s a ν p τ cap x (fun c y => f y c)) := by
  classical
  intro f g hfg
  let u (c : C) (y : V) := f y c
  let v (c : C) (y : V) := g y c
  have he y (hy : y ∈ roundBall G x 6) (c : C) : u c y = v c y := congrFun (hfg y hy) c
  have htot : badTotal d s a ν p τ cap x u ↔ badTotal d s a ν p τ cap x v := by
    unfold badTotal
    rw [sum_congr rfl (fun c (_ : c ∈ L x) => kept_local d s a ν p τ cap x c (u c) (v c)
      (fun y hy => he y (roundBall_mono G x (by decide : 5 ≤ 6) hy) c))]
  have htest (c : C) (i : Option (Finset V)) (hi : i ∈ testIndices d x) :
      badTest d s a ν p τ cap x c i u ↔ badTest d s a ν p τ cap x c i v := by
    let T := testSet G x i
    have hb y (hy : y ∈ T) := roundBall_neighbor G ((G.mem_neighborFinset _ _).mp (indexed_test_subset d x i hi hy))
    have near y (hy : y ∈ T) z (hz : z ∈ roundBall G y 5) (e : C) := he z (roundBall_comp G (hb y hy) hz) e
    have hpre y (hy : y ∈ T) := pre_local d s p cap y c (u c) (v c) (fun z hz => near y hy z
      (roundBall_mono G y (by decide : 4 ≤ 5) hz) c)
    have hrem y (hy : y ∈ T) : remainingWeight (G := G) (fun z e => keptWeight d s a ν p τ cap e (u e) z) u c y =
        remainingWeight (G := G) (fun z e => keptWeight d s a ν p τ cap e (v e) z) v c y := by
      have hnil := no_offer_local (G := G) y u v (fun z hz => near y hy z (roundBall_mono G y (by decide : 1 ≤ 5) hz))
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
end Vu
