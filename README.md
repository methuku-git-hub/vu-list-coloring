# A proof of Vu’s conjecture

This repository contains a Lean 4 and Mathlib formalization of Theorem 1.1 of *A proof of Vu’s conjecture*, by Abhishek Methuku. The main declaration is `Vu.main_result_real`. The development also proves `Vu.main_result` for integer degree bounds.

## Abstract

In 2002, Vu conjectured that, for every fixed $\zeta>0$, every graph of maximum degree $\Delta$ in which any two distinct vertices have at most $\zeta\Delta$ common neighbors can be properly colored from arbitrary lists of $(\zeta+o(1))\Delta$ colors per vertex. In this paper we prove Vu’s conjecture.

## The mathematical statement

**Theorem 1.1.** For every $\zeta,\varepsilon>0$ there exists $\Delta_0$ such that the following holds for all $\Delta\ge\Delta_0$. If $G$ is a finite simple graph with maximum degree at most $\Delta$ and maximum codegree at most $\zeta\Delta$, then

$$
\chi_\ell(G)\le (\zeta+\varepsilon)\Delta.
$$

The codegree of two distinct vertices is the number of their common neighbors. The hypothesis applies to every distinct pair. The threshold depends only on $\zeta$ and $\varepsilon$.

### Exact Lean statement

The real-degree statement in [Challenge.lean](Challenge.lean) and [Solution.lean](Solution.lean) has this type.

```lean
∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
  ∃ D₀ : ℕ, ∀ D : ℝ, (D₀ : ℝ) ≤ D →
  ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
  (∀ v, (G.degree v : ℝ) ≤ D) →
  (∀ x y : V, x ≠ y → (Fintype.card (G.commonNeighbors x y) : ℝ) ≤ ζ * D) →
  ∀ L : V → Finset C, (∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) →
  ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y
```

Each vertex has its own finite list of colors from the arbitrary palette `C`. The conclusion supplies a choice from each list and proves that adjacent vertices receive different colors. The floor expresses the real upper bound because the list chromatic number is an integer.

### Proof entry point

[Solution.lean](Solution.lean) proves the two declarations. [Challenge.lean](Challenge.lean) states the targets independently and uses intentional placeholders for Comparator. The proof imports [Vu/DegreeFloor.lean](Vu/DegreeFloor.lean) and [Vu/RevisedStructure.lean](Vu/RevisedStructure.lean).

The structure theorem builds families of neighbor sets and a symmetric matrix of coefficients using regular refinement and the codegree bound. [Vu/RevisedRound.lean](Vu/RevisedRound.lean) proves the estimate for a round of partial coloring with independent activations for vertex–color pairs. [Vu/RevisedReduction.lean](Vu/RevisedReduction.lean) iterates the round and completes the coloring. The argument gives a stronger bound using the actual maximum codegree. That form allows the degree bound to be rounded down when $\Delta$ is real. The [proof dependencies](evidence/proof-route.json) identify the declarations used by both final proofs.

## Building

The project uses Lean `v4.35.0-rc2` and the Mathlib revision pinned in [lake-manifest.json](lake-manifest.json). With Git and [Elan](https://github.com/leanprover/elan) installed, run the following commands.

```sh
git clone https://github.com/methuku-git-hub/vu-list-coloring.git
cd vu-list-coloring
lake exe cache get
lake build
lake env lean Audit.lean
```

The cache command is optional. It downloads available Mathlib build artifacts.

## Verification

Palomar registered this formalization on 27 November 2026 as [PALOMAR-2026-11-27-000050, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000050&version=1).

The two proofs depend only on `propext`, `Classical.choice`, and `Quot.sound`. The [local Comparator transcript](evidence/comparator.log) records acceptance by Lean’s kernel, NanoDa, and Con-Ron. The [axiom audit](evidence/axioms.txt) and [proof dependencies](evidence/proof-route.json) record the checks for the two declarations. The [Comparator configuration](comparator.json) specifies the statements and permitted axioms.

## Sources and attribution

The mathematical source is Theorem 1.1 of *A proof of Vu’s conjecture* by Abhishek Methuku. Sections 3–7 of the revised manuscript supply the proof. Its SHA-256 digest is `da3e9ecaa6fea8f9d7ba3cd64dd68cfc49e72e39ccc6b1f9eed7373a9633d968`. Abhishek Methuku supplied the mathematical proof and directed the formalization. OpenAI Codex wrote and checked the Lean development. [Project metadata](formalization.yaml) gives the scope and provenance.

## License and further reading

The Lean development is distributed under the [Apache License 2.0](LICENSE).

- Van H. Vu, *A General Upper Bound on the List Chromatic Number of Locally Sparse Graphs*, Section 3, Open Question 1. [Article](https://doi.org/10.1017/S0963548301004898)
- Tom Kelly, Daniela Kühn, and Deryk Osthus, *A special case of Vu’s conjecture: colouring nearly disjoint graphs of bounded maximum degree*. [arXiv](https://arxiv.org/abs/2109.11438)
