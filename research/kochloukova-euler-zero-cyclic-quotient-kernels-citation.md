---
rg: 2
id: kochloukova-euler-zero-cyclic-quotient-kernels-citation
kind: route
title: Import Kochloukova's Theorem 3 on normal subgroups of Euler-characteristic-zero groups, with Stallings' freeness theorem
target: kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop
requires: []
artifacts:
  - research/artifacts/hl-fp-intermediate-growth-2026-09-14.md
---

Literature import.
- **Source.** D. H. Kochloukova, *Some Novikov rings that are von Neumann finite and knot-like
  groups*, Comment. Math. Helv. 81 (2006), 931–943.
- **Copy read.** Publisher PDF from EMS Press, read on 2026-09-14.
- **Pins.** Verbatim pins are in `research/artifacts/hl-fp-intermediate-growth-2026-09-14.md`.

- **Theorem 3** (p. 933): "Let $G$ be a non-trivial discrete group with a finite $K(G,1)$
  CW-complex $Y$ of dimension $n$ such that the Euler characteristics of $Y$ is zero. Suppose that
  $N$ is a normal subgroup of $G$ containing the commutator subgroup such that $N$ is of homological
  type FP$_{n-1}$ and $G/N$ is cyclic-by-finite. Then a) $N$ is of homological type FP$_n$; b) $G/N$
  has finite virtual cohomological dimension vcd$(G/N)$ = cd$(G)$ − cd$(N)$. In particular either $N$
  has finite index in $G$ or $N$ has cohomological dimension cd$(G)-1$."
- **Stallings**, as quoted on p. 934: "otherwise cd$(G) = 1$ and by the Stallings theorem $G$ is free
  [20]". Here [20] is J. R. Stallings, *On torsion-free groups with infinitely many ends*, Ann. of
  Math. (2) 88 (1968), 312–334.
- **Same use in the paper.** On the same page, the proof of Corollary 3 applies Theorem 3 in the form
  used below: "by Theorem 3 cd$(N)\le 1$, so $N$ is a free group, possibly trivial."
- **Scope.** The paper derives Theorem 3 from its Theorem 1 (von Neumann finiteness of matrix rings
  over Novikov rings) and from an earlier paper. This route imports the statement only.

**Derivation of the n = 2 consequence.**
1. A finitely generated group `N` with finite generating set `S` is of type `FP₁`.
   - The augmentation ideal of `Z[N]` is generated as a left `Z[N]`-module by `{s − 1 : s ∈ S}`.
     This uses `gh − 1 = g(h − 1) + (g − 1)` and `g⁻¹ − 1 = −g⁻¹(g − 1)`.
   - So `Z[N]^S → Z[N] → Z → 0` is exact with finitely generated free terms.
2. `N = ker φ` contains `[G,G]` because `Z` is abelian, and `G/N ≅ Z` is cyclic. `G` is non-trivial
   because it maps onto `Z`.
3. Apply Theorem 3 with `n = 2`.
   - `G/N` is infinite, so `N` has infinite index.
   - Hence `cd(N) = cd(G) − 1 ≤ 1`, since the finite 2-dimensional `K(G,1)` gives `cd(G) ≤ 2`.
4. If `cd(N) = 0`, then `N` is trivial. If `cd(N) = 1`, then `N` is finitely generated and free by
   Stallings' theorem.
