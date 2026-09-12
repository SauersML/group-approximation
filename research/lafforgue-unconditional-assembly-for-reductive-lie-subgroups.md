---
rg: 2
id: lafforgue-unconditional-assembly-for-reductive-lie-subgroups
kind: claim
title: Closed subgroups of reductive Lie groups have bijective assembly into the K-theory of every unconditional completion (Lafforgue)
distinct_from:
  hyperbolic-groups-have-property-rd: that is the rapid decay inequality for hyperbolic groups, the analytic input that moves assembly to the reduced C*-algebra; this is Lafforgue's Banach KK theorem for unconditional completions of closed subgroups of reductive Lie groups, which reaches the reduced algebra only when some unconditional completion is closed under holomorphic calculus.
  baum-connes-counterexample-group-exists: that asks for a group whose reduced assembly map fails to be bijective; this is the unconditional-completion assembly theorem, which holds for SL_3(Z) while reduced assembly stays open there.
  bost-fixed-two-generator-torsion-free-tester: that reduces the Bost conjecture with coefficients for all torsion-free groups to one universal host; this imports Lafforgue's theorem that unconditional-completion assembly, the Bost conjecture included, holds for closed subgroups of reductive Lie groups.
artifacts:
  - research/artifacts/kk-sl3z-congruence-2026-09-12.md
---

**ESTABLISHED (citation).** Let `G` be a closed subgroup of a reductive Lie group. Examples
are the discrete subgroups of `SL_n(R)`, such as `SL_3(Z)` and all of its subgroups. Let
`A(G)` be an unconditional completion of `C_c(G)`: a Banach algebra completion whose norm
`||f||_A` depends only on `|f|` and is monotone in it. Then

```text
mu_A : K_*^G(\underline{E}G) -> K_*(A(G))
```

is an isomorphism. If `A(G)` is an involutive subalgebra of `C*_r(G)`, with inclusion `i`,
then `mu_r = i_* ∘ mu_A`. With `A(G) = L^1(G)` this is the Bost conjecture for `G`.

**The consequence used in this graph.** For such `G`, and every unconditional completion
`A(G) ⊆ C*_r(G)`:
- the image of `mu_r` equals `i_*(K_*(A(G)))`;
- reduced assembly is surjective as soon as some such `A(G)` is dense and closed under
  holomorphic calculus, which is how rapid decay is used (Lafforgue's Corollary 1.6.3);
- for `SL_3(Z)` no such completion exists (`sl3z-has-no-spectral-unconditional-completion`).

**Sources.**
- **V. Lafforgue, ICM 2002 address**, *Banach KK-theory and the Baum–Connes conjecture*
  (arXiv:math/0304342), §1.5–1.6, read from the arXiv PDF on MSI.
  - Before Theorem 1.5.3: the classes a′) and c′) "respectively contain all closed
    subgroups of reductive Lie groups, and all hyperbolic groups".
  - Theorem 1.6.2: "For any group G in the classes a′), b) or c′), and for any
    unconditional completion A(G) of C_c(G), μ_A : K_*^G(EG) → K_*(A(G)) is an isomorphism."
  - Just before it: "If A(G) is an involutive subalgebra of C*_red(G), and
    i : A(G) → C*_red(G) denotes the inclusion, μ_red = i_* ∘ μ_A."
- **Gomez Aparicio–Julg–Valette** (arXiv:1905.10081), §6.1.2: "All real semisimple Lie
  groups and all p-adic reductive Lie groups as well as their closed subgroups ... belong to
  this class. For all these groups G and all G-algebras A the map μ^A_{B(G)} is an
  isomorphism and hence the Bost conjecture holds".
- **Primary source, not read:** V. Lafforgue, *K-théorie bivariante pour les algèbres de
  Banach et conjecture de Baum–Connes*, Invent. Math. 149 (2002) 1–95.

**Caveats.**
- The ICM text says after Theorem 1.5.3: "In fact the statement is slightly incorrect, we
  should allow representations with a slow growth, but this adds no real difficulty."
- Class a′) is described as slightly smaller than class a). Only its stated containment of
  closed subgroups of reductive Lie groups is imported.
