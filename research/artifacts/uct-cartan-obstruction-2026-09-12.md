---
title: Cartan subalgebras and the UCT problem --- exact equivalences, type I counterexamples, and why no Cartan obstruction reaches a Kirchberg algebra (2026-09-12)
---

Lane `uct-cartan-obstruction`, swarm 6, 2026-09-12.  Root:
`nuclear-algebra-without-uct-exists`.  Sibling lane `uct-o2-cyclic-actions`
works the Barlak--Szabó `O_2 ⋊ Z_p` reduction; this lane takes Cartan
subalgebras directly.

# 1. Sources and what was read

All fetched from arXiv on MSI (`/scratch.global/sauer354/uct-cartan`).
`pdftotext` does not run on the MSI nodes (the `poppler/25.11.0` module needs a
newer `libstdc++`), so statements were read from the arXiv TeX sources.
Numbering was computed from each source's `\newtheorem` setup (one counter per
section shared by all statement types) and the order of environments.

* **Barlak--Li I**, arXiv:1511.02697.  Corollary 1.2 / its Section 3 restatement:
  "Let A be a separable and nuclear C\*-algebra.  If A has a Cartan subalgebra,
  then A satisfies the UCT."  Remark 3.3, verbatim: "Every UCT Kirchberg algebra
  has a Cartan subalgebra.  That follows from [Kat, Theorem C] and [Y1, Y2], see
  also [RSWY].  As every separable, nuclear C\*-algebra is KK-equivalent to a
  Kirchberg algebra by [Kir, Theorem I], we therefore conclude that the UCT
  problem has a positive answer if and only if every Kirchberg algebra admits a
  Cartan subalgebra."
* **X. Li**, arXiv:1802.01190.  Corollary 1.4, verbatim: "A unital separable
  simple C\*-algebra with finite nuclear dimension has a Cartan subalgebra if and
  only if it satisfies the UCT."  It follows Theorems 1.1 and 1.2 and Remark 1.3.
  The source adds that the unital restriction is only because stably
  projectionless classification was incomplete.
* **Li--Renault**, arXiv:1703.10505.
  * Lemma 2.1: a Cartan pair in an `n`-homogeneous algebra is locally trivial.
  * Proposition 2.2, verbatim: "An n-homogeneous C\*-algebra A has a Cartan
    subalgebra if and only if the principal Aut(M_n)-bundle of the M_n-bundle
    corresponding to A reduces to a principal Aut(M_n,D_n)-bundle."
  * §2.2, over spheres: over `S^2` every `n`-homogeneous algebra has a unique
    Cartan subalgebra up to equivalence; "over S^k, for k > 2, only the trivial
    n-homogeneous C\*-algebra C(S^k,M_n) has a Cartan subalgebra", which "gives a
    conceptual explanation for Gregson's and Natsume's examples of homogeneous
    C\*-algebras over spheres which do not admit Cartan subalgebras".
  * Corollary 4.6: if `B ⊆ A` is a C\*-diagonal and `τ` a trace on `A`, then
    `π_τ(A)''` has a Cartan subalgebra.
  * Corollary 4.7: `C*_r(Γ)` has no C\*-diagonal for `Γ` with property (HH)⁺ or
    icc hyperbolic.
  * Corollary 4.11: for torsion-free non-amenable `Γ` with the CMAP and a proper
    1-cocycle into an orthogonal representation weakly contained in the regular
    one, `C*_λ(Γ)` has no Cartan subalgebra; in particular `C*_λ(F_r)`, `r ≥ 2`.

# 2. Answers

**(a) Is "every separable nuclear algebra has a Cartan subalgebra" equivalent to
the UCT?**  No.  It is false: nontrivial homogeneous algebras over `S^k`, `k > 2`,
are separable, type I, nuclear and UCT, and have no Cartan subalgebra
(Li--Renault §2.2).  Node `uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan`
records the case `n = 2`, `k = 4`.  It strengthens the conclusion to "no masa is
the range of a conditional expectation" and notes that the stabilization
`A ⊗ K ≅ C(S^4) ⊗ K` does have a Cartan subalgebra.

**(b) Up to KK-equivalence.**  This form has no content.  A separable algebra
satisfies the UCT iff it is KK-equivalent to a commutative C\*-algebra
(`uct-class-permanence-properties`, item 1), and a commutative algebra is a
Cartan subalgebra of itself.  So "KK-equivalent to a nuclear algebra with a
Cartan subalgebra" is literally the UCT.  No node is landed for it.

**(c) Up to stable isomorphism.**  One direction is clear: a stable isomorphism
preserves the UCT, and Cartan implies UCT.  Whether every separable nuclear UCT
algebra is stably isomorphic to one with a Cartan subalgebra was not decided.
The type I example only shows the stable form is strictly weaker than the
literal one.  Recorded here, not as a node.

**(d) The exact Cartan forms of the UCT problem.**
* Global: the UCT problem has a positive answer iff every Kirchberg algebra has
  a Cartan subalgebra (Barlak--Li Remark 3.3, imported in
  `barlak-li-cartan-subalgebras-force-uct`).
* Simple finite nuclear dimension: Cartan ⟺ UCT for each unital separable simple
  algebra (Li Corollary 1.4, new import
  `li-simple-finite-nuclear-dimension-cartan-iff-uct`).
* Test class, pointwise: for a unital Kirchberg algebra with trivial K-theory,
  UCT ⟺ `≅ O_2` ⟺ Cartan subalgebra (new derivation
  `uct-cartan-trivial-k-kirchberg-uct-iff-cartan`).  This makes a counterexample
  exactly a Cartan-free trivial-K Kirchberg algebra (open node
  `uct-cartan-trivial-k-kirchberg-without-cartan-exists`, route
  `nuclear-non-uct-via-cartan-free-trivial-k-kirchberg` into the root).

**(e) Can this repository's non-exact or Kazhdan constructions give nuclear
algebras with Cartan obstructions?**  No.  The block representation algebras
carrying Ozawa's Kazhdan projection are not exact
(`kazhdan-fd-block-representation-algebras-are-not-exact`), so nothing containing
them is nuclear.  The two known kinds of Cartan obstruction also cannot reach a
Kirchberg algebra:
* the topological one (Li--Renault §2) lives in a nontrivial centre;
* the von Neumann one (Li--Renault Corollaries 4.6 and 4.11) needs a trace and
  non-amenable rigidity of the generated von Neumann algebra.
A Kirchberg algebra is simple and traceless, and representations of nuclear
algebras generate injective von Neumann algebras.  Injective factors with
separable predual have Cartan subalgebras (Connes, Krieger); that last input was
not re-read from source.

**(f) Known nuclear algebras without Cartan subalgebras.**  In these sources: the
nontrivial homogeneous algebras over spheres of dimension at least 3 (Gregson,
Natsume, Li--Renault), all type I and UCT.  Among unital simple algebras of finite
nuclear dimension, any Cartan-free example would fail the UCT (Li
Corollary 1.4).  The Cartan-free reduced group C\*-algebras of Li--Renault §4 are
not nuclear.

# 3. The strengthened homogeneous obstruction

Proof in `uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan-proof`.  A masa
`B` with a conditional expectation `P` contains the centre `C(S^4)`, so `P`
descends to fibre expectations `M_2 → B_x`.
1. Maximality forces the set where `B_x` is a masa to be dense.
2. Uniqueness of expectations onto masas of `M_2`, plus continuity of `P(a)`,
   forces `B_x` to be a masa at every point and to vary continuously.
3. That is a line subbundle of the rank-3 adjoint bundle, which over `S^4` forces
   the `PU(2) ≅ SO(3)`-bundle to be trivial.

The argument uses only maximality and the expectation, never regularity.  This is
the `n = 2`, `k = 4` case of Li--Renault's reduction to `Aut(M_n, D_n)`, with the
Cartan hypothesis weakened.

# 4. What remains open

* A Cartan-free unital trivial-K Kirchberg algebra, equivalently a UCT
  counterexample.  No known obstruction applies (Section 2(e)).
* Whether every separable nuclear UCT algebra is stably isomorphic to one with a
  Cartan subalgebra (Section 2(c)).
