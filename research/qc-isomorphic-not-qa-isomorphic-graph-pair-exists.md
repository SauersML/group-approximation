---
rg: 2
id: qc-isomorphic-not-qa-isomorphic-graph-pair-exists
kind: claim
title: Some pair of finite graphs is quantum commuting isomorphic but not quantum approximately isomorphic
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
distinct_from:
  perfect-qc-separation-yields-finite-bcs-with-no-matrix-model: that extracts an independent-set game with a qc/q gap from Lin's theorem, whose algebra has no canonical trace; this asks for the qc/qa gap in graph isomorphism syntax, where a nonzero algebra is a bigalois extension with a unique invariant trace.
  bisynchronous-to-monomial-game-algebra-compiler: that asks to realize the fixed non-CE game algebra as a finite-phase monomial linking algebra; this asks for any qc-but-not-qa pair of plain graphs, with no prescribed algebra.
  mipstar-bcs-tracial-nonru-exists: that is the gap for a general constraint system, which MIP*=RE supplies; this is the gap for isomorphism games, whose algebraic, C* and tracial levels collapse.
---

**OPEN.**  Find finite simple graphs `X, Y` whose isomorphism game has a
perfect `qc`-strategy but no perfect `qa`-strategy.  Equivalently
(BCEHPSW, arXiv:1812.11474v2, Theorems 2.1 and 4.9):

```text
A(Iso(X,Y)) != 0,   and   no unital *-homomorphism A(Iso(X,Y)) -> R^U.
```

**Consequence.**  By `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group`
such a pair gives a finite graph whose quantum automorphism group has
non-Connes-embeddable Haar von Neumann algebra.

**Relation to the goal.**  A finitely presented nonhyperlinear group gives
such a pair through the linear-system graphs `(G_(A,b), G_(A,0))`
(`lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap`).  No converse is known for
general graphs.

## Attempts

- **CFI pairs from linear systems.**  For `(G_(A,b), G_(A,0))` the `qc`/`qa`
  gap is equivalent to the tracial/non-`R^U` gap of `Ax=b` (BCEHPSW
  Theorem 5.6 and Proposition 5.3), hence to a finitely presented
  nonhyperlinear group (Paddock--Slofstra Proposition 5.8).  This source dies
  at the goal itself.
- **Uniform gadget reductions from NP-hard languages.**
  - A hereditary *-equivalence of games preserves perfect classical strategies
    (BCEHPSW Proposition 5.3 with `t = loc`).
  - A polynomial-time family of such equivalences from 3SAT-type systems would
    reduce 3SAT to graph isomorphism.  Babai's quasipolynomial algorithm
    (arXiv:1512.03547, not re-read here) would then put NP in quasipolynomial
    time.
  - This blocks only uniform, classical-solution-preserving gadgets.  It does
    not block a single instance, or compilers that destroy classical
    solutions, as `MIP*=RE` compilers do.
- **Algebra-level equivalence with the fixed source.**  Equivalence with an
  isomorphism game transfers the collapse of algebraic, C* and tracial
  satisfiability.  So no source whose own levels differ can be used, for
  example Paddock--Slofstra Section 4 or `A(Hom(K_5,K_4))`.  Where it dies:
  the `MIP*=RE` separating algebra is not excluded by this, and no equivalence
  for it is known.
- **Closure-safe bisynchronous sources.**  By
  `closure-safe-support-is-exactly-the-colored-iso-rung`, a bisynchronous game
  with a perfect trace, no `R^U` model, and support closed under linking gives
  a colored-digraph pair of this kind.  Where it dies:
  - independent-set games (Lin via Mančinska--Spaas--Spirig--Vernooij) are
    automatically closure-safe but not square, so the missing step is
    completing a quantum injection to a quantum bijection;
  - no colored-to-plain reduction preserving both `qc` and `qa` is landed.
- **Recursion-theoretic compiler.**
  - `A(Iso(X,Y)) = 0` is recursively enumerable, so `qc`-isomorphism is coRE.
  - Suppose `M |-> (X_M, Y_M)` is computable, with halting machines giving
    `X_M ≅_q Y_M` and nonhalting machines giving `X_M not ≅_qa Y_M`.  Then
    the fixed point that searches for `1 = 0` in its own isomorphism algebra
    names a pair (artifact §4).
  - Where it dies: this is perfect completeness again.  The
    Pauli completeness strategies of `MIP*=RE` are linear-system strategies,
    and `jnvwy-active-output-has-no-affine-safe-perfect-model` shows that the
    unchanged verifier has no affine-safe perfect model.  Isomorphism syntax
    admits nonabelian local symmetry, but no compiler using it exists.
- **Nonabelian local symmetry of torsor type.**
  - Running CFI over a finite group `H` gives colored digraphs whose
    isomorphism algebras are `H`-valued coset constraint algebras.  Their
    quantum symmetry is not a group dual when a local coset group is
    nonabelian (`torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra`).
  - Where it dies as a compiler: port values of such gadgets are twists of one
    graph.  Composing quantum isomorphisms makes every realizable scalar port
    profile a coset, and an affine set on Boolean ports, at the `q`, `qa` and
    `qc` levels (`torsor-cfi-port-profiles-are-cosets`).  So atom-by-atom
    torsor gadgets meet the same affine firewall.
  - What survives: gadget families that are not twists, non-scalar ports, and
    a single coset-safe `H`-valued constraint system with a perfect trace and
    no `R^U` model.
