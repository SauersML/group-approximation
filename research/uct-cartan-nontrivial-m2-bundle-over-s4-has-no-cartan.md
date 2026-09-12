---
rg: 2
id: uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan
kind: claim
title: A nontrivial M_2-bundle algebra over S^4 is type I and UCT but has no Cartan subalgebra, while its stabilization has one
distinct_from:
  barlak-li-cartan-subalgebras-force-uct: that proves a nuclear algebra with a Cartan subalgebra satisfies the UCT; this shows the converse fails already for a separable unital type I algebra, so "has a Cartan subalgebra" is strictly stronger than the UCT.
  nuclear-algebra-without-uct-exists: that is the open negative answer to the UCT problem; this is an algebra that satisfies the UCT and still has no Cartan subalgebra, so absence of a Cartan subalgebra is not evidence against the UCT.
artifacts:
  - research/artifacts/uct-cartan-obstruction-2026-09-12.md
---

**ESTABLISHED (derivation, this repository).**  Let `E → S^4` be a locally
trivial bundle with fibre `M_2(C)` and structure group `Aut(M_2) = PU(2)`
whose clutching class in `π_3(PU(2)) ≅ Z` is nonzero, and let `A = Γ(S^4, E)`
be its algebra of continuous sections.  Then:

1. `A` is a separable unital type I C\*-algebra, so it is nuclear and satisfies
   the UCT (the bootstrap class contains every separable type I algebra,
   Rosenberg--Schochet).
2. No maximal abelian subalgebra `B ⊆ A` is the range of a conditional
   expectation `A → B`.  In particular `A` has no Cartan subalgebra.
3. `A ⊗ K ≅ C(S^4) ⊗ K`, and `C(S^4) ⊗ c_0` is a Cartan subalgebra of it.

Proof: `uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan-proof`.

**Consequences.**  Having a Cartan subalgebra is invariant neither under
stable isomorphism nor under KK-equivalence, and it is not implied by the UCT,
even for type I algebras.  So "every separable nuclear C\*-algebra has a Cartan
subalgebra" is false and cannot be a reformulation of the UCT problem.  An exact
Cartan reformulation has to restrict the class of algebras; the test class of
trivial-K-theory Kirchberg algebras works
(`uct-cartan-trivial-k-kirchberg-uct-iff-cartan`).  The obstruction in item 2 is
topological and needs a nontrivial centre, so it says nothing about simple
algebras.

**Credit.**  The absence of a Cartan subalgebra is known.  Li--Renault,
arXiv:1703.10505, Proposition 2.2, show that an `n`-homogeneous algebra has a
Cartan subalgebra iff its principal `Aut(M_n)`-bundle reduces to
`Aut(M_n, D_n)`, and their §2.2 computes that over `S^k` with `k > 2` only
`C(S^k, M_n)` has one; this explains earlier examples of Gregson and Natsume.
Read from the arXiv TeX source on MSI, 2026-09-12.  Derived here: the
strengthening in item 2 from Cartan subalgebras to masas carrying a conditional
expectation, by an elementary fibrewise argument, and item 3, which matches their
remark that `ℵ_0`-homogeneous algebras over `S^k`, `k ≠ 3`, are trivial.  No
novelty is claimed.  Rosenberg--Schochet and the Dixmier--Douady classification
are used as standard facts, without re-reading them from source.
