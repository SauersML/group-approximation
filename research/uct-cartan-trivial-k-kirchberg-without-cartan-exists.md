---
rg: 2
id: uct-cartan-trivial-k-kirchberg-without-cartan-exists
kind: claim
title: Some unital Kirchberg algebra with trivial K-theory has no Cartan subalgebra
distinct_from:
  nuclear-algebra-without-uct-exists: that is the root in its K-theoretic form; this is the Cartan-free certificate shape, equivalent to it through uct-cartan-trivial-k-kirchberg-uct-iff-cartan, which records which Cartan obstructions can and cannot apply.
  trivial-k-theory-kirchberg-algebras-are-o2: that is the positive isomorphism question; this is the negative certificate phrased through Cartan subalgebras.
  uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan: that is a type I algebra with no Cartan subalgebra which still satisfies the UCT; this asks for a Cartan-free algebra inside the simple purely infinite test class, where absence of a Cartan subalgebra is equivalent to failure of the UCT.
artifacts:
  - research/artifacts/uct-cartan-obstruction-2026-09-12.md
---

**OPEN.**  Is there a unital Kirchberg algebra `A` (separable, nuclear, simple,
purely infinite) with `K_0(A) = K_1(A) = 0` that has no Cartan subalgebra?  By
`uct-cartan-trivial-k-kirchberg-uct-iff-cartan` this is equivalent to
`nuclear-algebra-without-uct-exists`, and route
`nuclear-non-uct-via-cartan-free-trivial-k-kirchberg` feeds it there.

## Attempts

* **Topological fibre obstructions.**  The known Cartan-free nuclear algebras are
  homogeneous algebras whose `Aut(M_n)`-bundle does not reduce to
  `Aut(M_n, D_n)`; over `S^k` with `k ≥ 3` only the trivial one has a Cartan
  subalgebra (Li--Renault, arXiv:1703.10505, Proposition 2.2 and §2.2; examples
  of Gregson and Natsume; here
  `uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan`).  The
  obstruction lives in the centre and its fibre bundle.  A Kirchberg algebra is
  simple, so there is no bundle to obstruct.  Dies.
* **Von Neumann obstructions.**  Li--Renault show that a C\*-diagonal forces a
  Cartan subalgebra in `π_τ(A)''` for every trace `τ` (Corollary 4.6), and that
  `C*_λ(Γ)` has no Cartan subalgebra for torsion-free non-amenable groups with
  the CMAP and a proper 1-cocycle into a representation weakly contained in the
  regular one (Corollary 4.11).  Both need a trace, and a Kirchberg algebra has none;
  both need non-amenable rigidity, and every representation of a nuclear algebra
  generates an injective von Neumann algebra.  Injective factors with separable
  predual all come from amenable ergodic equivalence relations and so have Cartan
  subalgebras (Connes, Krieger; not re-read from source).  Dies.
* **Non-exact Kazhdan constructions of this repository.**  The block
  representation algebras carrying Ozawa's Kazhdan projection are not exact
  (`kazhdan-fd-block-representation-algebras-are-not-exact`), so any algebra
  containing them is not nuclear and cannot be a candidate.  Dies.
* **Existence methods.**  Cartan subalgebras of Kirchberg algebras are built from
  graph-type models (Katsura, Yeend, Spielberg) or inductive limits of Cartan
  pairs (Barlak--Li, X. Li), all realizing UCT invariants.  They say nothing about
  an algebra outside the UCT class.  What a certificate would need is a rigidity
  theorem saying that some invariant of twisted étale groupoid models cannot
  vanish for a given trivial-K Kirchberg algebra; no such invariant is known.
  Open.
