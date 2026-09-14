---
rg: 2
id: leavitt-unit-certificate-predicates-are-decidable
kind: claim
title: Direct-finiteness, surjunctivity and Kervaire--Laudenbach certificates over the Leavitt unit group are decidable and complete
distinct_from:
  binary-leavitt-unit-word-problem-decidable: that decides equality of words in R^x; this decides whether finite data certify a counterexample to direct finiteness, surjunctivity or Kervaire--Laudenbach over R^x, and proves each certificate type complete for its counterexample.
artifacts:
  - research/artifacts/leavitt-unit-certificate-checker-2026-09-11.md
  - experiments/nonsofic-certificates/README.md
  - experiments/nonsofic-certificates/certcheck.py
---

Let `G = R^x`, `R = L_(F_2)(1,2)`, with elements given as finite words in explicit units.
Each of the following predicates of finite data is decidable.

* **(DF)** For finite `alpha, beta in F_2[G]`: whether `alpha beta = 1` and `beta alpha != 1`.
  Likewise, for `d x d` matrices over `F_2[G]`: whether `AB = I != BA`.
* **(CA)** For a finite alphabet `A`, automata `tau` and `sigma` on `A^G` (finite memory sets
  of units, local rule tables) and a pattern `q in A^Omega` on a finite set `Omega`: whether
  `sigma o tau = id` and `q` has no `tau`-preimage.
* **(KL)** For units `c`, a one-variable word `w in G * <x>`, and finitely many conjugators
  `h_j` with exponents `e_j`: whether `c != 1`, the exponent sum `eps(w)` is nonzero, and
  `c = prod_j h_j w^(e_j) h_j^(-1)` in `G * <x>`.

Each certificate type is **complete** for its counterexample.

* `F_2[G]` is not directly finite iff a DF certificate exists; this is the definition.
* `G` is not surjunctive iff some CA certificate exists. An injective automaton
  `tau : A^G -> A^G` is a homeomorphism onto its closed invariant image `X`. The inverse
  `X -> A^G` is continuous and equivariant, so each coordinate reads a finite window. Extend
  that local rule arbitrarily off the language of `X` to get `sigma` with `sigma o tau = id`.
  If `tau` is not surjective, the open complement of `X` contains a cylinder, and the finite
  pattern defining that cylinder has no preimage. The converse is immediate.
* A Kervaire--Laudenbach violation over `G` exists iff some KL certificate exists. `w` is
  solvable in some overgroup of `G` iff `G -> (G * <x>)/<<w>>` is injective. Non-injectivity
  means some `c != 1` in `G` lies in `<<w>>`, that is, `c` is a finite product of conjugates
  of `w^(+-1)`.

So each of `leavitt-unit-group-algebra-not-directly-finite`,
`leavitt-unit-group-nonsurjunctive` and `kl-violating-equation-over-leavitt-unit-group` is a
`Sigma^0_1` statement. A search can confirm it; no finite search can refute it.

The decision procedures are implemented in `experiments/nonsofic-certificates/`, and
`certcheck.py` reads JSON certificates in these formats. A certificate that passes it is
the finite object a proof route into those claims should cite, with this claim as a
requirement.
