---
rg: 2
id: finite-mark-centralizer-commutator-area-is-proper
kind: claim
title: Commutator filling area is proper on the centralizer of a finite mark
artifacts:
  - research/artifacts/finite-mark-centralizer-twisted-schreier-area-2026-08-21.md
distinct_from:
  cyclic-centralizer-slow-twist-has-linear-filling-area: that gives a sharp linear lower bound for a family of long words representing the same centralizer element, using explicit matrices; this is presentation-independent and forces divergence as the centralizer elements themselves escape modulo the finite marked subgroup.
  houghton-carmichael-sections-have-unbounded-edge-area: that uses hyperlinearity of one amenable family to force some Carmichael edge areas to diverge; this is a purely combinatorial local-coefficient theorem applying to every finitely presented group and every finite-order mark.
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that rules out one-cell templates by axes in the ambient free group; this permits arbitrary interacting van Kampen cells and detects them with a twisted Schreier-chain norm.
---

Let `G=<X|R>` be a finite presentation, let `b in G` have finite order
`m>=2`, and fix a word `beta` representing `b`.  Put `K=<b>`.  There are
constants `A>0` and `B>=0`, depending only on the presentation, `m`, and
`beta`, such that every `h in C_G(b)` and every word `eta` representing `h`
satisfy

```text
Area_R([beta,eta]) >= A d_(K\G)(K,Kh)-B.                 (FMC1)
```

Here the distance is in the right Schreier graph for the image of `X`.
Consequently the function

```text
h |-> Area_R([beta,eta_h])
```

is proper on every section of `C_G(b)/K`, uniformly over all choices of word
representatives `eta_h`.

Choose a prime `p|m`, map `K` onto `C_p`, and take the direct sum of all
`p-1` Galois-conjugate nontrivial characters.  In the corresponding twisted
Schreier graph, the two copies of the `eta` path in the commutator carry
coefficients differing by the diagonal action of `b`.  Reduction modulo
`(1-zeta_p)` turns the path chain into the ordinary `F_p` path chain, so its
support contains a path from `K` to `Kh`.  The Galois `ell^1` norm of the
commutator chain is therefore at least

```text
a_p d_(K\G)(K,Kh)-2(p-1)|beta|,                          (FMC2)
```

where `a_p=2 sin(pi/p)`.  Every translated defining-relator cell has twisted
boundary norm at most `(p-1)ell`, for
`ell=max_(r in R)|r|`.  One may therefore take

```text
A=a_p/((p-1)ell),
B=2|beta|/ell.
```

This lower bound already includes diagrams which leave the centralizer and
use arbitrary ambient relators.  It is therefore a coefficient-cocycle
area-undistortion theorem, not a corridor assertion inside a chosen
centralizer presentation.

There is also an averaged form.  Let `h_1,...,h_M in C_G(b)` represent
distinct cosets modulo `K`, and let `eta_(ij)` be arbitrary words representing
`h_i^(-1)h_j`.  If `B_R` is the size of the radius-`R` ball about `K` in the
Schreier graph, then at most `M B_R` ordered pairs have distance at most `R`.
Consequently, whenever `M>=2B_R+1`,

```text
1/(M(M-1)) sum_(i!=j) Area_R([beta,eta_(ij)])
  >= A R/2-B.                                             (FMC3)
```

In particular the average area over a growing distinct packet tends to
infinity.  Thus neither uniformly bounded individual certificates nor
bounded-average families of individual certificates can compile a complete
Carmichael packet.
