---
rg: 2
id: amenable-by-virtually-free-twisted-crossed-products-are-ce
kind: claim
title: Twisted crossed products of amenable-by-virtually-free groups are Connes embeddable, so ISW Theorem C charges no embeddability toll on either Sp4 parabolic
distinct_from:
  sp4-isw-theorem-c-embeddable-twist-data-exists: that asks for Theorem C data on the whole lattice Sp_4(Z), where the moreover clause needs Connes-embeddability of Maslov-twisted crossed products and is open; this proves that the same moreover clause is AUTOMATIC when the ambient group is a Siegel or Klingen parabolic (or any amenable-by-virtually-free group), for every action and every L^0-cocycle.
  sp4-small-maslov-twisted-group-factors-are-ce: that is the CE toll on Sp_4(Z) itself; this removes the toll on the parabolics, relocating the whole LLP-refutation question there to cohomology.
  amenable-edge-hnn-preserves-hyperlinearity: that uses the same Brown--Dykema--Jung permanence for HNN/amalgam groups; this applies it to cocycle-twisted crossed products L^infty(X) x|_{sigma,c} P with operator-valued 2-cocycles.
  sp2g-z-full-c-star-algebra-has-llp: this is a reduction lemma feeding the refutation side, not a decision of the root.
---

**ESTABLISHED.**  Let `P` be a countable group with an amenable normal subgroup
`N` such that `P/N` is virtually free (finitely generated).  Let
`sigma : P ~> (X,mu)` be a p.m.p. action on a standard probability space and
`c in Z^2(P, L^0(X,T))`.  Then

```text
L^infty(X) x|_{sigma,c} P  embeds (trace-preservingly) into R^omega.   (TCE1)
```

**Sp_4 consequence.**  Both maximal parabolics of `Sp_4(Z)` qualify:
`P_S = Sym_2(Z) x| GL_2(Z)` and `P_K = N_K x| ({+-1} x SL_2(Z))`, with
`GL_2(Z)` and `{+-1} x SL_2(Z)` virtually free.  So for `Gamma = P_S` or `P_K`
the moreover clause of Ioana--Spaas--Wiersma Theorem C (arXiv:2006.01874, p. 3:
"Moreover, if the twisted crossed product von Neumann algebra
`L^infty(X) x|_{sigma,c_n} Gamma` embeds into `R^omega`, for every `n`, then
`C^*(Gamma)` does not have the LLP") holds for free.  Any pair `(P,Lambda)`
with relative (T), an action with `sigma|Lambda` ergodic, and cocycles `c_n`
with `c_n|Lambda` not a coboundary and `||c_n(g,h)-1||_2 -> 0` would give
`C^*(P)` without LLP, hence `C^*(Sp_4(Z))` without LLP by subgroup permanence.
That would refute `sp2g-z-full-c-star-algebra-has-llp` with no Connes-embedding
input and no `F_2 x F_2` barrier.  The remaining cohomological question is
fenced in `sp4-parabolic-radical-theorem-c-data-dies`.

The route is `amenable-by-virtually-free-twisted-crossed-products-are-ce-proof`.
It gives a short averaging proof that `L^infty(X) x|_c N` is injective, then
decomposes along a lifted free subgroup into an amalgamated free product over
that injective algebra, and imports Brown--Dykema--Jung, arXiv:math/0609080,
Corollary 4.5 (verbatim in the route).
