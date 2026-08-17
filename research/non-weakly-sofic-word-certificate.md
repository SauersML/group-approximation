---
rg: 2
id: non-weakly-sofic-word-certificate
kind: claim
title: An explicit free-group tuple whose conjugacy product escapes its own normal closure profinitely
distinct_from:
  glebsky-rivera-w-sofic-criterion: that is the established equivalence between weak soficity of `F/N` and closure containment; this is the open assertion that the containment actually fails for some tuple, which is what the equivalence converts into an example
  non-weakly-sofic-group: that is the existence statement about groups; this is the finite-word certificate that produces it, and the two are equivalent only through the criterion, so they are kept apart to keep the certificate's shape visible
  hyperlinear-nonsofic-group: that separates hyperlinearity from soficity by exhibiting a group; this asks for a failure of the weakest metric approximation property of all, and no group in that node's family can serve, since Kun--Thom's wreath products are weakly sofic
  bespoke-routing-lemma: that is this program's gate on inventing a routing lemma to order; this is an externally posed open problem with a fixed published shape, not a lemma this program gets to design
  non-hyperlinear-group: that is this program's root target, a group with no normalized-Hilbert--Schmidt microstates, and it asks for a group; this asks for a tuple of words in a free group satisfying a profinite-closure condition, and it bears on the finite-group side, where hyperlinearity says nothing
  weakly-sofic-not-sofic: that is established and exhibits a group inside the weakly sofic class; this is open and asks for the word data that would put a group outside it, so the two point in opposite directions across the same class boundary
  torsion-free-countable-non-mf: that asks for a countable group with an algebraic side condition failing operator-norm matrix approximation; this asks for free-group words whose conjugacy product escapes profinitely, imposes no torsion or countability condition, and concerns finite groups with bi-invariant metrics rather than matrices
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
---

There exist a finite rank `r`, a free group `F = F(s_1,...,s_r)`, and reduced
words `g_1,...,g_k, x in F` such that

```text
(1)  x  not-in  N(g_1,...,g_k)        the normal closure of the g_i in F
(2)  q(x)  in  [q(g_1)]^Q ... [q(g_k)]^Q
                for EVERY homomorphism q : F -> Q with Q finite.
```

This is Glebsky--Rivera Conjecture 2.1, and by their Corollary 4.6 it is
equivalent to `non-weakly-sofic-group`.  **OPEN.**

## What makes it hard, stated precisely

Condition (2) is not "`q(x)` lies in the normal closure of the `q(g_i)`".
That weaker statement is cheap — it holds for any `x in N(g_1,...,g_k)`, and
it holds for the marked word of this repository's non-MF group `E` by
`unsquared-defect-finite-model-invisible`.  What (2) demands is that the
**number and ordered list of conjugacy factors is fixed once and for all**,
while only the finite group `Q` and the conjugators inside it may vary.

Glebsky--Rivera Remark 4.8 makes the difficulty exact: in the profinite
completion `Fhat`, with
`S = [g_1]^Fhat[g_1^(-1)]^Fhat...[g_k]^Fhat[g_k^(-1)]^Fhat`, one has
`Nhat(g_1,...,g_k) = union_n S^n`, and since `S` is compact this union is
closed **iff** it equals `S^n` for some `n`.  So closedness and bounded
conjugacy width are literally the same condition, and no compactness argument
can promote a quotient-dependent width `m(Q)` to a uniform `k`.

## The best known near-miss, and exactly what it is missing

Howie, *The p-adic topology on a free group: A counterexample*, Math. Z.
**187** (1984), 25--27, quoted in Section 2 of the Glebsky--Rivera paper,
gives in `F = <x,y>`:

```text
g_1 = x^(-2) y^(-3),      g_2 = x^(-2) (xy)^5,      a = xy^2
```

with

```text
a  not-in  N(g_1,g_2)                                     -- condition (1) HOLDS
a  =  w_i^(-1) g_1 w_i v_i^(-1) g_2 v_i   mod F_i         -- for every i,
                                                             F_0 = F, F_(i+1) = [F_i,F_i]
```

so for **every homomorphism to a nilpotent group** — in particular to every
finite `p`-group, since `phi(F_i) = {e}` for some `i` — one gets
`phi(a) in [phi(g_1)]^Q [phi(g_2)]^Q`.  This is condition (2) with `k = 2`
and rank `2`, verified on the whole pro-`p` side.

**What is missing is condition (2) for non-nilpotent finite quotients**,
where the derived-series argument is unavailable.  Glebsky--Rivera say only
"the same statement may be valid for the profinite topology" and suggest
Liebeck--Shalev diameters of finite simple groups and Nikolov--Segal I/II as
the tools.

So the frontier here is not "find a tuple".  A candidate tuple with `k=2` in
rank `2` has been on the table since 1984.  The frontier is a finite-group
theorem: a uniform bounded-width statement covering alternating groups,
groups of Lie type and arbitrary extensions.

## Search discipline

A search that verifies, for each tested finite `Q`, that `q(x)` lies in the
normal closure of the `q(g_i)` is measuring `m(Q)` and testing nothing.  The
factor count must be pinned before the quotient is chosen; the conjugators
found should be inspected for a uniform commutator identity or transfer
formula rather than tabulated.  Failure in a single finite quotient kills a
tuple outright, so the test is cheap in the negative direction and worthless
in the positive one — no bounded-order verification can discharge a universal
quantifier over all finite groups.
