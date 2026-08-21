---
rg: 2
id: free-cone-shift-finitely-wordizes-recursive-clifford-tails
kind: claim
title: One free-cone shift relator finitely wordizes every recursive Clifford tail
distinct_from:
  recursive-clifford-tail-supplies-anchor-but-not-contraction: that constructs the infinite subtree operators semantically and leaves their finite wordization open; this puts every tail and local controlled-Z gate in one four-generator finite presentation.
  thompson-clifford-central-product-tape: that finitely presents finite-support Pauli lamps and their common central sign on a Thompson orbit; this adds one genuinely infinite-support cone gate and needs neither a Thompson presentation nor a central-product kernel.
  toeplitz-tail-plus-one-swap-generates: that uses a one-ended algebraic shift and a finite head actuator to generate a coefficient ring; this uses the two positive cones in a free group and compiles the binary tail recursion directly as one ordinary group relator.
  nekrashevych-clifford-sign-tape: that obtains finite syntax from a contracted finite-state kernel and cylinder transport; this uses an external free shift, so the persistent tail state need not be a contracting automaton state.
---

**ESTABLISHED FINITE SYNTAX AND EXACT COMPLETENESS.**  Let

```text
G_cone=<t,c,s_0,s_1 |
          t^2=c^2=1,
          [s_0 t s_0^(-1),s_1 t s_1^(-1)]=1,
          t=c(s_0 t s_0^(-1))(s_1 t s_1^(-1))>.       (FCS1)
```

For a binary address `x=x_1...x_n`, put

```text
g_x=s_(x_1)...s_(x_n),
T_x=g_x t g_x^(-1),       C_x=g_x c g_x^(-1).         (FCS2)
```

Conjugating the two non-power relators in `(FCS1)` by `g_x` gives

```text
[T_(x0),T_(x1)]=1,
T_x=C_x T_(x0)T_(x1),
T_x T_(x0)T_(x1)=C_x.                                  (FCS3)
```

Thus every addressed recursion and identity-outer anchor is a conjugate of
one fixed relator.  Its boundary word has length `O(|x|)` and its relative
derivation area is one.  In particular the formerly semantic tail `T_x`
is now an ordinary word of length `2|x|+1`; no infinite relator list or
presentation depending on the depth is used.

The presentation has an exact nontrivial restricted-tensor representation.
Let `F=<s_0,s_1>` be the free group, let `P` be its positive binary monoid,
and attach a two-qubit space `(C^4,|00>)` to every `h in F`.  On the
incomplete tensor product, let `D_h` be controlled-Z at site `h`, let the
two shifts permute sites by left multiplication, and set

```text
rho(c)=D_e,                  rho(t)=product_(h in P) D_h. (FCS4)
```

The product is well-defined because controlled-Z fixes `|00>` and every
elementary tensor has finite excitation support.  The disjoint partition

```text
P={e} disjointUnion s_0 P disjointUnion s_1 P            (FCS5)
```

proves every relation in `(FCS1)`.  Moreover `rho(T_x)` is exactly the
controlled-Z product on the cone `g_x P`, and `rho(C_x)=D_(g_x)`.  Both
`rho(c)` and `rho(t)` are nonidentity.  This is the exact tail model of
`recursive-clifford-tail-supplies-anchor-but-not-contraction`, now factored
through a fixed finitely presented ordinary group.

This closes only the recursive-tail wordization seam.  The presentation
forces sibling tail commutation, which is all that `(FCS3)` uses; it does
not claim that arbitrary incomparable descendant words commute in every
representation.  Nor does it wordize the aggregate Schur child reflection
or prove the payload-dependent exposure estimate.  Those remain the two
interfaces needed by `tail-wordized-child-surplus-collision-supplies-rct7`.

