---
rg: 2
id: forbidden-character-kernel-quotient-compiler-proof
kind: route
title: Prove the forbidden-character kernel quotient compiler
target: forbidden-character-kernel-quotient-compiler
requires: []
---

Let `q:H->H/K` be the quotient map.  Group the terms in the character
idempotent by cosets of `K`:

```text
q(e_(H,chi))
 =1/|H| sum_(hK in H/K)
   overline(chi(h)) q(h) sum_(k in K) overline(chi(k)). (FKP1)
```

If `chi|K` is nontrivial, the last character sum is zero.  If it is trivial,
the sum is `|K|`, `chi` descends to a character `barchi` of `H/K`, and
`|H|=|K||H/K|`; `(FKP1)` becomes `e_(H/K,barchi)`.  This proves `(FKQ5)`.

Apply `(FKQ5)` to `K=N intersect H_i`.  Condition `(FKQ3)` makes the image
of every `e_i` zero in `C[barGamma]`.  The representation `theta` factors
through `barGamma` because `N<=ker(theta)`.  Its descended image sends `J`
to `-1`, so the image of `J` in `barGamma` is nontrivial.

Suppose `barGamma` were hyperlinear.  Its group von Neumann algebra with
canonical trace would admit a trace-preserving embedding into a tracial
matrix ultraproduct.  Since `J` is a nontrivial central involution,

```text
q_-=(1-J)/2                                             (FKP2)
```

is a nonzero central projection of canonical trace `1/2`.  The normalized
corner `q_- L(barGamma)` is again Connes embeddable.  The contextual group
generators commute with `q_-`; on this corner `J=-1`, all structural group
relations hold, and every forbidden local character projection is zero by
`(FKQ5)`.  The corner trace is therefore a Connes-embeddable perfect
contextual trace, contrary to the assumed contextual separation.  Thus
`barGamma` is nonhyperlinear.

Finally, every `N<=ker(theta)` satisfies

```text
N intersect H_i <= ker(theta) intersect H_i.          (FKP3)
```

If `chi_i` is trivial on the right side, no smaller `N` can separate it.  If
all restrictions in `(FKQ6)` are nontrivial, taking `N=ker(theta)` satisfies
`(FKQ3)`.  Alternatively take `(FKQ7)`.  Its normal closure lies in
`ker(theta)` and contains every `K_i`, so each forbidden `chi_i` remains
nontrivial on `N intersect H_i`.  The optimal local relation count is
`local-kernel-bases-optimally-annihilate-character-types`; this proves the
finite form and the finite-presentation clause.
