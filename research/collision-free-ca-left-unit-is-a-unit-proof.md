---
rg: 2
id: collision-free-ca-left-unit-is-a-unit-proof
kind: route
title: Decode one independent memory block and force the encoder rule to be unary
target: collision-free-ca-left-unit-is-a-unit
requires: []
artifacts:
  - research/artifacts/gottschalk-nonlinear-ca-search-2026-08-24.md
  - research/artifacts/gottschalk-nonlinear-ca-search-2026-08-24.py
---

## Proof

Use the convention

    tau(x)(g)   = mu( (x(g s))_(s in S) ),
    sigma(y)(g) = nu( (y(g t))_(t in T) ).

Then `(sigma tau)(x)(1)` depends on the coordinates `x(t s)` for `(t,s)` in
`T x S`.  Since `sigma tau = id`, it must depend on `x(1)`, so `1` belongs to
`T S`.  Injectivity of the multiplication rectangle gives a unique
`(t0,s0)` with `t0 s0 = 1`.

Because all coordinates `t s` are distinct, a pattern on `T S` is exactly an
independent family of row-patterns `p_t in A^S`.  The identity equation says

    nu( (mu(p_t))_(t in T) ) = p_(t0)(s0)                    (* )

for every independent choice of the `p_t`.

Fix arbitrary row-patterns away from `t0`.  If two patterns `p,q in A^S`
have `p(s0) != q(s0)` but `mu(p)=mu(q)`, substituting `p` and `q` into the
`t0` row of (*) gives the same left side and two different right sides, a
contradiction.  Hence, for each `a in A`, the image

    I_a = { mu(p) : p(s0)=a }

is nonempty, and the `I_a` are pairwise disjoint subsets of `A`.  There are
`|A|` nonempty pairwise disjoint subsets of an alphabet of size `|A|`; each is
therefore a singleton, and their union is `A`.  Thus there is a permutation
`pi : A -> A` such that

    mu(p) = pi(p(s0))

for every `p`.  The global map is consequently

    tau(x)(g) = pi(x(g s0)),

which has the evident cellular-automaton inverse.  In particular `tau` is
surjective, so a strict embedding is impossible under the collision-free
hypothesis.
