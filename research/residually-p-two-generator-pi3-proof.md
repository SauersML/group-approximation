---
rg: 2
id: residually-p-two-generator-pi3-proof
kind: route
title: Pro-p closure criterion via the lower central p-series of right-angled Artin groups, and p-adic rows
target: residually-p-two-generator-recursive-is-pi3-complete
requires:
  - shift-raag-family-is-rf-iff-symmetrized-index-set-closed
  - residual-finiteness-two-generator-recursive-is-pi3-complete
---

**Criterion.**  *Not closed implies not residually p.*  If
`d in cl_p(J^s) \ J^s`, then in any homomorphism `chi` to a finite
`p`-group the image of `t` has order `p^k` for some `k`, and `d = j + l p^k`
with `j in J^s`, so exactly as in [[shift-raag-family-rf-proof]]
`chi([a_0, a_d]) = chi([a_0, a_j]) = 1` while `[a_0, a_d] != 1`.

*Closed implies residually p.*  Given `g = n t^k != 1`: if `k != 0` use
`Z/p^s` with `p^s` not dividing `k`.  If `k = 0`, choose as in
[[shift-raag-family-rf-proof]] a modulus `m = p^s > 2r` such that every
non-edge difference `d` of the window satisfies `(d + p^s Z) n J^s`
empty (each has such a power by pro-p closedness; take the largest), and
map to `A(Gamma_{J,m}) x| Z/p^s`; `n` survives in `A(Gamma_{J,m})`.  A
finitely generated right-angled Artin group is residually torsion-free
nilpotent (Duchamp--Krob), hence residually a finite `p`-group; the terms
of its lower central `p`-series are characteristic, hence invariant under
the `Z/p^s` action, and the quotient by such a term is a finite `p`-group
extended by `Z/p^s`, again a finite `p`-group.  So the image of `g`
survives in a finite `p`-group.

**Upper bound.**  Residual `p`-finiteness is "for every word `w`, `w = 1`
or some finite `p`-group quotient separates `w`", and "the assignment
into the finite `p`-group `Q` kills every enumerated relator" is `Pi^0_1`,
so the matrix is `Sigma^0_2` and the whole is `Pi^0_3`.

**Hardness.**  Let row `x` be `{ p^x (p j + 1) : j < |W_g(e,x)| }` and
`J_e` the union of the rows, and let `D_x` be the set of integers of exact
`p`-adic valuation `x`, a clopen subset of `Z_p`, the sets `D_x` being
pairwise disjoint and covering `Z \ {0}`; `J_e^s n D_x = +-(row x)`.  If row `x` is infinite,
`j = p^k - 1` gives `p^x (p j + 1) = p^x (1 - p) + p^{x+1+k}`, so
`p^x (1 - p) in cl_p(J_e^s)`; it has valuation `x` and is congruent to
`p^x` modulo `p^{x+1}`, whereas `-(row x)` is congruent to `-p^x`, and
`2 p^x` is not divisible by `p^{x+1}` for odd `p` (for `p = 2` use the
rows `2^x (4 j + 1)` of [[rf-two-generator-pi3-proof]] verbatim); and
`p^x (p j + 1) = p^x (1 - p)` forces `j = -1`.  So the closure point is
outside `J_e^s`.  If all rows are finite, a closure point `i != 0` lies in
one clopen `D_x`, where the closure is that of the finite set `+-(row x)`,
so `i in J_e^s`.  Hence `G_{J_e}` is residually `p` iff every `W_g(e,x)`
is finite, a `Pi^0_3`-complete condition.
