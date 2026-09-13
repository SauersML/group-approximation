---
rg: 2
id: stw29-counterexample-level-two-fingerprint-proof
kind: route
title: Take the least infinite multiple of a finite projection, split the unit with OPR 4.3, and read off a separativity failure
target: stw29-counterexample-level-two-fingerprint
requires: [opr-properly-infinite-multiple-splits, ara-goodearl-tame-refinement-monoids-separative]
---

Throughout, `V(.)` is the Murray--von Neumann monoid, `<=` its algebraic order.
Two elementary facts are used repeatedly.

* (F1) If `x <= y` and `x` is infinite (`x = x + s`, `s != 0`), then `y` is
  infinite: `y = x + t = x + s + t = y + s`.
* (F2) In a simple conical monoid an infinite element `x = x + s` is properly
  infinite.  Iterating gives `x = x + m s` for every `m`, simplicity gives
  `x <= m s` for some `m`, so `2x <= x + m s = x`.  A properly infinite `x`
  satisfies `k x <= x` for all `k`; if moreover `x` is an order unit, then
  `z <= x` for every `z`.

**(1) implies (2).**  Let `A` be simple of real rank zero, neither stably
finite nor purely infinite.  Real rank zero gives a nonzero projection in every
nonzero hereditary subalgebra.  If all nonzero projections of `A` were infinite,
every nonzero hereditary subalgebra would contain an infinite projection and
`A` would be purely infinite.  So `A` has a nonzero finite projection `q`.
Some matrix projection `p` is infinite.  By simplicity `[p] <= l[q]` for some
`l`, so `l[q]` is infinite by (F1).  Let `n >= 2` be least with `n[q]` infinite.
Put `C = M_(n-1)(qAq)`, the corner of `M_(n-1)(A)` cut down by
`q direct_sum ... direct_sum q`.  It is unital and simple, and has real rank
zero (Brown--Pedersen: real rank zero passes to hereditary subalgebras and
matrix algebras).  Its unit has class `(n-1)[q]`, which is finite, so `C` is
finite.  The unit of `M_2(C)` has class `(2n-2)[q] >= n[q]`, which is infinite
by (F1).

**(2) implies (1).**  `C` is simple of real rank zero and not stably finite.
It is not purely infinite, because `1_C` is a nonzero finite projection.

**(2) iff (3).**  Given `C`, choose a separable sub-C\*-algebra containing
`1_C` and the entries of a non-unitary isometry of `M_2(C)`, and enlarge it by
Blackadar's separable inheritance to a separable simple real-rank-zero `C_1`.
`C_1` is finite since it shares the unit of `C`, and `M_2(C_1)` contains the
isometry.  The converse is trivial.

**(a).**  `V(C)` is a conical refinement monoid (real rank zero), and
`u = [1_C]` is an order unit.  Since `2u` is infinite, it is properly infinite
by (F2), so `M_2(C)` is properly infinite.  By
`opr-properly-infinite-multiple-splits` (OPR Theorem 4.3 with `n = 2`) write
`u = s_1 + t_1` with order units `s_1, t_1` and `2s_1`, `2t_1` properly infinite.
Realize this as `1_C = f_1 + e_1` with orthogonal projections, `[f_1] = s_1`,
`[e_1] = t_1`.  Apply Theorem 4.3 to `s_1`, which is again an order unit with
`2 s_1` properly infinite: `f_1 = f_2 + e_2`, and so on.  The `e_i` are nonzero
and mutually orthogonal, and every `2[e_i]` is a properly infinite order unit.
By (F2), `2u <= 2[e_i]`.

**(b).**  `M_2(C)` is properly infinite by (a).  Rordam (Acta 2003, proof of
Corollary 7.2): "No properly infinite C\*-algebra can admit a non-zero trace
(or a quasitrace), so M_n(A), and hence A, do not admit a tracial state (nor a
non-zero quasitrace)."  An infinite simple C\*-algebra has infinite stable rank
(Rordam 2005, page 2), so `tsr(M_2(C)) = infinity`.  Rieffel's matrix formula
`tsr(M_n(B)) = ceil((tsr(B) - 1)/n) + 1` (Proc. London Math. Soc. 1983) then
forces `tsr(C) = infinity`.

**(c).**  Proper infiniteness gives `4u <= 2u`, i.e. `2u = 4u + w`.  With
`r = 2u + w`,

```text
2u + r = 4u + w = 2u,
x + y = 2u + r = 2u = 2x,
2y = 2u + 2r = (2u + r) + r = 2u + r = 2u.
```

If `x = y`, then `u = u + r`.  Here `r != 0` (conicality, `u != 0`), so `u`
would be infinite, contradicting finiteness of `C`.  So `V(C)` violates
separativity (`2x = 2y = x + y` implies `x = y`).  Tame refinement monoids are
separative (Ara--Goodearl Theorem 2.3), so `V(C)` is wild.  Realize `y` by a
projection `g` in some `M_k(C)`.  Then `1_C direct_sum 1_C` and
`g direct_sum 1_C` have the same class `2u`, both `1_C` and `g` are full
(simplicity), and `1_C` is not equivalent to `g`.  This is a failure of weak
cancellation.

**(d).**  C\*-algebras of real rank zero are exchange rings, and for them the
monoid of finitely generated projective modules is `V(C)` (Ara--Goodearl--
O'Meara--Pardo, Israel J. Math. 105 (1998), as recalled on page 1 of
Ara--Goodearl arXiv:1405.7582).  By (c) this exchange ring is not separative.
The separativity problem for exchange rings, posed by Ara--Goodearl--O'Meara--
Pardo, is still open (reformulated in Ara--Goodearl--Nielsen--Pardo--Perera,
arXiv:2403.11837, 2024, whose abstract describes the problem as unsolved).

Finally `C` is a full corner of `A tensor K`, so `V(C) = V(A)`.
