---
rg: 2
id: restricted-influence-transfer-degree-two-proof
kind: route
title: Cauchy--Schwarz over the restriction fibre, which is finite exactly below degree three
target: restricted-influence-transfer-holds-below-degree-three
requires: []
---

**The fibre.**  For `S subset Omega` let `pi_b(S)` be the set of `b`-cosets
meeting `S` oddly, so that `chi_S|_{D_b} = chi_{pi_b(S)}` in the quotient
coordinates `Y_{[c]}`.  A coset has exactly two elements, so
`|S intersect [c]| in {0,1,2}`: it is `1` on each coset of `T = pi_b(S)` and
`0` or `2` elsewhere.  Hence `(T2)`,

```text
|S| = |T| + 2m,     m = #{cosets contained in S},
```

and the fibre `{S : pi_b(S) = T}` is parametrised by a choice of one point
in each coset of `T` (`2^{|T|}` ways) together with a set of `m` further
cosets.  If `deg g <= 2` then `|S| <= 2`, and for `|T| >= 1` the identity
`|S| = |T| + 2m` forces `m = 0`; the fibre has exactly `2^{|T|}` elements.

**The inequality.**  Assume `deg g <= 2`.  For `T ∋ C` with `|T| = t <= d`,
Cauchy--Schwarz over the `2^t`-element fibre gives

```text
hat{g|_{D_b}}(T)^2 = ( sum_{pi_b(S)=T} hat g(S) )^2 <= 2^t * sum_{pi_b(S)=T} hat g(S)^2.
```

Summing over `T ∋ C` with `|T| <= d`, and noting that the fibres over
distinct `T` are disjoint and that `pi_b(S) ∋ C` says exactly that `S` meets
`C = {q, q+b}` oddly, i.e. contains exactly one of `q`, `q+b`:

```text
Inf^{<=d}_C(g|_{D_b}) <= 2^d * sum_{S : |S intersect C| = 1, |S| <= d} hat g(S)^2
                      <= 2^d * ( sum_{S ∋ q} hat g(S)^2 + sum_{S ∋ q+b} hat g(S)^2 )
                       = 2^d * ( Inf^{<=d}_q(g) + Inf^{<=d}_{q+b}(g) ),
```

which is `(T1)`.  (With `deg g <= 2` only `t <= 2` occurs, so the constant
is at worst `4`.)

**Failure at degree three, with the witness.**  Take `r = 1` in
`linear-pairing-memorizer-restricts-to-a-dictator`, so
`deg B_{b,1} = 3` and `M = N/2 - 1`.  Here `T = {C_b}` is a singleton and
the fibre `{S : pi_b(S) = {C_b}}` contains the `M` sets `{0} union {u, u+b}`
-- one absorbed coset each, allowed because `|S| = 1 + 2` is within degree
three.  The memorizer makes that fibre sum coherently: every term is `1/M`
and they add to `1`, so

```text
Inf_{C_b}( B_{b,1}|_{D_b} ) = 1,     Inf_0(B_{b,1}) = Inf_b(B_{b,1}) = 1/M = Theta(1/N).
```

`(T1)` would give `1 <= 2^d * Theta(1/N)`.  So the inequality is false at
degree three, and the failure is caused by exactly the term `(T2)` permits
for the first time.  Nothing between degrees two and three is missing: the
statement flips at the first degree that admits coset absorption.

**The decomposition (T3).**  Reading the fibre over a singleton `T = {C}`
for general `g`, the fibre elements are `{q} union R` and `{q+b} union R`
with `R` a union of `m >= 0` cosets disjoint from `C`, giving

```text
hat{g|_{D_b}}({C}) = [ hat g(q) + hat g(q+b) ] + sum_{m>=1} sum_R [ hat g({q} union R) + hat g({q+b} union R) ].
```

The `m = 0` bracket is what `(T1)` controls.  The tail is what a proof of
`affine-orientation-glue-lemma` must control, and the memorizer shows it
cannot be controlled by degree, by `L^2` mass, or by noise -- all three of
which the memorizer keeps.
