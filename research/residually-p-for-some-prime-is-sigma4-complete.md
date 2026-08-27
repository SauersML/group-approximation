---
rg: 2
id: residually-p-for-some-prime-is-sigma4-complete
kind: claim
title: Being residually a finite p-group for some prime is Sigma-zero-four complete, so the fourth arithmetical level is realized by a natural group property
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  residually-p-two-generator-recursive-is-pi3-complete: that fixes the prime and lands at the third level; this quantifies over primes and lands at the fourth, and its content is the selectively visible index family that makes the existential over primes non-degenerate.
  natural-group-properties-realize-the-first-three-levels: that records the first three levels and poses this question; this answers it.
  index-set-profinitely-closed-is-pi3-complete: that is the profinite closedness index set for a single topology; this needs a family whose closedness in the pro-q topology is automatic for every q other than one prescribed prime.
---

ESTABLISHED.  For two-generator recursive presentations,

```text
{ e : G_e is residually a finite p-group for some prime p }
    is Sigma^0_4-complete.                                              (S4)
```

So the fourth level of the arithmetical hierarchy is realized by a natural
property of finitely generated groups, continuing the pattern of
[[natural-group-properties-realize-the-first-three-levels]] (property (T)
at level one, the approximation properties and amenability at level two,
residual finiteness and residual `p`-finiteness at level three).

**Upper bound.**  `Sigma^0_4`: an existential over primes of the `Pi^0_3`
condition of [[residually-p-two-generator-recursive-is-pi3-complete]].

**Hardness: a selectively visible index family.**  Fix a computable
enumeration `(p_i, x_i)` of pairs (prime, natural number) and put

```text
row(i, k) = { p_i^(n!) + c_i : start_i <= n < start_i + k },
```

where `start_i >= i` and the shifts are factorials, `c_i = M_i!` with
`M_i >= i`, adjusted (finitely often, computably) so that no `c_i` is
itself an element of the set constructed.  Let

```text
J_e = {0, 1} u (union over i of row(i, k_i(e))),
```

where `k_i(e)` is infinite exactly when the `i`-th `Sigma^0_2` event of a
fixed uniform reduction fails, so that

```text
all rows over the prime p are finite   iff   the p-th Pi^0_3 event holds.
```

Then, for every prime `q`,

```text
J_e is closed in the pro-q topology   iff   every row over q is finite,   (S4a)
```

and therefore `J_e` is pro-`q` closed for some `q` iff the corresponding
`Pi^0_3` event holds for some prime, a `Sigma^0_4`-complete condition.
Feeding `J_e` to the shift family of
[[shift-raag-family-is-rf-iff-symmetrized-index-set-closed]] --- in its
pro-`p` form [[residually-p-two-generator-recursive-is-pi3-complete]] ---
turns (S4a) into (S4).

## Why the rows are selectively visible

Two computations, both elementary, are what make the existential over
primes non-degenerate; the first also explains why no earlier attempt
could work.

* **Arithmetic progressions are useless.**  A row that is an arithmetic
  progression with common difference `p` is *dense* in `Z_q` for every
  `q != p`, because `p` is invertible modulo `q^m`; so such rows are
  maximally visible to every other prime.
* **Factorial powers are invisible to the other primes.**  Fix `q` and
  `m`, and let `lambda` be the exponent of the unit group of `Z/q^m`.  For
  every `p != q` and every `n >= lambda`, `lambda` divides `n!`, so
  `p^(n!) = 1` in `Z/q^m` --- a threshold *uniform in p*.  Likewise
  `c_i = M_i! = 0` in `Z/q^m` once `M_i >= q^m`.  Hence, for each fixed
  `q^m`, **all but finitely many elements of `J_e` are congruent to `1`
  modulo `q^m`**.

## The companion at `Pi^0_4`, and the finite-presentation contrast

The same family settles the universal form.  Since `J_e` is pro-`q` closed
exactly when every row over `q` is finite, and the rows over distinct
primes are independent,

```text
{ e : G_e is residually a finite p-group for EVERY prime p }
    is Pi^0_4-complete,                                                 (P4)
```

by the same reduction with the outer quantifier universal.  So both halves
of the fourth level are realized:

```text
level 4:   residually p for some prime   Sigma^0_4-complete,
           residually p for every prime  Pi^0_4-complete.
```

For **finite** presentations the picture collapses one level, as it does
for residual finiteness: residual `p`-finiteness of a finite presentation
is `Pi^0_2` (a finite relator list needs no closure quantifier), so
"residually `p` for some prime" is `Sigma^0_3` and "for every prime" is
`Pi^0_3` there; their completeness is open, and by
[[finite-presentation-rice-criterion-via-the-fixed-positive-rope]] the
compiler route is unavailable, since the rope is not residually finite and
a fortiori not residually `p`.

## Where the mechanism stops

The index-set family supplies exactly two quantifier resources: the
finiteness of a single row (`Sigma^0_2`), and the two indices `x` and `p`
that range over it.  That yields levels three (`Pi^0_3`, fixed prime) and
four (both halves, quantifying over primes) and no further; reaching a
natural fifth level would need a genuinely new resource --- another
topological parameter of the same group, not another index.
