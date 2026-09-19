---
rg: 2
id: affine-memorizer-orthogonality-proof
kind: route
title: A set invariant under two independent F_2 translations has size divisible by four
target: affine-memorizers-are-cross-direction-orthogonal
requires: []
---

Both statements come from one counting argument, applied twice.

**Disjoint Fourier support.**  By `linear-pairing-memorizer-dictator-proof`
the Fourier support of `B_{b,r}` is
`{ {0} union supp(A) : A subset P_b \ {C_b}, |A| = r }`, and every member
contains `0`.  Suppose `b != c` are nonzero and some set lies in both
supports.  Deleting the common forced coordinate `0` leaves a set `S` with
`|S| = 2r` that is a union of `b`-pairs *and* a union of `c`-pairs, so

```text
S + b = S,      S + c = S.
```

Hence `S` is invariant under the subgroup `<b,c> = {0, b, c, b+c}`, which
has exactly four elements because `b, c` are distinct and nonzero over
`F_2`.  A set invariant under a group is a union of its orbits, and every
orbit here has size `4`, so `4 | |S| = 2r`.  But `r` is odd, so
`2r = 2 mod 4`.  Contradiction.

**No cross-direction contribution to the quotient singleton.**  Restriction
to `D_b` sends the character `chi_U` to the quotient character indexed by
the set of `b`-cosets meeting `U` in an odd number of points.  For a
monomial `U = {0} union supp(A)` of `B_{c,r}` to restrict to the singleton
quotient character at `C_b = {0,b}`, we need `|U intersect {0,b}|` odd and
`|U intersect {q, q+b}|` even for every other coset.  Since `0 in U`, the
first condition says `b notin U`; the second says `S := U \ {0}` meets every
coset `{q,q+b}` with `q notin {0,b}` evenly, and `S intersect {0,b} = empty`.
Together these say `S` is a union of full `b`-cosets, i.e. `S + b = S`.  And
`S = supp(A)` is a union of `c`-pairs, so `S + c = S`, with `|S| = 2r`.  The
same four-element-orbit contradiction applies.

**The superposition.**  Fix a sign pattern `s` and put
`P_s = sum_{b != 0} s_b B_{b,r}`.  Disjoint supports give
`||P_s||_2^2 = sum_{b != 0} ||B_{b,r}||_2^2 = (N-1)/M`, and
`M = Theta_r(N^r)` gives `Theta_r(N^(1-r))`.  For the quotient coefficient:
`B_{b,r}|_{D_b} = X_0` contributes exactly `s_b` to the singleton at `C_b`,
and by the previous paragraph no monomial of any `B_{c,r}` with `c != b`
contributes anything there.  So that coefficient is exactly `s_b`.

Note where oddness of `r` is spent: only in `2r = 2 mod 4`.  For even `r`
both arguments collapse, which is why the construction fixes `r` odd.
