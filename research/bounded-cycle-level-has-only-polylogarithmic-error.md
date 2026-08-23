---
rg: 2
id: bounded-cycle-level-has-only-polylogarithmic-error
kind: claim
title: The one-parameter bounded-cycle staircase reaches its finite congruence level only at polylogarithmic HS accuracy
distinct_from:
  bs14-long-cycles-admit-bounded-period-shadowing: that proves the error is O(K^-1/2); this expresses the same unavoidable staircase cost in terms of the imposed power level and finite quotient size.
  fixed-level-bs14-compatible-basin: that states the abstract radius-crossing condition; this quantifies the scale any proposed level-dependent radius estimate must beat.
  one-unipotent-quotients-are-bounded-congruence: that identifies the target quotient; this compares the target size with the preconditioning accuracy.
requires:
  - bs14-long-cycles-admit-bounded-period-shadowing
  - one-unipotent-quotients-are-bounded-congruence
---

For

```text
N_K=lcm_(1<=m<=K)(4^m-1),
alpha_K=C_*/sqrt(K),
Q_K=Gamma/<<s^N_K>>,                                  (PLE1)
```

one has the elementary bounds

```text
4^K-1 <= N_K < 4^(K(K+1)/2).                          (PLE2)
```

Together with `|Q_K| asymp_Gamma N_K^3`, these imply, for all sufficiently
large `K`, constants `c,C>0` with

```text
c/(log |Q_K|)^(1/2)
 <= alpha_K
 <= C/(log |Q_K|)^(1/4).                              (PLE3)
```

In fact the Akiyama--Luca least-common-multiple theorem for Lucas
sequences applies to `u_m=4^m-1` and gives

```text
log N_K=(3 log(4)/pi^2)K^2+O(K log K).                (PLE4)
```

Consequently the upper scale in `(PLE3)` is sharp:

```text
alpha_K asymp_Gamma (log |Q_K|)^(-1/4).               (PLE5)
```

Thus the bounded-cycle preconditioner approaches its moving finite target
only at a polylogarithmic rate in the target size.  Any proposed proof that
certifies a fixed-level stability basin merely by a negative power of
`N_K` or `|Q_K|` is quantitatively incapable of proving the crossing
condition in `fixed-level-bs14-compatible-basin`: its certified radius is
eventually much smaller than `alpha_K`.

This is a firewall on a **proof method**, not an upper bound on the actual
optimal stability radius.  A successful use of the staircase needs a
uniform or sufficiently polylogarithmic congruence-family repair theorem,
or must exploit the exact BS core and the special four `x`-rows rather than
expand them through a generic multiplication table.

The external number-theory input is Shigeki Akiyama and Florian Luca,
*On the least common multiple of Lucas subsequences*, Acta Arithmetica 161
(2013), 327--349, Theorem 2, DOI `10.4064/aa161-4-2`.
