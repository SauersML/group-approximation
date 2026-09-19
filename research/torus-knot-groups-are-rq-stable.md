---
rg: 2
id: torus-knot-groups-are-rq-stable
kind: claim
title: Every torus knot group <x,y | x^p = y^q>, in particular K(3,4), is R_q-stable in operator norm, with an uncontrolled finite-quotient padding
distinct_from:
  torus-knot-group-k34-is-matricially-stable: that is the open same-dimension, unpadded operator-norm stability of K(3,4); this is the padded statement, where the almost representation is corrected only after adding an arbitrary block that factors through a finite quotient.
  bs1n-rq-padded-opnorm-stability: that imports Willett's one-relator theorem 7.9(i) for BS(1,n); this imports his free-by-cyclic theorem 1.14 for the torus knot groups, after checking that they are free-by-cyclic with H_2 = 0.
  dadarlat-matricial-stability-obstruction: that is the rational-cohomology obstruction to unpadded stability; here H^2(K; Q) = 0, which is exactly the hypothesis under which Willett's padded theorem is unconditional.
  torus-knot-group-k34-has-central-eigencorners: that is the projection conclusion that the chain to T-bar consumes; this statement does not imply it by any known argument (see "What it does not give").
---

**ESTABLISHED (literature, with an elementary hypothesis check).**  Let
`p, q >= 2` with `gcd(p, q) = 1`, and let `K = K(p,q) = <x, y | x^p = y^q>`.
Then `K` is `R_q`-stable in Willett's sense.  That is, for every finite
`S` in `K` and `epsilon > 0` there are a finite `T` in `K` and `delta > 0`
with the following property.  For every unital `(T, delta)`-representation
`phi : K -> M_N(C)_1` there are representations `theta : K -> U(k)` and
`pi : K -> U(N + k)`, both factoring through finite quotients of `K`, with

```text
||(phi(s) (+) theta(s)) - pi(s)|| < epsilon          (s in S).      (RQ)
```

No control on `k` or on the isomorphism type of `theta` is asserted.  The
case used by the Thompson chain is `(p, q) = (4, 3)`, i.e.
`K(3,4) = <x, y | x^4 = y^3>`.

## Corona form

By a diagonal argument over an exhaustion `S_1 ⊂ S_2 ⊂ ...` of `K` and
`epsilon_j = 1/j`, `(RQ)` gives the following.  Let `rho : K -> U(Q)` be a
homomorphism into `Q = prod M_(k_n) / (+) M_(k_n)`.  Then there are
representations `theta_n : K -> U(m_n)` and `pi_n : K -> U(k_n + m_n)`, each
factoring through a finite quotient, with

```text
rho (+) theta = pi     in   Q' = prod M_(k_n + m_n) / (+) M_(k_n + m_n),
```

where `theta = [(theta_n)]` and `pi = [(pi_n)]`.

Source: R. Willett, *Conditional representation stability, classification
of \*-homomorphisms, and relative eta invariants*, arXiv:2408.13350 (PDF
dated May 25, 2026, read 2026-09-19): Definition 1.3, Definition 1.6 with
`Q = R = R_q` (Remark 1.8), and Theorem 1.14 (Theorem 7.8 in Section 7.1).
These are quoted verbatim in `torus-knot-groups-rq-stable-citation`, which
also proves the one hypothesis to check: `K(p,q)` is free-by-cyclic,
`F_((p-1)(q-1)) ⋊ Z`, with `H_2(K; Z) = 0`.

## What it does not give

- **Unpadded stability.**  It does not give same-dimension matricial
  stability of `K(3,4)` (`torus-knot-group-k34-is-matricially-stable`).
  Willett, Remark 1.18: "We do not know if the conclusions of Theorems
  1.10, 1.14, or 1.15 can be strengthened to (conditional) stability."
- **Eigencorners, by compression.**  It does not give central eigencorners
  (`torus-knot-group-k34-has-central-eigencorners`) by compression.  In the
  corona form, let `P = [1_(k_n) (+) 0]`.  Then `P` commutes with `pi(K)`,
  and `P (pi(K)' ∩ Q') P = rho(K)' ∩ Q`.  Every exact spectral projection
  `E` of `pi(c)` lies in `pi(K)' ∩ Q'`, but its compression `P E P` is only
  a positive eigen-element of `rho(c)`.  Positive eigen-elements exist for
  every corona representation without any stability (see the attempt
  recorded on `torus-knot-group-k34-is-matricially-stable`).  `P E P` is a
  projection when `P` commutes with `E`.  That happens, for instance, when
  `P_n` can be chosen in the exact commutant `pi_n(K)'`, because `E_n` is
  central in `pi_n(K)''`.  Because `K` does not have Property (T),
  asymptotic commutation does not force this.
- **Hilbert-Schmidt statements.**  It is an operator-norm statement, so it
  is not subject to the EL20 trace kill.  Its padding, however, is exactly
  what the corner arguments cannot absorb.
