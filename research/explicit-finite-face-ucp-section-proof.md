---
rg: 2
id: explicit-finite-face-ucp-section-proof
kind: route
title: Read the averaged section as a matrix coefficient of the right regular representation on a Hilbert module
target: explicit-finite-face-ucp-section-is-edge-equivariant
requires:
  - triangle-colimit-llp-reduces-to-relator-local-splitting
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

The equivalence node supplies the two structural facts used: `E=P_1 *_(P_0)
P_3` embeds in `G_0` with `q_E:E->>P:=P_13` surjective, and the composite
`C^*(E) subset C^*(G_0) ->> C^*(Lambda)` sends `u_e` to `u_(q_E(e))`, so that
the image of `C^*(E)` is `C^*(P) subset C^*(Lambda)`.

**Complete positivity.**  Let `M:=l^2(P) (x) C^*(E)`, the free right Hilbert
`C^*(E)`-module of rank `|P|`, and let `R` be the right regular representation
of `P` on `l^2(P)`, `R_p delta_x = delta_(x p^(-1))`.  Since `P` is finite,
`R` extends to a faithful unital `*`-homomorphism `C^*(P)->B(l^2(P))`, and
`R (x) 1` is a unital `*`-homomorphism `C^*(P) -> L(M) = M_(|P|)(C^*(E))`.  Put

```text
xi := |P|^(-1/2) sum_(x in P) delta_x (x) u_(sigma(x)) in M. (FFP1)
```

Then `<xi,xi> = |P|^(-1) sum_x u_(sigma(x))^* u_(sigma(x)) = 1`, so `xi` is a
unit vector, and for `p in P`

```text
(R_p (x) 1) xi = |P|^(-1/2) sum_x delta_(x p^(-1)) (x) u_(sigma(x))
               = |P|^(-1/2) sum_y delta_y (x) u_(sigma(y p)),
<xi,(R_p (x) 1) xi> = |P|^(-1) sum_y u_(sigma(y))^* u_(sigma(y p)),
```

which is `(FF1)`.  Hence `Theta(a)=<xi,(R (x) 1)(a) xi>` for all `a in C^*(P)`,
a compression of a unital `*`-homomorphism by a unit vector of a Hilbert
module -- the Stinespring form -- so `Theta` is completely positive, and unital
because `<xi,xi>=1`.  This proves `(a)`; no lifting theorem is used.

**Section property.**  Apply `q` to `(FF1)`.  For `x in P`, `q(u_(sigma(x)))
= u_(q_E(sigma(x))) = u_x`, so

```text
q(Theta(u_p)) = |P|^(-1) sum_(x in P) u_x^* u_(x p)
              = |P|^(-1) sum_(x in P) u_p = u_p,
```

which is `(FF2)`.  Note this needs only that `sigma` is a set section; no
positivity is involved.

**Edge equivariance.**  Assume `sigma(xh)=sigma(x)h` for `h in P_1`.  For
`p in P` and `h in P_1`,

```text
Theta(u_p u_h) = Theta(u_(p h))
  = |P|^(-1) sum_x u_(sigma(x))^* u_(sigma(x p h))
  = |P|^(-1) sum_x u_(sigma(x))^* u_(sigma(x p)) u_h
  = Theta(u_p) u_h,
```

using the equivariance at the point `xp`.  Both sides are linear in the second
variable and `C^*(P_1)` is spanned by `{u_h : h in P_1}`, so `Theta(ab)
= Theta(a) b` for all `b in C^*(P_1)`.  Taking `p=1` and `a=1` gives
`Theta(u_h)=u_h`.  This is `(c)`.

**Existence of an equivariant `sigma`.**  The right action `x |-> xh` of `P_1`
on `P` is free with orbit set `P/P_1` (left cosets `xP_1`).  Choose one
`x_i` per coset, choose any `sigma(x_i) in q_E^(-1)(x_i)`, and define
`sigma(x_i h):=sigma(x_i)h`.  This is well defined by freeness, and it is a
section because `q_E` restricted to `P_1 <= E` is the identity onto
`P_1 <= P` (the edge group embeds in `P_13` by hypothesis (H2) of the
equivalence node), so `q_E(sigma(x_i)h)=x_i h`.  Normalize by taking `x_i=1`
in the coset `P_1` and `sigma(1)=1`.
