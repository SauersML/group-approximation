---
rg: 2
id: hyperoctahedral-corner-support-forces-packet-normalizer
kind: claim
title: The hyperoctahedral primitive and reflection corners force literal transporters into the packet normalizer
distinct_from:
  canonical-types-extend-every-finite-bass-serre-actor: that constructs extensions of canonical ultraproduct types across arbitrary finite Bass--Serre actors; this is an internal support-rigidity theorem saying that a literal group word preserving the specific hyperoctahedral corner must normalize the original finite packet.
  single-finite-type-promotion-forces-a-finite-perfect-strategy: that derives a finite strategy from abstract covariant Schur-factorized transports; this proves that the literal corner-preservation hypothesis itself forces those transports back into one finite root packet.
  common-reflection-defect-is-holonomy-spectator: that splits any transporter preserving the accepting corner from its thin complement; this identifies the group-theoretic normalizer containing every literal such transporter.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that excludes a completed atlas already known to lie in one finite root block; this proves that literal conjugation by a corner-preserving group word necessarily has that property.
---

Let

```text
K_N=(C_2)^N semidirect S_N,             N>=3,             (HIS1)
```

and let `rho_N` be its tautological signed-permutation representation on
`V=C^N`.  Write `p=z_(rho_N)` for the primitive central idempotent in
`C[K_N]`.  Let `s_0` be the sign flip on coordinate zero and put

```text
q=p(1+s_0)/2.                                             (HIS2)
```

Thus, on the `rho_N` block, `q` is the projection `Q` onto
`span(e_1,...,e_(N-1))` used by the common-reflection atlas.

## Support generation

Both group-basis supports generate the whole packet:

```text
<supp(p)>=K_N,                    <supp(q)>=K_N.           (HIS3)
```

For `p`, the coefficient of `k` is a nonzero scalar multiple of the
tautological character `chi(k^(-1))`.  Every coordinate sign flip and every
unsigned transposition has character `N-2`, which is nonzero for `N>=3`;
these elements generate `K_N`.

For `q`, Fourier inversion on the `rho_N` block says that its coefficient at
`k` is a nonzero fixed scalar times

```text
Tr(Q rho_N(k^(-1))).                                      (HIS4)
```

At `k=s_0` this trace is `N-1`.  At every unsigned transposition `(0 i)` it
is `N-2`.  Hence `supp(q)` contains `s_0` and all `(0 i)`.  The latter
generate `S_N`, and conjugating `s_0` by them produces every coordinate sign
flip.  This proves the second equality in `(HIS3)`.

## Literal transporter rigidity

Let `Gamma` contain `K_N`.  For every `g in Gamma`, conjugation permutes the
canonical group basis, so

```text
supp(g p g^(-1))=g supp(p) g^(-1),
supp(g q g^(-1))=g supp(q) g^(-1).                       (HIS5)
```

Consequently either equality

```text
g p g^(-1)=p                 or                 g q g^(-1)=q
                                                               (HIS6)
```

forces, using `(HIS3)`,

```text
g K_N g^(-1)=K_N.                                      (HIS7)
```

The same conclusion follows if the literal compression `qgq` is a unitary
of `q C[Gamma]q`: unitarity gives `(1-q)gq=0` and the analogous equation for
`g^(-1)`, hence `gq=qg` and the second equality in `(HIS6)`.

Thus an infinite packet normalizer supplies no new context placements.
Conjugation factors through the finite group `Aut(K_N)`; the possibly
infinite centralizer kernel acts trivially on every packet observable.  In
particular, if all context observables have the literal form

```text
g_c d_(c,x) g_c^(-1),          d_(c,x) in K_N,           (HIS8)
```

and every `qg_cq` is a corner unitary on the one common reflection carrier,
then every observable and every joint context projection lies in the single
finite-dimensional algebra

```text
q C[K_N] q.                                             (HIS9)
```

If these context partitions also satisfy all shared-variable equalities,
they give a finite-dimensional perfect BCS strategy.  Therefore this literal
one-global-packet architecture cannot realize a BCS with a strict
finite-dimensional gap (and a fortiori cannot realize the fixed no-CE BCS).

This does not exclude the signed-Hecke target: a multi-piece algebraic corner
unitary need not be the compression of one group element, so `(HIS5)` does
not apply.  It proves that replacing the missing additive holonomy by literal
normalizer conjugates cannot be that target.
