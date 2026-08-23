---
rg: 2
id: infinite-index-factor-induction-kills-every-coset-payload
kind: claim
title: Infinite-index finite-trace induction kills every localized coset factor payload
distinct_from:
  infinite-index-canonical-subgroup-corner-is-impossible: that treats one projection in a probability crossed product satisfying a Fourier compression identity; this treats every covariant coset imprimitivity system, including invariant-mean and commensurated induction attempts.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that distinguishes counting-measure induction from compact probability coinduction for algebraic actions; this gives the representation/factor version and identifies exactly what the GNS quotient kills.
  standard-permanence-does-not-rigidify-the-cdi-image: that states the induction firewall qualitatively; this proves the infinite-index trace-zero assertion and audits the invariant-mean and Hecke workarounds.
---

Let `H<Lambda` have infinite index and put `I=Lambda/H`.  Suppose a finite
tracial von Neumann algebra `(M,tau)` contains a covariant coset carrier

```text
{p_x:x in I},
p_x p_y=0                      (x!=y),
u_g p_x u_g^*=p_(gx).                                  (IIP1)
```

Then

```text
tau(p_x)=0                                                 (IIP2)
```

for every `x`.  With faithful trace all the carriers vanish.  With a
possibly nonfaithful tracial state, their images vanish in its GNS quotient.
Therefore no factor stored in the identity-coset corner can survive as a
positive-trace payload of a finite factorial character of `Lambda`.

This remains true if `H` is coamenable and one replaces normalized counting
measure by an invariant mean on `I`: every singleton has mean zero, so its
localized factor corner has zero GNS norm.  Commensuratedness does not help.
The canonical Hecke trace lives on double-coset operators rather than giving
a tracial group character with a positive identity-coset carrier.  The
quasi-regular coefficient

```text
g |-> <lambda_(Lambda/H)(g)delta_H,delta_H>=1_H(g)       (IIP3)
```

is a character only when `H` is normal; in that case it is merely the
regular character of the quotient `Lambda/H` and contains none of the
original factor payload.

Thus standard induced representations from an infinite-index
acylindrically hyperbolic subgroup cannot transfer a non-CE generating
factor into a character-rigid Kac--Moody host.  Any successful transfer must
delocalize the payload over infinitely many cosets or use a genuinely
non-imprimitivity construction.
