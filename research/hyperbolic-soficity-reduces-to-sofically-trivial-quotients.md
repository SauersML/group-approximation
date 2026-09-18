---
rg: 2
id: hyperbolic-soficity-reduces-to-sofically-trivial-quotients
kind: claim
title: A nonsofic hyperbolic group exists iff some hyperbolic group has no nontrivial sofic quotient iff some hyperbolic presentation has positive permutation Cheeger constant
distinct_from:
  nonsofic-hyperbolic-question-reduces-to-one-fixed-host: that pushes a bad ball into a finite-quotient-free quotient of the host, where the quotient may still have nontrivial sofic quotients; this makes the sofic radical itself surject, so the quotient has no sofic quotient at all, and it is then strictly stable with a positive Cheeger constant
  hyperbolic-rf-question-reduces-to-one-fixed-host: that is the residual-finiteness version, where Kapovich--Wise supplies a finite-quotient-free group; this is the sofic analogue, where the sofic radical of a free product plays that role
  sofically-trivial-iff-positive-permutation-cheeger: that is the presentation-level equivalence for one finitely presented group; this shows that in the hyperbolic class the extreme case of that equivalence occurs as soon as any nonsoficity occurs
---

**ESTABLISHED** through `hyperbolic-soficity-reduces-to-sofically-trivial-quotients-proof`.

Let `T` be any non-elementary word-hyperbolic group with trivial maximal
finite normal subgroup, `E(T) = 1`. Call a group **sofically trivial** when
every homomorphism from it to a sofic group is trivial, and write `h(S|R)` for
the permutation Cheeger constant of
`sofically-trivial-iff-positive-permutation-cheeger`. The following
are equivalent.

1. Some word-hyperbolic group is not sofic.
2. Some nontrivial word-hyperbolic group is sofically trivial.
3. Some finite presentation `<S|R>` of a nontrivial word-hyperbolic group
   has `h(S|R) > 0`.
4. Some nontrivial word-hyperbolic group is strictly permutation stable and
   has no nontrivial finite quotient. (Flexible stability may replace strict
   stability.)
5. For every finite `M subset T` there is a surjection `pi : T -> Q`,
   injective on `M`, onto a non-elementary word-hyperbolic group `Q` that is
   sofically trivial.
6. `T` has a nontrivial word-hyperbolic quotient that is sofically trivial.

## Sofic Kapovich--Wise form

Negating the list:

```text
every hyperbolic group is sofic
  <=> every nontrivial hyperbolic group has a nontrivial sofic quotient
  <=> every nontrivial hyperbolic quotient of T has a nontrivial sofic quotient
  <=> every finite presentation of a hyperbolic group has h(S|R) = 0.
```

Here `h(S|R) = 0` means that there are almost-actions with no global fixed
point and arbitrarily small relator defect. This is the exact sofic analogue of
Kapovich--Wise's "all hyperbolic groups are residually finite iff every
infinite hyperbolic group has a nontrivial finite quotient". Soficity of all
hyperbolic groups follows from a nontriviality statement, which is much weaker
on its face.

## Kazhdan host

Take `T` torsion-free, non-elementary, hyperbolic and Kazhdan
(`torsion-free-hyperbolic-kazhdan-partner-exists`). Then a nonsofic hyperbolic
group exists iff `T` is a marked limit of quotients `Q_n` with all of the
following properties:

- each `Q_n` is a non-elementary Kazhdan hyperbolic group;
- each `Q_n` has no nontrivial sofic quotient, and in particular no finite,
  amenable or LEF quotient;
- each `Q_n` is strictly permutation stable, with the linear rate
  `supp(sigma) <= delta(sigma) / h` for every almost-action `sigma` of a fixed
  presentation of `Q_n`.

## What this settles about certificates

- **Stability certificates are complete for the flagship.** The
  compression and commuting-non-LEF certificates vanish on every group locally
  embeddable into hyperbolic groups
  (`hyperbolic-local-embedding-kills-compression-certificates`). The positive
  Cheeger constant does not: if any nonsofic hyperbolic group exists, some
  hyperbolic group is certified nonsofic by `h > 0`, the most rigid
  stability certificate there is, with no finite quotients involved. So "no
  certificate survives local embedding" is false as a class statement. The
  flagship is exactly the existence question for this one certificate.
- **The refutation side is one uniform construction.** To prove every
  hyperbolic group sofic, it is enough to build, for each non-elementary
  hyperbolic quotient `Q` of the Kazhdan host, a fixed-point-free
  almost-action of arbitrarily small defect. No injectivity or separation is
  needed.
- **The Chapman--Peled route aims at a flexibly stable non-residually-finite
  group.** Saturation shows that any success can be upgraded to a strictly
  stable, sofically trivial Kazhdan hyperbolic quotient. It does not show that
  the random groups themselves have this form.

## Hyperlinear version

The same proof gives: a non-hyperlinear hyperbolic group exists iff some
nontrivial hyperbolic group has no nontrivial hyperlinear quotient, iff the
fixed host `T` has such a quotient, injective on any prescribed finite set. The
only extra input is that finite direct products of hyperlinear groups are
hyperlinear. No Cheeger-constant form of the hyperlinear version is claimed.

No literature survey for novelty was done. Not Lean-verified.
