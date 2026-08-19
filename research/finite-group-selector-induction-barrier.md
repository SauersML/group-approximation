---
rg: 2
id: finite-group-selector-induction-barrier
kind: claim
title: Finite group gadgets cannot isolate a nonaffine family of commuting selector signs
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  one-hot-selector-parity-barrier: That only rules out affine parity equations directly on commuting selector bits; this allows an arbitrary finite nonabelian auxiliary gadget and rules it out by induction from the selector subgroup.
  affine-auxiliary-control-flow-barrier: That allows arbitrarily many existential classical affine auxiliaries; this allows genuinely noncommuting finite-group auxiliaries but assumes the visible selectors remain commuting involutions.
  zpc-selector-sound-lcs-compiler: That remains open because a successful compiler may couple selectors to the payload so that bad selector representations do not extend, or may abandon commuting group-element selectors altogether.
---

Let `F` be a finite group, let `J in Z(F)` be an involution, and let
`z_1,...,z_m in F` be pairwise commuting involutions.  Write

```text
A=<J,z_1,...,z_m>.
```

Then `A` is a finite elementary abelian `2`-group.  Consider the set `Sigma`
of joint selector sign patterns which occur in finite-dimensional unitary
representations of `F` on which `J=-1`:

```text
Sigma = { (eps_1,...,eps_m) in {+1,-1}^m :
          some pi:F->U(V), V!=0, has pi(J)=-I and
          some 0!=xi in V with pi(z_i)xi=eps_i xi for all i }.
```

Identify signs with bits.  Then `Sigma` is exactly the image, under restriction
to `z_1,...,z_m`, of the affine character slice

```text
{ chi in Hom(A,{+1,-1}) : chi(J)=-1 }.
```

In particular `Sigma` is an affine subset of `F_2^m`.

Consequently, for `m>=3`, no such finite group gadget can have precisely the
one-hot selector sectors

```text
{e_1,...,e_m}
```

among its `J=-1` finite-dimensional representations.  More strongly, if every
one-hot sign pattern occurs, then at least one non-one-hot sign pattern also
occurs.

This remains true no matter how nonabelian the rest of `F` is.  Thus adding a
standalone finite noncommutative auxiliary group around commuting selector
involutions does not evade the selector obstruction.  A successful LCS
compiler must either use payload-coupling relations that prevent the induced
bad selector sectors from extending to the full compiled group, or encode the
branch sectors by a mechanism other than a commuting family of group-element
involutions.
