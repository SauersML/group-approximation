---
rg: 2
id: faithful-rooted-tree-recurrence-countermodel-proof
kind: route
title: Separate a finite word window at one tree level and use its regular representation
target: faithful-rooted-tree-recurrence-cannot-pay-cps12
requires: []
---

For every `g!=1`, faithfulness supplies a vertex moved by `g`; hence `g`
acts nontrivially on some finite level.  Apply this to the finite set

```text
W union (K\{1}).                                      (RTP1)
```

Choose one level `n` at least as deep as all the resulting witness levels.
The finite-level homomorphism

```text
pi_n:Gamma -> Sym(T_n)                                (RTP2)
```

is injective on `K` and sends every `w in W` to a nonidentity permutation.
Let `Q_n=pi_n(Gamma)`, a finite group, and compose `pi_n` with the normalized
left regular representation of `Q_n`.

The regular trace vanishes on every nonidentity element, proving the first
part of `(RTR2)`.  Since `pi_n|_K` is injective, the restriction of the
regular representation of `Q_n` to `K` is `[Q_n:K]` copies of the regular
representation of `K`.  Therefore

```text
tr(rho_W(F))=tau_K(F)>0.                              (RTP3)
```

The map is an honest representation of `Gamma`, so all relators and all
group-algebra identities valid in exact representations have zero defect.
Substitution in `(RTR3)` gives a positive left side and zero right side.

Equivalently, the kernels of the finite-level actions have trivial
intersection, so the faithful rooted-tree actor is residually finite.  The
argument above records the stronger packet-sensitive statement needed here:
one level simultaneously retains the whole finite D8 packet, its forbidden
projection trace, and any prescribed canonical word window.
