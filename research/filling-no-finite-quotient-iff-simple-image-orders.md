---
rg: 2
id: filling-no-finite-quotient-iff-simple-image-orders
kind: claim
title: A power filling has no finite quotient iff no finite simple image of the host kills that power
distinct_from:
  sp21-one-element-filling-without-finite-quotients: that is the open existence assertion for one lattice; this is the elementary criterion deciding any single candidate, valid for every group
  kapovich-wise-rf-iff-finite-quotients: that reduces Gromov's question to hyperbolic groups without finite quotients; this says which finite images of a host decide whether one filling of it has any finite quotient
---

**ESTABLISHED.** Let `Γ` be any group, `g in Γ` and `n >= 1`. Then

```text
Γ/<<g^n>> has no nontrivial finite quotient
  <=>  for every epimorphism φ: Γ ->> S onto a finite simple group,
       the order of φ(g) does not divide n.
```

**Necessary conditions read off from it.**

1. `φ(g) != 1` for every epimorphism of `Γ` onto a finite simple group. So `<<g>>`
   must itself be dense in the profinite completion of `Γ`.
2. Abelian simple images. If `Γ^ab` is finite, then:
   - the image of `g` must generate `Γ^ab`, so `Γ^ab` is cyclic;
   - `n` must be coprime to `|Γ^ab|`.

   Indeed, for a prime `p` with `Γ ->> Z/p`, both possible orders `1` and `p`
   divide `n` as soon as `p | n`.
3. Congruence images of an arithmetic host. When `ord φ(g) = o_𝔭` at a congruence
   image `G(O/𝔭)/Z`, `n` must avoid every multiple of `o_𝔭`. This is the
   `n = N!` obstruction recorded on `sp21-one-element-filling-without-finite-quotients`.

Proof in `filling-no-finite-quotient-iff-simple-image-orders-proof`. It is
elementary, and no novelty is claimed.
