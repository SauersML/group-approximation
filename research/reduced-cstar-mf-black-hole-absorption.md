---
rg: 2
id: reduced-cstar-mf-black-hole-absorption
kind: claim
title: A reduced full-radical group algebra is an MF black hole for every unital over-algebra
distinct_from:
  full-mf-radical-cstar-reflection: that theorem computes the MF reflection of the two canonical group completions; this theorem proves upward permanence through arbitrary unital C-star inclusions.
  full-mf-radical-absorber: that is a group-level quotient formula requiring normal closure; this theorem is a reduced-C-star statement and needs only a subgroup inclusion, with no normality.
artifacts:
  - research/reduced-cstar-mf-black-hole-absorption-proof.md
---

Call a unital C-star algebra `B` an **MF black hole** if every star
homomorphism from `B` to every MF C-star algebra is zero.

MF black holes are upward hereditary under unital inclusions: if

```text
B -> A
```

is an injective unital star homomorphism and `B` is an MF black hole, then so
is `A`.

Let `H` be a nonamenable countable group with `Rad_MF(H)=H`.  Then
`C*_r(H)` is an MF black hole.  Therefore:

1. for every countable supergroup `H <= G`, the algebra `C*_r(G)` is an MF
   black hole;
2. every nonzero quotient of `C*_r(G)` is non-MF;
3. every unital C-star tensor product containing `C*_r(H)` as the first
   factor is an MF black hole;
4. every unital crossed product, amalgam, or other C-star over-algebra into
   which `C*_r(H)` embeds unitally is an MF black hole.

For the Hilbert-hotel group `H=EL_16(L_(F_2)(1,2))`, all conclusions hold.
In particular, **every countable group containing this one has a reduced
group C-star algebra with no nonzero MF image**, whether or not the subgroup
is normal and whether or not the ambient group has nontrivial MF-visible
quotients.

