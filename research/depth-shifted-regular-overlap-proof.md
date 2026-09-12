---
rg: 2
id: depth-shifted-regular-overlap-proof
kind: route
title: Compute the shifted kernel image and sum the common regular irreducibles
target: depth-shifted-regular-overlap-is-exactly-one-sixteenth
requires:
  - two-power-sector-conjugator-dichotomy
---

Conjugation by `h=diag(2,1,1/2)` multiplies the six off-diagonal entries
`12,13,23,21,31,32` by

```text
2,4,2,1/2,1/4,1/2.
```

Thus `gamma in K_B(a)` has, modulo `2^a`, diagonal equal to one, lower
entries zero, entries `12,23` divisible by `2^(a-1)`, and entry `13`
divisible by `2^(a-2)`.  This proves that its image in `Q_A` is contained in
`U_a`.  Conversely every element of `U_a` has an upper-unitriangular lift in
`Lambda_0`; after conjugation by `h` all three upper entries are divisible by
`2^a`, so that lift lies in `K_B(a)`.  Hence the image is exactly `U_a` and
has order sixteen.  The transpose-inverse automorphism sends the generators
`A` to the generators `B` up to signs and preserves principal congruence
kernels, proving `|Q_A|=|Q_B|`.

For the representation formula, an irreducible `G`-representation occurs in
both quotient regular representations exactly when its kernel contains both
`K_A` and `K_B`, equivalently when it factors through `G/(K_AK_B)`.  Such an
irreducible `tau` occurs with multiplicities `r_A dim(tau)` and
`r_B dim(tau)`.  Summing the smaller copy count times `dim(tau)` gives

```text
sum_tau min(r_A,r_B) dim(tau)^2
 = min(r_A,r_B)|G/(K_AK_B)|.
```

At a mixed level `2^a q`, membership in either kernel imposes the same
condition `gamma=1 mod q`, because `h` is invertible modulo odd `q`.
Strong approximation/CRT splits the odd image from the fixed two-primary
parahoric image.  Multiplying the three upper parameters in `(DSO3)` by
appropriate odd integers realizes every one of the sixteen residues while
remaining trivial modulo `q`, so the join-index ratio is unchanged.

Finally the orthogonal projection of a unitary onto the intertwiner space is
supported on the common domain projection of trace `1/16` and has operator
norm at most one (it is the mean-ergodic average of unitary left-right
translates).  Its normalized Hilbert--Schmidt norm squared is at most `1/16`;
Pythagoras gives `(DSO6)`, and the Kazhdan inequality gives `(DSO7)`.
