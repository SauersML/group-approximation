---
rg: 2
id: leavitt-hnn-shift-has-sign-or-checksum-dichotomy
kind: claim
title: Canonical Leavitt HNN shifts either move the common sign or transport only diagonal checksums
distinct_from:
  proposed-twisted-clifford-substitution-needs-endomorphism-audit: that checks whether a Clifford substitution preserves its packet presentation; this classifies the canonical Leavitt corner, diagonal, and cross-corner maps as possible elementary-group HNN endomorphisms.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that uses finite representation multiplicity; this is an exact ring/Steinberg obstruction involving the common root sign and full prefix idempotents.
  diagonal-leavitt-prefix-transport-cannot-carry-cross-corners: that proves the rectangular coefficient map is not multiplicative; this adds the HNN/common-sign consequence and contrasts it with the genuine unital diagonal endomorphism.
  ascending-hnn-cannot-create-nonhyperlinearity: that is a permanence theorem after an injective endomorphism is given; this decides what the natural Leavitt endomorphisms actually transport before permanence is relevant.
---

Let `B=ARA` be the active binary Leavitt corner, with identity `A`, and put

```text
e_i=s_i t_i,                 J=x_13(A).                  (HSD1)
```

There are three natural ways to turn the matrix chart into a depth shift.

### 1. A single-corner shift moves the sign

The map

```text
alpha_i(r)=s_i r t_i                                      (HSD2)
```

is an injective, nonunital ring endomorphism with image `e_i B e_i`.  It
induces an injective endomorphism of the concrete elementary matrix group by

```text
I+M |-> I+alpha_i(M),                                    (HSD3)
```

but

```text
alpha_i(J)=x_13(e_i) != J.                               (HSD4)
```

If an HNN presentation imposes both the corner-shift relation and
`tJt^(-1)=J`, it forces `x_13(e_(1-i))=1`.  The complementary prefix
idempotent is full:

```text
t_(1-i) e_(1-i) s_(1-i)=A.                              (HSD5)
```

Steinberg commutators propagate a killed root coefficient through its
two-sided ideal, so `(HSD5)` forces `x_13(A)=J=1`.  Thus a genuine
single-prefix HNN shift cannot both fix and preserve a nontrivial common
sign.

### 2. The unital shift fixes the sign but gives only a checksum

The canonical diagonal endomorphism

```text
delta(r)=s_0rt_0+s_1rt_1                                (HSD6)
```

is unital and injective.  Hence its elementary-group endomorphism is
injective and fixes `J`.  Its iterates are

```text
delta^N(r)=sum_(|u|=N) s_u r t_u.                       (HSD7)
```

Conjugating a fixed root relation by the corresponding stable letter does
give the relation for `(HSD7)` with constant van Kampen area: after naming a
depth word as `t^N w t^(-N)`, the whole relation is one conjugate of the
base diagram.  But `(HSD7)` is only the diagonal checksum.  It does not name
any individual `s_u r t_v`, and in particular it does not produce the
`2^(2N)` cross-corner table

```text
t_u s_v=delta_(u,v)A.                                   (HSD8)
```

### 3. Cross-corner shifts are not endomorphisms

For `u!=v`, the desired map

```text
beta_(u,v)(r)=s_u r t_v                                 (HSD9)

is not multiplicative: its square product is zero because `t_v s_u=0`
(for INCOMPARABLE `u, v` -- neither a prefix of the other; for `u != v`
alone this fails, e.g. `t_(01) s_1 = t_0`; the proof only ever uses
`|u| = |v|`, where incomparability is automatic),
while `beta_(u,v)(rs)` need not vanish.  It therefore cannot induce a
Steinberg or elementary-group endomorphism and cannot be implemented by an
ascending HNN stable letter.

This gives an exact obstruction to the proposed uniform-area compiler when
the stable letter is induced by one of the canonical matrix-chart maps.  The
map that addresses one branch loses the common sign; the map that fixes the
sign symmetrizes all branches into one checksum; and the maps that would
name the cross-corners are not homomorphisms.  A stabilized Morita
equivalence can transport the full matrix chart between different ranks,
but ordinary HNN conjugacy then identifies whole representations and does
not turn its matrix entries into individually addressable root words in one
fixed elementary group.

It does not classify arbitrary endomorphisms decorated by an additional
self-similar state group.  Such a construction would have to prove
separately that its branching conjugators create every cross-corner while
preserving the same center; neither property follows from the
Leavitt/Morita chart.

There is one exact stronger partial construction.
`dual-prefix-growth-needs-two-morita-branches` applies right multiplication
by `t_i` on one Heisenberg root and left multiplication by `s_i` on the
adjacent root.  The two branch monomorphisms share the center and their
iterates give the complete dual-prefix packet; conjugating the packet may
replace `J` by an equal-trace level sign `J_n`.  But the Heisenberg base is
infinitely generated, and the root-dependent branch maps do not extend to
one ring-induced endomorphism of the finitely presented Steinberg ambient.
Thus moving signs solve the carrier-density objection, while finite
presentation of the two Morita branches becomes the exact remaining gate.

There is also a finite-presentation caveat.  Entrywise injectivity is clear
for `EL_n(B)`.  The repository's unconditional finite-presentation theorem
is for `St_n(B)`, and injectivity of the induced Steinberg endomorphism is
not automatic because the map `St_n(B)->EL_n(B)` can have a `K_2` kernel.
Thus even the diagonal-checksum HNN requires either a separate injectivity
theorem on the finitely presented Steinberg cover or a finite presentation
of the concrete elementary group.  Resolving that caveat would not repair
the cross-corner failure `(HSD8)--(HSD9)`.

**Scope note (2026-08-22 audit).**  The three computations are correct,
but the dichotomy is verified for the three displayed maps only; no
closure argument shows that every "canonical" shift (e.g.
`r -> sum_i s_i phi_i(r) t_i` with automorphisms `phi_i`, or `alpha_u`
with `|u| > 1`) falls into one of the two cases.  Read the title as a
classification of the listed shifts.
