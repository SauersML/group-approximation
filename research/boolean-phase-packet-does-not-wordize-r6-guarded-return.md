---
rg: 2
id: boolean-phase-packet-does-not-wordize-r6-guarded-return
kind: claim
title: The Boolean phase packet computes the R6 guarded AND only in selected sectors
distinct_from:
  boolean-predicate-central-phase-word: that constructs the nonlinear phase in assignment-coordinate irreducibles of a finite 2-group; this couples the specific guarded AND to visible R6 selectors and then to the D16 Hadamard cell.
  controlled-central-phase-finite-group-barrier: that proves the general affine obstruction; this identifies the exact selector, phase, and one-half wrong-sector mass for the Fanizza R6 attempt.
  r6-guard-is-visible-but-guarded-source-is-not-a-word: that proves the guarded overlap reflection is not a word of the three native commuting signs; this tests the strongest finite noncommutative predicate gadget intended to evade that word barrier.
---

# The Boolean phase packet computes the R6 guarded AND only in selected sectors

ESTABLISHED.  Use bits `(g,p,s)` for the three R6 projections

```text
G=(1+gamma)/2,       P=(1-Z)/2,       S=(1-Y)/2
```

and let

```text
f(g,p,s)=g p s.                                          (BPR1)
```

The construction in `boolean-predicate-central-phase-word` gives a fixed
finite 2-group `H_f` and central involution word `c=W_f` such that, in each
distinguished assignment-coordinate irreducible `pi_a`,

```text
pi_a(c)=(-1)^(f(a)) I.                                   (BPR2)
```

There is an immediate compatibility obstruction with the native R6 words.
For the cubic monomial, the phase factor is an iterated commutator of
overlapping unitriangular transvections, schematically

```text
c_3=[[u_g,u_p],u_s].                                    (BPR2a)
```

The native signs `gamma,Z,Y` commute on the C18 table.  Therefore every
homomorphism which directly identifies

```text
u_g=gamma,             u_p=Z,             u_s=Y         (BPR2b)
```

sends `c_3` to the identity.  In particular it cannot give the nontrivial
phase on the active-overlap character.  The bits `a_i` in the predicate
construction say whether a transvection is present in one external
assignment coordinate; they are not eigenvalues of three commuting group
elements `u_i`.

If one externally labels the distinguished irreducibles by the native
selector assignments and takes their matched direct sum, then `(BPR2)` does
realize the desired coefficient

```text
c=1-2GPS.                                                 (BPR3)
```

This is an exact completeness representation of the finite packet.  In a
genuine R6 operator solution `GPS=0`, so it also has the correct trivial
phase on the active recurrence support.

It is not an ordinary-word soundness compiler.  Direct identification has
already failed by `(BPR2a)--(BPR2b)`.  To connect the externally labelled
models in `(BPR2)` to the native signs instead, let

```text
D=<gamma,Z,Y>
```

be the visible Boolean selector subgroup and require `c` to commute with
`D`.  In the regular representation of any finite overgroup containing this
data there are exactly two cases.

1. If `c in D`, its phase is an affine character of `(g,p,s)` and cannot be
   `(BPR1)`.
2. If `c notin D`, then above **every** selector character the two `c` signs
   occur with equal multiplicity.  Hence `(BPR2)` is wrong on exactly one
   half of every selector sector, not on a negligible exceptional block.

Flexible HS exactification of the fixed packet preserves this regular type
decomposition; it does not select the assignment-coordinate irreducibles.
Adding the relator `c=1` does not repair the issue.  The surviving exact
selector characters of a finite central extension form an affine set.  The
desired support of `(BPR1)=0` has seven of the eight characters and is not
affine; any affine subset avoiding the single forbidden character has size
at most four.  Thus exact phase pruning either retains a wrong sector or
discards at least three satisfying selector sectors.  R6 completeness in
one chosen representation does not supply the missing representation-wide
state/type selection.

Nor does the D16 charger turn the central phase into the required return.
If the packet is tensored with D16 and one takes `d=c`, then on the selected
two-dimensional D16 type

```text
d=diag(c,c),                                               (BPR4)
```

so the Hadamard commutator has zero energy for every value of `c`.  The
needed input is instead

```text
d=diag(1,c).                                               (BPR5)
```

Applying the predicate construction once more to the four-bit controlled
function `q f(g,p,s)` produces `(BPR5)` only in distinguished assignment
sectors and recreates the same one-half regular wrong mass.  If a semidirect
or HNN Hadamard letter is required to normalize the selector-central packet,
the exact block calculation forces the two blocks in `(BPR5)` to be equal.
If it is adjoined freely, arbitrary representations need not place the two
phase sectors on the two D16 selector lines.

Therefore the nonlinear 2-group packet solves coefficient computation on an
externally labelled family of representations but not the native-input
coupling or the common-source/D16 word cell.  It also does not manufacture the
arithmetic two-path average: a central phase supplies equal D16 blocks,
whereas both the Fanizza and arithmetic applications require a literal
selector-central word with independently authenticated blocks.
