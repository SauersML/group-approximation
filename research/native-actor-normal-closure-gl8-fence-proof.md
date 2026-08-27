---
rg: 2
id: native-actor-normal-closure-gl8-fence-proof
kind: route
title: Put the paid collision in the stabilizer kernel of the three-bit constant atom
target: native-actor-normal-closure-does-not-localize-paid-t00-support
requires:
  - native-t00-y1-collision-pays-marked-opnorm
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
  - native-whitehead-hecke-head-has-order-seven-anchor
  - el20-order-seven-heads-force-zero-common-hecke-reducing-cut
  - paid-t00-pauli-menu-hits-whitehead-constant-atom
---

On the character basis `delta_x`, `x in F_2^3`, represent the three incoming
roots by the diagonal signs

```text
C_7=Z_(100),             C_8=Z_(010),
C_9=Z_(001),             z=-1.                       (1)
```

The dual roots are the three coordinate translations, so the marked
Heisenberg relations are exact.  The literal `J_1,J_2` are the two adjacent
coordinate permutations.  Collapse the auxiliary coordinate `4` of the
first head to coordinate `9`, and the auxiliary coordinate `5` of the second
head to coordinate `7`.  The resulting linear transvections give the same
two `GL_3(F_2)` Singer matrices, so both head products still have exact order
seven.  This is a quotient of the displayed occurrence relations and does
not manufacture a source projection.

Let `M` be the involution with columns `(100,110,101)` and let `S_M` be its
permutation implementer on `ell^2(F_2^3)`.  Set

```text
rho(D)=C_8 S_M.                                      (2)
```

Then `rho(D)` is a nonidentity involution, fixes `delta_000`, and has a
four-dimensional negative eigenspace.  Exact signed-permutation
multiplication gives

```text
[C_7,rho(D)]C_8=C_9,
[rho(D),D_8]D_7=z.                                  (3)
```

Thus both coefficient-sensitive identities `(TYC8)` survive after the new
root occurrences are sent to `C_9` and `z`.  In particular the model does
not kill the mark: `[C_7,D_7]=z=-1`.

The common all-positive atom for the actual `J_1,J_2` frame is the line
`E=C delta_000`.  Every linear actor fixes that line pointwise, as do
`rho(D)` and `C_9`.  Hence every conjugate of `rho(D)` by `J_1,J_2` or either
order-seven head fixes `E` pointwise, and so does every product or commutator
of those conjugates.  Nevertheless `rho(D)` is nontrivial and has paid
negative rank `4/8` off `E`.  Therefore

```text
E P_D=0.                                             (4)
```

This proves more than failure of normalization: even adding exact
normalization by the whole native actor menu does not transport any of the
paid negative support to the constant atom.

The scope is exactly the actor normal closure.  The literal dual Pauli roots
`Y_1,Y_2,Y_3` are not in that closure.  Conjugating by their eight-element
translation group crosses the fence, and
`paid-t00-pauli-menu-hits-whitehead-constant-atom` proves by the character
partition identity that one of those eight conjugates has positive
compression on `E`.  The `GL_8` audit checks this distinction explicitly:
all `J_i`/head conjugates fix `delta_000`, while the Pauli-conjugate menu has
nonzero aggregate compression defect there.

Finally the constant atom cannot be relabelled as the signed Hecke source.
`el20-order-seven-heads-force-zero-common-hecke-reducing-cut` proves from the
ordinary word identity `(OZC3)` that every common reducing subcut of the
actual signed source `Q` is zero.  Since `E` reduces both heads, its image in
`Q` is necessarily zero.  Thus the finite model fences normalization by the
actor words as a substitute for the Pauli localization lemma, while `(OZC3)`
fences the attempted identification of that atom with the signed source.

The MSI audit uses exact integral signed-permutation matrices in
`GL_8(C)`; dimension eight is the smallest faithful matrix carrier for the
three-bit character basis used by the actual middle-index packet.  This is a
scoped model of the named occurrence table, not a representation of the full
binary Leavitt elementary group.  No Property T, canonical trace, literature
input, local computation, or Lean compilation is used.
