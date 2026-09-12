# The raw swap gives a complete two-branch routing table

Date: 2026-08-14

## 1. Exact routing

Let

```text
w = x_14(s1) x_41(-t1) x_14(s1)
```

be the raw swap.  The existing mul-past identities prove that it moves the
`1` branch:

```text
w x_0j(s1 a) = x_4j(-a) w,
w x_i0(b t1) = x_i4(-b) w.                            (RBR1)
```

The complementary identities are equally exact:

```text
[w,x_0j(s0 a)] = 1,
[w,x_i0(b t0)] = 1.                                  (RBR2)
```

They follow from

```text
p0 s0=s0,    t1 s0=0,
t0 p0=t0,    t0 s1=0.                                (RBR3)
```

Theorems `rawInvolutionWord_commutes_firstBranchRow` and
`rawInvolutionWord_commutes_firstBranchColumn` now state `(RBR2)` in
`GroupApproximation/Leavitt/RawSwapCompressors.lean`.  They were added
source-first and were not compiled in this iteration.

Thus `w` is an exact controlled router:

```text
branch 0  -> coordinate 0,
branch 1  -> coordinate 4.                            (RBR4)
```

No preferred matrix entries are needed to describe `(RBR4)`; it is a list
of group conjugation identities on adjacent root subgroups.

## 2. The full multiplication table is visible

For distinct auxiliary indices `i,j`, set

```text
O_k(a)=x_0j(s_k a),
I_l(b)=x_i0(b t_l).                                  (RBR5)
```

The Steinberg commutator relation gives

```text
[I_l(b),O_k(a)] = x_ij(b t_l s_k a)
                = x_ij(delta_lk b a).                (RBR6)
```

Equations `(RBR1)--(RBR2)` route both operands of `(RBR6)` to coordinate
`0` or `4` according to the same branch label, so the complete diagonal-one,
cross-zero table survives conjugation by `w`.  In particular, the raw word
does distinguish the two child branches locally; the missing decoder is not
the elementary identity `t_l s_k=delta_lk`.

## 3. Precise limitation

The packet `(RBR1)--(RBR6)` still has an exact finite Pauli realization.
On a nontrivial central character sector it is the two-qubit Weyl table, and
`w` acts by a finite Clifford normalizer that routes its two labels.  Hence
these relations alone cannot identify the source character with one of the
many extension characters created by the proper compressor map.

The remaining synchronization problem is now strictly external to the
local branch packet:

> Show that the comb compressor transports the source character PVM to the
> extension-character PVM in a way for which the raw routing label in
> `(RBR4)` is a deterministic function of the source atom, with vanishing
> total normalized-HS error.

Once this is proved, the character-to-map coarsening theorem turns the
routing labels into whole response maps, variable-rank averaging removes
rank selection, tree gluing produces a common latent law, and the robust
paired-quotient floor gives the contradiction.

This also rules out another unproductive search: no additional local
Steinberg commutator is needed merely to reveal the cross-zero branch.  A
successful new word must couple `(RBR4)` to the compressor extension fibers;
remaining inside the finite routed Pauli packet is sterile.

