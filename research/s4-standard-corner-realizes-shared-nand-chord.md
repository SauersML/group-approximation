---
rg: 2
id: s4-standard-corner-realizes-shared-nand-chord
kind: claim
title: The S4 standard corner realizes a shared nonuniform NAND chord
distinct_from:
  two-qubit-clifford-closes-transverse-m2-chord: that is the minimal full-root transverse block and therefore has uniform conditional weight one half; this uses the proper subalgebra M2 plus C and realizes the nonuniform NAND table.
  every-boolean-predicate-has-a-character-free-finite-type-block: that realizes each predicate separately in a selected finite type; this makes several NAND contexts share the same chord involution and gives literal separator-fixing transports.
  full-root-separators-force-uniform-chord: that rules out nonuniform tables when the separators generate a full matrix block; this realizes the sharp proper-multiblock alternative.
---

Let `K=S_4`, let `rho` be its three-dimensional standard representation, and
let `q=z_rho in C[S_4]`.  Thus

```text
q C[S_4]q isomorphic to M_3(C).                         (SNC1)
```

Let `H=S_3<=S_4` be the stabilizer of `4`, let `e_std in C[H]` be the
primitive central idempotent of the two-dimensional standard representation
of `H`, and put

```text
p=q e_std,                 Z=2p-q.                     (SNC2)
```

The restriction is

```text
rho|_H = 1_H direct_sum std_H,                          (SNC3)
```

so `p` has rank two and `q-p` rank one.  For a transposition
`s in H`, put `S_s=q s` and let `u_s in S_4` be the complementary
transposition on the other two letters.  Then `[u_s,s]=1`.  Define

```text
p_s=u_s^(-1) p u_s,             Y_s=2p_s-q.            (SNC4)
```

The two endpoint signs commute and the literal group transport closes the
chord:

```text
[S_s,Y_s]=0,        [q u_s,S_s]=0,
(q u_s) Y_s (q u_s)^*=Z.                                (SNC5)
```

After this separator-preserving transport, the joint spectral atoms of
`(S_s,Z)` have ranks

```text
rank(+,+)=1,       rank(+,-)=1,
rank(-,+)=1,       rank(-,-)=0.                         (SNC6)
```

Thus `(S_s,Z)` is exactly the three-allowed-assignment NAND context (up to
renaming the two signs).  Its chord-plus conditional fractions are

```text
1/2 on the rank-two S_s=+ atom,
1   on the rank-one S_s=- atom,                         (SNC7)
```

so the table is genuinely nonuniform.

Taking `s=(12),(13),(23)` and respectively
`u_s=(34),(24),(14)` gives three NAND contexts with one common chord sign
`Z`, while their private separator signs need not commute.  Every projection
is an explicit finite group-algebra expression and every transport is a
literal element of `S_4`.  Hence this is a concrete finite signed-Hecke block
for a nonuniform incidence star.

The construction is local rather than a no-CE atlas: its canonical corner
trace is finite-dimensional.  What it proves is that neither nonuniform NAND
multiplicities, noncommuting private separators, nor exact group translates
are the first-cycle obstruction.  A global obstruction can begin only when
different such stars prescribe incompatible choices of the rank-two
subgroup-type projection `p` around a cycle.

