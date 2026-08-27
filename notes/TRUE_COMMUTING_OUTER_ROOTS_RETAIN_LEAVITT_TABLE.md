# Commuting outer roots retain the full Leavitt table

Date: 2026-08-14

## 1. Outcome

The adjacent-root realization of the paired-quotient table uses

```text
[x_i0(b t_l),x_0j(s_k a)]=x_ij(delta_lk b a).       (COR1)
```

Its two measured root packets do not commute, so the finite Pauli model
survives. The four-root envelope has an exact alternative in which the two
coefficient packets commute.

For `a,b` in the binary Leavitt algebra, define

```text
X_i(a)=x_12(a t_i),
Y_j(b)=x_34(s_j b),
H=x_23(1).                                           (COR2)
```

The outer root groups `X_12` and `X_34` are in non-addable positions, hence

```text
[X_i(a),Y_j(b)]=1                                   (COR3)
```

for every `i,j,a,b`. Nevertheless the fixed middle root transduces their
coefficient product:

```text
[X_i(a),[H,Y_j(b)]]
 =x_14(a t_i s_j b)
 =x_14(delta_ij a b).                               (COR4)
```

Thus the complete two diagonal-one and two cross-zero identities are visible
through nested commutators while the two outer measurement algebras commute
exactly.

The exact group identities are now stated source-first in
`GroupApproximation/Leavitt/OuterRootLeavittRouting.lean` as

```text
outerRootPackets_commute
outerRoot_middle_nested_commutator
leavitt_outerRoot_nested_00
leavitt_outerRoot_nested_01
leavitt_outerRoot_nested_10
leavitt_outerRoot_nested_11.
```

No local build was run, in accordance with the development constraint.

## 2. Why this is different from bare four-root associativity

`TRUE_FOUR_ROOT_ASSOCIATIVITY_HAS_UNIFORM_HS_BUDGET.md` already records

```text
[[x_12(a),x_23(b)],x_34(c)]
 =[x_12(a),[x_23(b),x_34(c)]]
 =x_14(abc).                                        (COR5)
```

The new use is the specialization `b=1` together with the placement of the
two variable coefficient packets on the **outer** roots. The variables
measured on the left and right now commute before the fixed middle-root
transduction, while `(COR4)` still reads the required coefficient product.
This is precisely the geometry needed by
`TRUE_COMMUTING_TARGET_PACKETS_SYNCHRONIZE_TRANSITIONS.md`.

In a normalized-Hilbert--Schmidt microstate, the fixed-length word telescope
from the four-root note gives a dimension-free defect for every instance of
`(COR4)`. Averaging over a growing coefficient table has no table-size loss.

## 3. Consequence for the live gate

The algebraic placement part of the three-edge PVM program is now closed:
for each of `(R0,L0)`, `(R0,L1)`, `(R1,L1)`, use the corresponding outer
coefficients `a t_i` and `s_j b`. Their target root packets commute exactly,
and the nested word supplies the correct diagonal/crossed product.

The common carrier itself is automatic. The long root `x_14(1)` commutes
with both outer packets and the middle root, so its nontrivial spectral
corner is a common positive-density invariant carrier in a faithful tracial
ultraproduct. See
`TRUE_LONG_ROOT_CARRIER_IS_COMMON_BUT_NOT_A_DECODER.md`.

What remains is a smaller synchronization statement:

> **Proper-compressor outer-root decoder gate.** Show that the compressor
> transitions for `a |-> a t_i` in `X_12` and `b |-> s_j b` in `X_34`
> become asymptotically deterministic response maps on the common long-root
> carrier, and that `(COR4)` makes their labels decode the long-root
> character with vanishing total mismatch.

If this statement holds, single-edge covariance supplies the leakage bounds.
The commuting-target transition theorem gives vanishing edge commutator
energy; path PVM classicalization makes the three edges exactly commuting;
character-to-map coarsening and tree gluing give a common latent law; and the
robust `1/36` paired-quotient floor finishes the contradiction.

The remaining clause is not automatic from the group identity alone. The
left regular representation of `UT_4(F_2)` already realizes the common
trace-`1/2` carrier, commuting outer roots, and the complete nested table,
while retaining a finite Clifford transition. Thus proper-compressor
extension-fiber coherence is the unique operator-coordinate issue in this
route; neither carrier alignment nor growing-outcome rounding remains.
