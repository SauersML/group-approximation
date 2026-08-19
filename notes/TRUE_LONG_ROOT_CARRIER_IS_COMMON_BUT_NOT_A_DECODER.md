# The long-root carrier is common, but it is not a decoder

Date: 2026-08-14

## 1. The common carrier is automatic

In the four-root packet, put

```text
Z(z)=x_14(z),   X(a)=x_12(a),
H(b)=x_23(b),   Y(c)=x_34(c).                       (LRC1)
```

The long root is in a non-addable position with all three other roots, so

```text
[Z(z),X(a)]=[Z(z),H(b)]=[Z(z),Y(c)]=1.              (LRC2)
```

These identities are now stated in
`Leavitt/OuterRootLeavittRouting.lean` as

```text
longRoot_commutes_leftOuter
longRoot_commutes_middle
longRoot_commutes_rightOuter.
```

In characteristic two, `Z(1)` is an involution. In any faithful tracial
ultraproduct representation, `Z(1) !=1`, hence

```text
p=(1-Z(1))/2
```

has strictly positive trace because

```text
||Z(1)-1||_2^2=4 tau(p)>0.                          (LRC3)
```

Equation `(LRC2)` makes `p` an exact common invariant carrier for the two
outer packets and the middle transducer. Thus the common-carrier clause in
`TRUE_COMMUTING_OUTER_ROOTS_RETAIN_LEAVITT_TABLE.md` is algebraic; it does
not require commutant recovery or a matrix-coordinate nesting theorem.

If one works with the usual trace-zero hyperlinear normalization on the
finite packet, `tau(p)=1/2`. Only positive density is needed here.

## 2. Why this still does not decode coefficient multiplication

The finite upper-unitriangular group `UT_4(F_2)` gives an exact guardrail.
Its left regular representation has all of the following simultaneously:

* the long-root negative corner has trace `1/2`;
* the outer root packets commute exactly;
* the middle root preserves the long-root corner; and
* the complete nested diagonal-one/cross-zero table holds exactly.

Therefore no implication of the form

```text
common long-root carrier
 + commuting outer roots
 + nested Leavitt table
 -> multiplication-coherent whole-map decoder              (LRC4)
```

can be valid. The middle root can retain a finite Clifford/Pauli
corepresentation on the carrier. The nested word records the correct phase
without forcing its transition blocks to be deterministic functions of the
outer character atoms.

This is the four-root analogue of the order-32 Pauli countermodel, now with
the apparent carrier issue removed.

## 3. Correct remaining gate

The live theorem is consequently narrower than the common-carrier statement
but stronger than the local nested identity:

> **Proper-compressor outer-root decoder gate.** Across a growing finite
> coefficient window, use the proper comb-compressor covariance and raw
> branch routing to show that the middle-root transition blocks on the
> common long-root carrier are asymptotically deterministic response maps on
> the outer character atoms, with the nested word transferring those maps to
> `ell(a t_i s_j b)` with vanishing total mismatch.

The two outer transition measurements themselves can now be recovered
jointly. In rank five the entire four-root chain lies in the rank-four core,
so one comb compressor acts on the product of the two commuting outer root
groups. Product-group covariance gives one joint extension-character PVM,
whose outer measurements are exact marginals. See
`TRUE_ONE_COMPRESSOR_JOINTLY_RECOVERS_BOTH_OUTER_TRANSITIONS.md`.

Accordingly the remaining content of the decoder gate is the finite-window
endomorphism step: turn a joint pair of complete outer characters into common
finite paired-radical label spaces invariant, up to vanishing error, under
all four one-sided Leavitt maps.

The word **proper-compressor** is load bearing. Every bounded finite
unitriangular/Clifford envelope satisfies all local relations above. The
missing estimate must compare successive many-to-one extension fibers of
the proper coefficient corner map; it cannot be obtained from one finite
four-root packet alone.

Once that decoder is available, all later steps are closed:

```text
proper-compressor outer decoder
 -> whole-map PVMs with vanishing three-edge energies
 -> cardinality-free path classicalization
 -> tree gluing
 -> robust paired-quotient 1/36 contradiction.       (LRC5)
```

No local computation or build was run for this note.
