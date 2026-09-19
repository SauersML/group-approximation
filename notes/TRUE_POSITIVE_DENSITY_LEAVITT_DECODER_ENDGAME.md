# Positive density removes corner renormalization from the Leavitt decoder

Date: 2026-08-14

## 1. Outcome

The finite-multiplicity Leavitt decoder can be stated more weakly than in the
usual normalized-corner formulation.  A merely nonzero decoded corner would
not be enough: its normalized Hilbert--Schmidt norm rescales ambient error by
the inverse square root of the corner trace.  The atlas Pauli packet avoids
this problem because its relevant corners have fixed positive canonical
trace.

Let `M_d(C)` have normalized trace `tau_d`, let `p` be a nonzero projection,
and put

```text
alpha=tau_d(p)=rank(p)/d.
```

For every `X in p M_d(C) p`, the normalized corner trace
`tau_p(X)=tau_d(X)/alpha` gives the exact identity

```text
||X||_(2,p)=alpha^(-1/2)||X||_(2,d).                  (PDL1)
```

Suppose `T_0,S_0,T_1,S_1` are contractions in `p M_d(C) p`, whose unit is
`p`.  Applying the already formalized multiplicative Leavitt floor in the
corner and then `(PDL1)` gives

```text
max {
  ||T_0 S_0-p||_(2,d),
  ||T_1 S_1-p||_(2,d),
  ||T_0 S_1||_(2,d)
}
  >=sqrt(alpha)(2-sqrt(3)).                           (PDL2)
```

Thus a sequence of such packets with `alpha_n -> alpha>0` cannot have all
three **ambient** normalized-HS defects tend to zero.  More precisely,

```text
liminf max ambient defect >=sqrt(alpha)(2-sqrt(3)).  (PDL3)
```

For the trace-`1/8` initial Pauli cut in the existing atlas packet, this is

```text
(2-sqrt(3))/sqrt(8)>0.                               (PDL4)
```

For a trace-`1/4` carrier the corresponding floor is
`(2-sqrt(3))/2`.

## 2. Correct decoder statement

The terminal extraction theorem therefore need not promise normalized
relations on an unspecified nonzero corner.  It is enough to prove the
following ambient statement.

> **Fixed-density ambient Leavitt decoder.**  From a trace-preserving atlas
> microstate of defect `delta_n -> 0`, recover exact projections `p_n` and
> four `p_n`-corner contractions such that
>
> ```text
> tau(p_n)->1/8
> ```
>
> and the three ambient normalized-HS defects in `(PDL2)` tend to zero.

The exact finite Pauli subgroup already supplies the projection and its
trace after finite-subgroup exactification.  The only new content is the
common-coordinate coefficient extraction producing the four contractions
and the three ambient product estimates.  No minimum rank of individual
character fibers and no separate corner-error normalization are required.

Conversely, if a proposed decoder only produces corners with
`tau(p_n)->0`, then ambient error `epsilon_n` becomes normalized corner error
`epsilon_n/sqrt(tau(p_n))`.  Such a decoder closes the proof only with the
additional quantitative condition

```text
epsilon_n=o(sqrt(tau(p_n))).                          (PDL5)
```

Calling the corner merely nonzero hides precisely this requirement.

## 3. Relation to the two current endpoints

This density bookkeeping makes the fixed Pauli route preferable to a
growing Heisenberg-sector extraction whenever both are available.

1. The Pauli packet has a fixed finite type and canonical trace `1/8`, so
   `(PDL2)` converts ambient microstate control directly into a uniform
   contradiction.
2. A *single selected* growing central-character sector may have vanishing
   weight.  Selecting one therefore needs either a positive-mass theorem or
   the stronger rate `(PDL5)`.  This selection can be avoided: the sum of all
   root characters with `ell(1)=1` is the trace-`1/2` negative phase sector,
   and blockwise radical-quotient decoders can be aggregated there.  See
   `TRUE_NEGATIVE_CHARACTER_SECTOR_AGGREGATION.md`.
3. The fixed `3/28` binary-algebra distance floor is even less demanding if
   one can prove membership of the transported carrier in the parent binary
   algebra.  The four-contraction decoder remains the fallback when that
   membership estimate is too strong.

Accordingly the live theorem is not the terminal matrix inequality, which
is complete.  It is the finite-coordinate synchronization statement on the
already positive-density Pauli coefficient packet.

## 4. Formal support

The local normalized-corner inequality is kernel-represented in
`GroupApproximation/Sofic/LeavittTraceFloor.lean` as
`two_sub_sqrt_three_le_of_leavitt_product_defects` and
`two_sub_sqrt_three_le_max_leavitt_product_hsNorm`.  Equation `(PDL1)` is the
definition of the normalized trace on a matrix corner.  The present note
does not assert the still-missing coordinate decoder and no build or local
computation was run.
