# Property-(T)-free Leavitt MF collapse: atomic integration audit

Integrated 2026-08-24.  This artifact records how the supplied Atomic
Leavitt Gap / Atomic Morita Return note is represented in the Cairn graph.
It preserves the note's honesty boundary: the finite-matrix endpoints below
are proved, while the literal binary-Leavitt same-atom decoder is open.

## 1. New established endpoint: the Atomic Leavitt Gap

For every nonzero projection `p in M_d(C)`, every `m>=2`, and every
`s_i,t_i in pM_d(C)p`,

```text
m-1
 <= sum_i ||t_i s_i-p||_op
    + ||sum_i s_i t_i-p||_op.                         (1)
```

The proof uses `tau_p=Tr/rank(p)` and cyclicity.  It is independent of the
ambient dimension and of `rank(p)/d`.  In the binary case the maximum of the
three relevant defects is at least `1/3`.

Cairn nodes:

- `atomic-leavitt-gap-on-nonzero-matrix-corner`;
- `atomic-leavitt-gap-on-nonzero-matrix-corner-proof`.

The same nodes record the corona corollary: no nonzero norm-matrix-corona
corner carries an exact Leavitt family.  This is a quantitative
coordinatewise strengthening of the stable-finiteness endpoint.

## 2. New established conditional theorem: Atomic Morita Return

For a finitely presented group `Gamma=<S|R>` and a finite-order word `w`,
AMR prescribes a nontrivial rounded spectral projection `p_U` of `w(U)`
before coefficient operators are selected.  On every nonzero such
projection it requires

```text
||t_i s_i-p_U||_op <= eta(delta),              i=0,1,
||s_0t_0+s_1t_1-p_U||_op <= eta(delta),
eta(delta)->0.                                         (2)
```

The atomic gap makes `(2)` impossible in any surviving corona coordinate.
Thus `w in Rad_MF(Gamma)`; normal generation gives total MF radical.

Cairn nodes:

- `atomic-morita-return-kills-finite-order-mf-mark`;
- `atomic-morita-return-collapse-proof`.

This statement incorporates the note's diagonal-gluing observation.  The
address and finite coefficient window may vary with the coordinate.  There
is no inverse-limit compatibility requirement and no carrier-density
requirement.

## 3. Literal binary-Leavitt frontier

The nontrivial involution is

```text
z=x_13(q),                       q=s_1t_1,
```

in the fixed finite presentation of
`St_20(L_(F_2)(1,2))`.  The prescribed atom is the nontrivial spectral
projection of the rounded `z` coordinate.

The exact open target is now:

- `binary-leavitt-atomic-morita-return`.

Its concrete moving-address attack is:

- `binary-leavitt-three-row-atomic-compiler`;
- `binary-leavitt-atomic-return-via-three-row-compiler`.

The compiler asks for finitely many prototype discrepancy words and a
dimension-independent bound for the two inverse rows and completeness row.
Remote checks must be literal conjugates of the prototypes, so arbitrary
address length is free in operator norm.  The generic implication is
recorded by:

- `bounded-prototype-rows-imply-atomic-morita-return`;
- `bounded-prototype-row-compiler-proof`.

Finally,
`property-t-free-leavitt-via-atomic-morita-return` connects this open leaf to
the top-level goal using
`full-leavitt-idempotent-defect-saturation`.

The failure modes are part of the open nodes, not hidden assumptions:

- separately exact typed packets admit `rectangular-escape`;
- the three-elementary prefix swap does not identify packet identities;
- fixed typed PI and Reynolds data do not recover the prescribed carrier;
- a functorial group-algebra selector would also act in the regular finite
  trace and therefore proves too much;
- normalized-HS leakage can vanish on a carrier where operator leakage is
  exactly one.

## 4. Existing Cairn results reused instead of duplicated

The supplied cyclic rank-product theorem is the general form of
`operator-norm-rank-monodromy-zero`.  That node and its proof were extended
from the constant equation `a^k r=b^k r` to arbitrary rational fractions

```text
alpha_i r_i=beta_(i+1)r_(i+1),
prod_i alpha_i=prod_i beta_i.                          (3)
```

The coarse/fine `1/2` versus `1/4` cycle is its binary specialization.
The one-row version remains
`rank-deficient-return-row-has-operator-norm-one`.

The supplied finite-packet linearity no-go is already subsumed by
`finite-rational-rank-flows-are-fd-dense` and
`finite-corona-dimension-certificate-calculus`.  The former now states the
unnormalized rational-polyhedral cone corollary explicitly: a nonzero real
solution to fixed homogeneous rational multiplicity constraints scales to a
nonzero integer solution.  Hence fixed semisimple packet bookkeeping needs a
nonlinear holonomy/operator return or another integral exit.

The existing selector route remains distinct:

- `opnorm-leavitt-coarse-fine-return-row`;
- `authenticated-coarse-fine-return-forces-mf-collapse`.

It asks for exact `M_2` and `M_4` packets with one identity and a vanishing
support row.  AMR asks for no exact packet systems and instead returns three
coefficient equations on the prescribed root atom.

## 5. Exact self-copy theorem and calibrations

For the Heisenberg law

```text
(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab'),
```

the two Leavitt branch maps

```text
alpha_i(a,b,c)=(a t_i,s_i b,c)
```

are injective, have commuting images, intersect in the central third-root
subgroup, and generate the whole Heisenberg group.  Prefix iteration gives
`2^n` commuting self-copies.  Over a finite coefficient field this
Heisenberg group is locally finite.

Cairn nodes:

- `binary-leavitt-heisenberg-is-orthogonal-central-self-copy`;
- `binary-leavitt-heisenberg-central-self-copy-proof`.

The separate finitary elementary calibration is:

- `orthogonal-root-self-copy-is-mf-compatible`;
- `orthogonal-root-self-copy-mf-calibration-proof`.

It records that `E_fin(F_q)` is locally finite/MF, has two commuting
infinite block copies, has the full Steinberg calculus, and is normally
generated by any nontrivial root.  Therefore the raw slogan

```text
orthogonal self-copy + root calculus + normal generation
```

is false as a non-MF criterion.  Same-atom return is the structural dividing
line.

## 6. Status after integration

Established:

- the `m`-ary atomic operator-norm gap;
- no nonzero Leavitt corner in a norm matrix corona;
- AMR implies MF-radical membership and normal-generation collapse;
- the lossless bounded-prototype compiler implication;
- general cyclic rank-product obstruction;
- fixed rational-linear multiplicity scaling no-go;
- exact orthogonal Heisenberg self-copy and its local-finiteness calibration.

Open:

- return the three binary coefficient rows to the prescribed nonzero
  `x_13(s_1t_1)` spectral atom in the literal binary-Leavitt Steinberg
  presentation;
- concretely, build the bounded three-row prototype compiler.

No node created by this integration claims an unconditional
property-`(T)`-free non-MF group.
