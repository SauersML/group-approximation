---
rg: 2
id: diagonal-difference-shift-propagates-pauli-incidence
kind: claim
title: The diagonal difference shift propagates Fanizza--Pauli incidence without identifying the two clocks
artifacts:
  - research/artifacts/diagonal-covariant-pauli-incidence-and-constant-depth-audit-2026-08-21.md
distinct_from:
  diagonal-covariance-synchronizes-hnn-and-bcs-shifts: that synchronizes conjugates of a finite BCS word menu; this also propagates cross-commutation with every Toeplitz-addressed coordinate Pauli.
  toeplitz-coordinate-paulis-localize-cells-and-grams: that proves the analytic Pauli Reynolds estimate once the cross-commutators are available; this supplies those commutators by finite ordinary group relations and preserves an exact marked model.
---

Let `t` be the Toeplitz stable letter, let `U` be the distinct Fanizza shift,
and put `c=tU^(-1)`.  Let `A` be a finite menu of base Toeplitz Pauli seeds
and let `Z` be a finite menu containing every base C18 selector/reset word
used to form the Fanizza projections.  Add the finite relations

```text
[t,U]=1,       [U,a]=1,       [c,z]=1,       [z,a]=1
                         (a in A, z in Z).                 (DPI1)
```

For

```text
a_i=t^i a t^(-i),             z_j=U^j z U^(-j),            (DPI2)
```

one then has, exactly,

```text
[U,a_i]=1,                    [z_j,a_i]=1                  (DPI3)
```

for every `i,j>=0`.  Indeed `[t,U]=1` makes `c` commute with both `t` and
`U`, while `[U,a]=1` gives

```text
a_i=c^i a c^(-i).                                             (DPI4)
```

The word `z_j` commutes with `c` by `[c,z]=1` and `[c,U]=1`, and it
commutes with `a` by `[z,a]=[U,a]=1`; this proves the second relation in
`(DPI3)`.  The first follows from `(DPI4)`.

The proof uses only conjugation and commutator collection.  Together with
`diagonal-covariance-has-quadratic-hs-word-cost`, its level-`i,j` relators
have polynomial derivation area, hence polynomial normalized-HS loss.  If
`E,H` are formed from the shifted C18/reset menu, `(DPI3)` supplies the
support commutations required by
`toeplitz-coordinate-paulis-localize-cells-and-grams`.  For
`X=(E-H)UE` and `q=E-X^*X`, the latter therefore places `q` polynomially
close to the old-spin commutant.

The added relations retain the standard exact marked model:

```text
h |-> pi_T(h) tensor I,
a |-> pi_T(a) tensor I,
z,U |-> I tensor pi_B(z), I tensor pi_B(U),
t |-> pi_T(t) tensor pi_B(U).                              (DPI5)
```

Here `c` acts as `pi_T(t) tensor I`, so every relation in `(DPI1)` is
exact, and a nontrivial marked BCS word remains nontrivial.  Thus the
same-carrier Pauli **incidence syntax** does not require `t=U` and is no
longer an open part of the Toeplitz--Schur amalgam.  This result supplies no
one-sided Schur multiplicity current and no absorbing contraction.
