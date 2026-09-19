---
rg: 2
id: atlas-root-triangle-heisenberg-proof
kind: route
title: Intersect one root subgroup with its same-source and same-target neighbors
target: atlas-root-triangle-is-heisenberg-character-fibers
requires:
  - atlas-steinberg-rank-five-translation
---

The deterministic dictionary gives the three coefficient-one matrices in
`(HTF2)`.  Direct multiplication over `F_2` gives

```text
[I+E_32,I+E_24]=I+E_34,
```

and the last transvection is central in the generated upper-unitriangular
three-coordinate group.  This proves `(HTF3)` and identifies `H` with `D8`.

For each coefficient letter `a`, the packet entries used are precisely

```text
root_12_ab,              a!=b,
inv_12_a, inv_15_a, inv_52_a,
orth_12_15_ab,
orth_12_52_ab,
st3_152_a1,
st3_152_1a.                                      (HTP1)
```

The first line of `(HTP1)` makes the `C_a` commute, the involutivity entries
make the three families self-adjoint involutions, and the two orthogonal-root
families put every `C_a` in the commutants of both `X` and `Y`.  The two
Steinberg families are exactly `(HTF5)`.  The same orthogonal-root rows with
arbitrary second coefficient show that `X_a,Y_a` commute with all `C_b`.
This proves `(HTF4)`--`(HTF7)`.

For `(HTF8)`, left multiplication restricts from `A8` to `H` as `2520`
copies of the regular representation of `H`.  The complex group algebra of
`D8` is

```text
C[D8] ~= C^4 direct-sum M_2(C).
```

Taking the commutant of the left regular representation and amplifying by
`C^r` gives four copies of `M_(2520r)` and one copy of `M_(5040r)`.  The
commutator `Z` is `+1` in every one-dimensional representation and `-I` in
the unique two-dimensional representation, proving the final assertion about
`chi_1`.

All arguments are finite word identities.  For a vanishing microstate
sequence they hold exactly after passage to the tracial ultraproduct.  The
representative-level formulation follows from normalized-HS stability of a
fixed finite commuting-involution packet and from the trace-preserving finite
group average

```text
T |-> |H|^(-1) sum_(h in H) lambda(h) T lambda(h)^*.
```
