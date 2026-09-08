---
rg: 2
id: binary-jacobson-rank-two-dichotomy-proof
kind: route
title: Rerun the symbol, simplicity and centralizer arguments with two outer rows
target: binary-jacobson-mark-dichotomy-holds-from-rank-two
requires:
  - two-outer-rows-suffice-for-finitary-transvections
  - laurent-elementary-groups-are-residually-finite
  - jacobson-shift-representation-is-faithful
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

**Exactness.**  The third prerequisite gives the ring sequence
`0 -> M_fin(N,F_2) -> J -> F_2[z,z^(-1)] -> 0` and faithfulness of the
shift action, so `G_n` acts faithfully on `V^n`, `V = (+)_(k>=0) F_2 e_k`.
Surjectivity of `G_n -> Q_0^(n)` holds by lifting the coefficients of
elementary generators.  An element of the kernel has trivial symbol, so
differs from the identity by a finite-support matrix, hence lies in
`L_n`.  Conversely the first prerequisite shows every finitary
transvection lies in `G_n` already for `n = 2`, and those generate `L_n`;
each is in the kernel because `Q` has zero symbol.  So the kernel is
exactly `L_n`, and it is normal.

**Simplicity of `L_n`.**  Let `1 != g` lie in a normal subgroup of `L_n`
and fix a finite coordinate subspace containing the support of `g`.
Choose `v` with `(g - I)v != 0` inside it and a fresh coordinate `k`
outside it, and put `u = I + v e_k^*`, an element of `L_n`.  Since `g`
fixes `e_k` and the functional `e_k^*`,

```text
[g,u] = I + (g - I)v e_k^*                                        (1)
```
is a nonidentity transvection lying in the normal subgroup.  A finite
change of basis conjugates it to any prescribed elementary transvection,
and over `F_2` every finite invertible change of basis has determinant
one, so it stays inside `L_n`.  Those transvections generate `L_n`, so
the normal subgroup is everything.  `L_n` is infinite because the
coordinate set is.

**Self-centralizing.**  An invertible operator commuting with every
finitary transvection commutes with every off-diagonal matrix unit;
evaluating on basis vectors forces all off-diagonal coefficients to
vanish and all diagonal coefficients to agree, so it is scalar.  Over
`F_2` the only invertible scalar is `1`.  Hence `C_(G_n)(L_n) = 1`.

**Faithful mark.**  Let `phi : G_n -> D` retain some `1 != c in L_n`.
Then `ker(phi) cap L_n` is a proper normal subgroup of the simple group
`L_n`, so trivial.  For `k in ker(phi)`, normality of `L_n` gives
`[k, L_n] <= ker(phi) cap L_n = 1`, so `k in C_(G_n)(L_n) = 1`.  Thus
`phi` is injective.  `w_n = e_12(Q)` is such a `c`, being the
transvection `Q_(00)` in the `(1,2)` position.

**Radical dichotomy.**  The second prerequisite makes `Q_0^(n)`
residually finite, hence MF, so the symbol map is an MF-target
homomorphism with kernel `L_n` and `Rad_MF(G_n) <= L_n`.  The MF radical
is normal in `G_n`, so its intersection with the simple `L_n` is `1` or
`L_n`; since it already lies inside `L_n`, it equals one of them.  If it
is `1` then, `G_n` being countable, enumerating nonidentity elements,
choosing an MF-target map separating each and forming block-diagonal
matrix models gives one faithful norm-corona model, so `G_n` is
operator-MF; conversely an operator-MF group has trivial radical.  If it
is `L_n`, every MF-target map kills `L_n` and factors through `Q_0^(n)`.
This is `(JR3)`.
