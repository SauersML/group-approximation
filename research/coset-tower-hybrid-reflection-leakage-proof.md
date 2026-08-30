---
rg: 2
id: coset-tower-hybrid-reflection-leakage-proof
kind: route
title: Expand the tower compression into its off-diagonal leakage corners
target: coset-tower-hybrid-reflection-pays-exact-payload-leakage
requires: []
---

Put

```text
X_i=(1-E_i)A_iE_i.
```

The summands `E_iA_iE_i` have mutually orthogonal left and right supports.
Consequently `R` is self-adjoint, is a contraction, and PVM orthogonality
gives

```text
R^2=sum_i E_iA_iE_iA_iE_i.
```

Since `A_i^2=1` and `sum_i E_i=1`,

```text
1-R^2
 =sum_i(E_i-E_iA_iE_iA_iE_i)
 =sum_i E_iA_i(1-E_i)A_iE_i
 =sum_i X_i^*X_i.                                    (1)
```

Taking the faithful finite trace in `(1)` proves

```text
tau(1-R^2)=sum_i ||X_i||_2^2.                         (2)
```

Relative to `E_i+(1-E_i)`, the commutator has precisely its two
off-diagonal corners:

```text
[E_i,A_i]=E_iA_i(1-E_i)-(1-E_i)A_iE_i=X_i^*-X_i.
```

Those corners are Hilbert--Schmidt orthogonal and have equal norm, so

```text
||[E_i,A_i]||_2^2=2||X_i||_2^2.                       (3)
```

Equations `(2)--(3)` are `(CTH2)`.  Every term in `(1)` is positive.
Thus `R^2=1` if and only if every `X_i` vanishes.  Since the other
off-diagonal corner is `X_i^*`, this is equivalent to
`[E_i,A_i]=0` for every `i`, proving `(CTH4)`.

For the native-shell consequence, suppose the native lamp reflections
generate a finite tracial von Neumann algebra `M`.  A projection which
reduces every native lamp belongs to

```text
{c_x:x in S}' cap M=M' cap M=Z(M).                    (4)
```

If `M` is a factor, a covariant 42-atom tower has 42 nonzero translates of
equal trace `1/42`, so its atoms cannot lie in `(4)`.  This proves the stated
conditional common-reducing obstruction.  The exact leakage identity itself
uses no factoriality assumption.  In particular, it does not infer that the
canonical shell group is ICC merely from a transitive noncomplete defining
graph.

Finally, `(CTH2)` applies row by row to any proposed Fano hybrid.  A bare
coset PVM supplies none of the commutator equations in its right-hand side.
Thus exact wordization requires either a payload-reducing tower or separate
relations controlling those leakage corners; the identity itself supplies
neither authentication mechanism.
