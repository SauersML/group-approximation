---
rg: 2
id: stw99-lxxvi-first-factor-order-cofinality-proof
kind: route
title: Convert finite ideal generation into one Cu-image dominator
target: stw99-lxxvi-first-factor-cu-image-is-order-cofinal
requires: []
---

Stabilize throughout.  Let `x=[c] in Cu(C)` and fix `x'<<x`.  Choose
`epsilon>0` such that

```text
x'<=[(c-epsilon)_+].                                     (P1)
```

Fullness of `phi` says that the positive cone of `C tensor K` is the norm
closure of finite sums

```text
h=sum_(j=1)^N z_j* phi(a_j) z_j,
```

with `a_j in (A tensor K)_+` and multiplier-compatible rectangular `z_j`.
Choose such an `h` close enough to `c` that the perturbation lemma gives

```text
x'<=[(c-epsilon)_+]<=[h].                               (P2)
```

Put `w_j=phi(a_j)^(1/2)z_j` and let `W` be the column with entries `w_j`.
Then `h=W*W`, while

```text
WW*=D Z Z* D <= ||Z||^2 D^2,
D=diag(phi(a_1)^(1/2),...,phi(a_N)^(1/2)).              (P3)
```

The elements `W*W` and `WW*` have the same Cuntz class, and `(P3)` makes
`WW*` Cuntz below `diag(phi(a_1),...,phi(a_N))`.  Therefore, with

```text
y=[a_1]+...+[a_N] in Cu(A),
```

equations `(P2)--(P3)` prove `(OC1)`.

For the global assertion, choose a rapidly increasing sequence
`x_1<<x_2<<...` with supremum `x`.  Apply `(OC1)` to obtain
`x_n<=Cu(phi)(y_n)`.  The partial sums `s_n=y_1+...+y_n` increase in
`Cu(A)`; set `y=sup_n s_n`.  Since a Cu-morphism preserves addition and
increasing suprema,

```text
x=sup_n x_n <= sup_n Cu(phi)(s_n)=Cu(phi)(y),
```

which proves `(OC2)` for every full `phi`.

For completeness, the unital first-factor map is full.  Its generated ideal
contains every elementary tensor with positive first coefficient, since

```text
a tensor b=(a^(1/2) tensor 1_B)(a^(1/2) tensor b),
```

and their linear span is dense in `A tensor_min B`.

Now specialize to `phi=iota`, `B=Z`, and separable `A`.  Let `J=Ideal(c)` in
`A tensor_min Z`.  The ideal correspondence gives a unique ideal `I` of
`A` with

```text
J=I tensor_min Z.                                        (P4)
```

The restricted first-factor map `I->I tensor_min Z=J` is full.  Apply the
already proved local theorem to this restricted map.  It gives
`y in Cu(I)` with `x'<=Cu(iota)(y)`, so the image ideal is contained in
`J=Ideal(x)`.  This proves `(OC3)` without choosing coefficients outside the
correct ideal.

For the ideal-matched global assertion, repeat the rapidly increasing
construction for `x`, applying the ideal-local result to every `x_n<<x`.
All resulting `y_n` belong to the same source ideal `I` corresponding to
`Ideal(x)`.  Put `s_n=y_1+...+y_n` and `y=sup_n s_n`.  Then `y` belongs to
`Cu(I)`, so
`Ideal(Cu(iota)(y))` is contained in `Ideal(x)`.  The reverse inclusion
follows from `x<=Cu(iota)(y)`, proving `(OC4)`.

**Trust boundary.**  The proof places an image element above a compactly
contained window, and then above the whole class by a countable sum.  In the
`Z` case it can keep that element in the correct closed ideal, but not in the
hereditary subalgebra of `x`.  It does not reflect comparison and does not
approach surjectivity.
