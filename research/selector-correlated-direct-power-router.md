---
rg: 2
id: selector-correlated-direct-power-router
kind: claim
title: A selector-correlated direct power turns a full truth-table router into one ordinary automorphism
distinct_from:
  hyperoctahedral-balanced-word-truth-table: that constructs the balanced truth word once a selector-labelled router is available; this constructs one finite type in which one fixed automorphism has exactly those selector-labelled packet actions.
  full-conjugation-table-cancels-router-multiplicity: that removes multiplicity after the full conjugation table is supplied; this supplies the table by an ordinary group automorphism on one selected finite-type sum.
  hyperoctahedral-router-interface-for-fanizza: that needs one carrier shared by several noncommuting contexts; this solves one context and identifies failure of the selected carriers to agree as the remaining obstruction.
---

Let `A` be a finite elementary abelian two-group, let `K` be a finite group,
let `rho` be an irreducible unitary representation of `K`, and choose elements

```text
r_a in K,                         a in dual(A).          (SDR1)
```

Put

```text
L=K^(dual(A)) times A.
```

For every `a in dual(A)`, let `sigma_a` be the irreducible representation of
`L` which uses `rho` on the `a`-coordinate of `K^(dual(A))`, is trivial on
the other `K`-coordinates, and uses the character `a` on `A`.  If `q_a` is
its primitive central projection and `q=sum_a q_a`, define

```text
theta((k_b)_b,e)=((r_b k_b r_b^(-1))_b,e).             (SDR2)
```

Then `theta(q_a)=q_a` for every `a`.  In the HNN extension

```text
Gamma=<L,t | t l t^(-1)=theta(l), l in L>,             (SDR3)
```

the selected `q_a`-carrier of an arbitrary unitary representation has

```text
t = rho(r_a) tensor V_a                                (SDR4)
```

for one arbitrary multiplicity unitary `V_a`.  Consequently, if `W(t)` is
any word in `t` and diagonal constants

```text
Delta(k)=(k)_b in K^(dual(A))
```

whose exponent sum in `t` is zero, then

```text
q_a W(t;Delta(k_1),...,Delta(k_s))
 =q_a rho(W(r_a;k_1,...,k_s))                           (SDR5)
```

in every representation, with the right side interpreted on the `rho`
factor.  The multiplicity unitary cancels exactly.

There is also a dimension-independent robust form.  For the complete finite
table of `L`, the finite covariance menu in `(SDR3)`, and a fixed balanced
word `W`, a normalized-Hilbert--Schmidt defect `eta` gives `(SDR5)` with
error at most `C eta`, after replacing the algebraic central projections by
their evaluated Fourier sums.  The constant is computable from the displayed
finite data and is independent of all irreducible multiplicities.

For the hyperoctahedral packet of
`hyperoctahedral-balanced-word-truth-table`, take `r_a=tau_a`.  Then every
Boolean predicate is realized on `q` by one ordinary automorphism and one
balanced word, with no uncontrolled second-layer packet action.  If the
characters and `rho` are rational-valued, as in that signed-permutation
specialization, all `q_a` and `q` lie in the rational group algebra.

## Limitation

The construction is local to one commuting selector group `A`.  For two
contexts whose original selector subgroups do not commute, the corresponding
projections `q_c` live in different finite subgroups and need not agree or
commute.  Taking their product, or identifying the selector copies, would
silently classicalize the original machine relations.  Thus this closes the
selector-dependent full-conjugation-table problem for one context, but does
not by itself prove `fanizza-native-signal-groupification`.  The remaining
problem is precisely a common-carrier or coherent-verifier return across the
finitely many native contexts.

There is a second, independent limitation.  If

```text
R=(r_b)_b in K^(dual(A)),
```

then `theta=Ad(R)` on all of `L`.  Hence `R^(-1)t` is central in `Gamma`, and
every balanced word in `t` and constants from `L` reduces group-theoretically
to the corresponding word with `t` replaced by `R`.  The router therefore
cannot also serve as the regular-normal-form wandering mark.  Any final
compiler must couple this local decoder to a separate proper-edge or coherent
return mechanism; treating `(SDR3)` itself as that mechanism would be a gap.
