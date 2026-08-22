---
rg: 2
id: balanced-occurrences-have-linear-character-decoder
kind: claim
title: Globally commuting balanced occurrences admit a linear same-Hilbert character decoder
distinct_from:
  damped-cloud-face-return-has-an-exact-scalar-fixed-sheet: that refutes every independent sign-preserving face return on an inconsistent scalar sheet; this chooses one code character globally on each common spectral atom and therefore moves the whole sheet coherently.
  bounded-type-balanced-occurrences-synchronize: that treats noncommuting occurrence algebras of every fixed irreducible type with an unspecified compactness modulus; this gives an explicit linear modulus for arbitrary-dimensional abelian occurrence algebras.
  central-clifford-parity-sectors-round-uniformly: that permits noncommuting reflections with central scalar commutators; this assumes literal global commutation but allows arbitrary scalar direct integrals and does not use complete-pair energy.
---

ESTABLISHED.  Let `H:F_2^L->F_2^M` be a bounded-row, bounded-column
binary LTC family with

```text
 dist(y,ker H)/L <=sigma^(-1)|Hy|/M.                    (GCD1)
```

Use the balanced repeated occurrence presentation.  Write
`lambda_(i,v)` for the stationary probability within cloud `i` and choose
cloud weights `nu_i` with `sum_i nu_i=1` and
`c/L<=nu_i<=C/L`.  The equality edge law in cloud `i` is reversible with
stationary law `lambda_(i,-)` and Markov gap at least `lambda>0`.  The
normalized law on repeated original faces is compatible with the cloud law
in the following precise sense: for every nonnegative occurrence function
`x`,

```text
 E_(h original) E_(t repeat of h)
       sum_(i in supp h)x_(i,h,t)
 <=C_inc sum_i nu_i sum_v lambda_(i,v)x_(i,v).          (GCD0)
```

Here `(i,h,t)` denotes the corresponding vertex `v` of cloud `i`.  Uniform
face and occurrence weights in the regular balanced overlay satisfy
`(GCD0)`: every original row is repeated `Theta(M)` times, the original
layer has constant total weight, and each cloud has `Theta(M)` original and
redundant occurrences of comparable weights.

Let `(A_(i,v))` be reflections in a finite tracial von Neumann algebra and
assume that **all** occurrence reflections commute globally.  No parity
relation is assumed exact.  Normalize the defects by

```text
 E_eq=sum_i nu_i E_((u,v) equality edge i)
                   ||A_(i,u)-A_(i,v)||_2^2,
 E_orig=E_(h original)E_(t repeat of h)
                   ||prod_(i in supp h)A_(i,h,t)-I||_2^2.       (GCD0a)
```

Then there is, in the same abelian occurrence algebra, a joint PVM
`(P_c)_(c in ker H)` and commuting code reflections

```text
 S_i=sum_(c in ker H)(-1)^(c_i)P_c                     (GCD2)
```

such that

```text
 sum_i nu_i sum_(v in cloud i)lambda_(i,v)
       ||A_(i,v)-S_i||_2^2
 <=C(E_eq+E_orig).                                      (GCD3)
```

The constant depends only on `sigma,lambda` and the fixed incidence and
weight-comparability constants.  It is independent of `L`, matrix
dimension, the number of scalar atoms, and their trace weights.  Replacing
every occurrence by `S_i` makes the equality and every original or
redundant parity face exact.  Every bounded face PVM is then reconstructed
from these marginals with the same linear modulus.

There is a useful basin form.  For an arbitrary occurrence-reflection tuple
`Q`, let

```text
 d_ab(Q)^2=inf_A sum_(i,v)nu_i lambda_(i,v)
                    ||Q_(i,v)-A_(i,v)||_2^2,            (GCD4)
```

where the infimum is over globally commuting occurrence-reflection tuples
on the same Hilbert space, with no parity constraint.  Fixed-width
telescoping of the equality and original parity words, followed by `(GCD3)`,
gives

```text
 d_code(Q)^2<=C(E_eq(Q)+E_orig(Q)+d_ab(Q)^2).           (GCD5)
```

Here `d_code` is the same weighted occurrence distance as `(GCD4)`, with
the infimum restricted to tuples obtained from a joint PVM on `ker H` as in
`(GCD2)`.

Thus a far small-defect countersequence must remain a constant distance
from **every** common abelian occurrence algebra; merely having large
generated-algebra type is irrelevant.

In particular, the scalar fixed sheets in
`damped-cloud-face-return-has-an-exact-scalar-fixed-sheet`, including
arbitrary small-trace direct sums of them, are corrected at cost bounded by
their equality energy.  Their stationarity is a fence only against
facewise sign-preserving return maps, not against a globally coordinated
character decoder.

The global-commutation hypothesis is load-bearing.  Sparse Clifford cycles
and their direct-sum symmetrizations have no common scalar spectral space
on which the pointwise majority below can be performed.  The theorem
therefore does not infer an abelian table from small average commutators and
does not weaken `averaged-commutators-do-not-give-abelian-table`.  The open
shared-face theorem must first manufacture, or converge to, this common
abelian spectral space on the genuinely noncentral unbounded-type sector.

Without `(GCD0)` the displayed conclusion is false as stated, even for two
scalar coordinates.  Take `H=(1,1)`.  In each cloud use two vertices
`v_0,v_1` with stationary weights `epsilon,1-epsilon`; let the sole original
face use the two `v_0` occurrences.  A lazy reversible two-state chain with

```text
 P(v_0,v_1)=1/2,
 P(v_1,v_0)=epsilon/(2(1-epsilon))
```

has this stationary law, bounded degree, and Poincare gap at least `1/2`.
Put the scalar signs

```text
 (A_(1,v_0),A_(1,v_1))=(-1,+1),
 (A_(2,v_0),A_(2,v_1))=(-1,-1).                       (GCD6)
```

The face product is exact, while for `nu_1=nu_2=1/2` the equality energy is
`2 epsilon` under the ordered stationary edge convention.  But the only
scalar code characters are `(+1,+1)` and `(-1,-1)`, and the weighted square
distance to either is at least `2(1-epsilon)`.  Thus no uniform version of
`(GCD3)` follows from bounded degree and a cloud spectral gap alone.  The
example violates `(GCD0)` because the face layer is concentrated on the
vertices of stationary mass `epsilon`.
