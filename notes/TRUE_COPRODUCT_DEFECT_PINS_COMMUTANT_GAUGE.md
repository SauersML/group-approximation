# A coproduct defect pins the commutant gauge

Date: 2026-08-14

## 1. Outcome

The arbitrary commutant unitary in the finite regular-envelope model is not
an irreducible obstruction. Once that unitary satisfies the appropriate
coproduct identity, its gauge freedom becomes classical.

There are two precise statements.

1. In multiplicity one, the distance to the nearest right translation is at
   most the group-like coproduct defect, with constant one and no dependence
   on the order of the finite group.
2. With an arbitrary finite multiplicity algebra, an exact group-like
   coproduct identity makes the coefficients an orthogonal projection-valued
   partition. Thus the gauge is a direct sum of ordinary right translations,
   rather than an entrywise family of unrelated unitaries.

This does not yet prove nonhyperlinearity. It sharpens the remaining
four-root interface: the task is to identify the four-root word average with
the coproduct defect of the actual commutant gauge. Once that identification
is made, no separate gauge-fixing theorem is needed.

## 2. Multiplicity-one stability with constant one

Let `K` be a finite group, let `(lambda_g)_(g in K)` be its right regular
unitaries, and use the normalized group trace. Write a unitary in the group
algebra as

```text
C=sum_(g in K) c_g lambda_g,
sum_g |c_g|^2=1.                                      (CGP1)
```

For the group coproduct

```text
Delta(lambda_g)=lambda_g tensor lambda_g,             (CGP2)
```

orthogonality of the regular basis gives

```text
epsilon^2
 :=||Delta(C)-C tensor C||_2^2
  =2-2 Re sum_g |c_g|^2 c_g.                          (CGP3)
```

Choose `h` maximizing `Re(c_h)`. Since the numbers `|c_g|^2` are
nonnegative and sum to one,

```text
Re(c_h) >= sum_g |c_g|^2 Re(c_g)
          =1-epsilon^2/2.                             (CGP4)
```

The regular basis is orthonormal, so

```text
||C-lambda_h||_2^2
 =2-2 Re(c_h)
 <=epsilon^2.                                         (CGP5)
```

Hence

```text
boxed(min_h ||C-lambda_h||_2
      <=||Delta(C)-C tensor C||_2).                   (CGP6)
```

The estimate is uniform in `|K|`. In particular, a growing finite envelope
does not create a table-size loss at this gauge-pinning step.

The weighted-maximum arithmetic behind `(CGP4)--(CGP5)` is formalized
source-first in
`GroupApproximation/Leavitt/RawWordReynoldsGap.lean` as
`exists_scalar_gauge_coefficient_distSq_le_defectSq`. No local build was
run.

## 3. Exact operator-valued classification

Now let `N` be a finite matrix algebra and write

```text
C=sum_(g in K) lambda_g tensor C_g
  in L(K) tensor N.                                   (CGP7)
```

Suppose `C` is unitary and satisfies the exact corepresentation equation

```text
(Delta tensor id)(C)=C_13 C_23.                       (CGP8)
```

Before taking the defect to zero, regular-basis Parseval gives the exact
operator-valued identity

```text
||(Delta tensor id)(C)-C_13 C_23||_2^2
 =sum_g ||C_g-C_g^2||_(2,N)^2
   +sum_(g!=h)||C_g C_h||_(2,N)^2.                    (CGP8a)
```

The tensor-product trace is normalized, but the regular unitaries are an
orthonormal basis, so there is no missing factor of `|K|` in `(CGP8a)`.
This is the operator-valued analogue of `(CGP3)`: the single coproduct
defect is already the *total* idempotence and cross-orthogonality error of
all coefficient blocks.

Comparing regular-basis coefficients in `(CGP8)` gives

```text
C_g^2=C_g,
C_g C_h=0                 (g!=h).                     (CGP9)
```

Each coefficient is a contractive slice of the unitary `C`. A contractive
idempotent on a Hilbert space is an orthogonal projection, so every `C_g` is
a projection. Applying the counit to `(CGP8)` shows that

```text
S=sum_g C_g
```

is both unitary and idempotent; hence `S=1`. Therefore

```text
(C_g)_(g in K) is a PVM and
C=sum_g lambda_g tensor C_g.                          (CGP10)
```

On the range of `C_g`, the gauge is exactly the ordinary right translation
`lambda_g`. Arbitrary multiplicity holonomy has collapsed to a classical
random translation. This is precisely the kind of common holonomy under
which the full-space Fourier contraction gap is invariant.

For a fixed group `K`, the approximate version follows qualitatively by a
tracial-ultraproduct argument: an asymptotically vanishing defect gives the
exact PVM `(CGP10)` in the ultraproduct, and a finite PVM lifts to coordinate
PVMs. More explicitly, if `C_n` has defect tending to zero, the coefficient
families define the projections `(C_g)_omega` in the ultraproduct. Lift that
finite PVM to coordinate PVMs `(P_(g,n))`; then

```text
D_n=sum_g lambda_g tensor P_(g,n)                     (CGP10a)
```

is an exact classical gauge and `||C_n-D_n||_2->0`. Thus for the fixed
four-label Pauli packet the multiplicity dimension causes no loss.

A growing-`K` application needs a total-error PVM-rounding estimate. Mikael
de la Salle's
[orthogonalization theorem](https://arxiv.org/abs/2103.14126) gives the
optimal kind of cardinality-free conclusion once one has a positive POVM:
if `sum a_g=1` and `tau(sum a_g^2)>1-epsilon`, it produces a PVM with total
squared `L2` error below `9 epsilon`. The raw coefficients `C_g` in
`(CGP7)` are not positive, so that theorem cannot be applied without an
additional positivization estimate. The scalar estimate `(CGP6)` already
shows that no such issue occurs in multiplicity one; `(CGP8a)` identifies
the exact total budget available in general.

There is now an intrinsic way to bypass this positivization issue. Given a
source spectral projection `P`, target PVM `(Q_j)`, and actual compressor
matrix `U`, the transition effects `P U*Q_j U P` form a POVM automatically.
Their total non-idempotence is exactly one half of the total commutator
energy of `UPU*` against `(Q_j)`, after converting between ambient and corner
trace. De la Salle then rounds them with ambient total squared error at most
`9/2` times that commutator energy. See
`TRUE_TRANSITION_EFFECTS_REMOVE_THE_POSITIVIZATION_GATE.md`. Thus the growing
application should use intrinsic transition effects rather than attempt to
positivize the arbitrary coefficients in `(CGP7)`.

## 4. What this changes in the four-root program

`TRUE_FOUR_ROOT_ASSOCIATIVITY_HAS_UNIFORM_HS_BUDGET.md` established that the
two parenthesizations

```text
[[x_12(a),x_23(b)],x_34(c)]
and
[x_12(a),[x_23(b),x_34(c)]]                           (CGP11)
```

have normalized mean squared discrepancy at most `900 delta^2`, independent
of the coefficient-table size. The remaining qualification there was that
an arbitrary commutant unitary preserves all group-word relations while it
can alter the proposed coefficient tensor.

The present calculation splits that qualification in two.

* Mere four-root word equality still does not constrain the gauge.
* If the coefficient-identification map sends the averaged four-root
  discrepancy to the genuine defect
  `||(Delta tensor id)(C)-C_13 C_23||_2`, then `(CGP6)` or `(CGP10)` pins the
  gauge automatically.

Thus the missing theorem no longer needs to choose a preferred regular
basis or prove entrywise block coherence directly. It needs one
gauge-covariant Parseval identity, but that identity cannot be derived from
the pure four-root words alone:

> **Coproduct-identification gate.** Construct the coefficient expansion of
> the repaired finite-envelope implementer and prove that its total
> corepresentation defect is the normalized four-root associativity energy,
> up to a dimension-free `o(1)` error.

The `C_2` counterexample in
`FALSE_PURE_FOUR_ROOT_WORDS_CANNOT_PIN_COMPRESSOR_GAUGE.md` shows that the
construction of the coefficient expansion must explicitly use the comb
compressor's compiled source word, or another mixed relator detecting the
compressor gauge. Root covariance and root-only associativity both remain
exact under a nongroup-like commutant deformation, while the coproduct
defect changes.

After that gate, the gauge becomes a PVM of classical translations. The
existing whole-map decoder and robust `1/36` paired-quotient floor, or the
fixed four-label full-space contraction gap, can be applied without an
additional holonomy hypothesis.

## 5. Exact limitation

Equation `(CGP8)` must concern the coefficients of the *actual repaired
implementer*. It is not enough to note that the abstract ring products are
associative. Multiplying an implementer by an arbitrary commutant unitary
leaves every covariance relation unchanged, while its coproduct defect is
generally nonzero. Therefore the map from four-root word evaluations to the
coefficient expansion remains load bearing.

The advance is that this is now the only gauge issue: once the correct
coproduct defect is obtained, finite multiplicity cannot hide an arbitrary
entrywise holonomy.
