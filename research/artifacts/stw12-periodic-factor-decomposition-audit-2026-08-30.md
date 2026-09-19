# STW Problem XII: outer-periodic-factor decomposition audit (2026-08-30)

## Result

Let `B` be unital separable AF, let `C` be unital separable and
AF-embeddable, let `beta` be arbitrary, and let `gamma` be outer-periodic.
Then

```text
(B tensor C) rtimes_(beta tensor gamma) Z
```

is stably finite if and only if it is quasidiagonal if and only if it embeds
in an AF algebra.  Stable finiteness is also equivalent to stable finiteness
of `B rtimes_beta Z`.

When `C` is real-rank-zero AH, Rordam's theorem supplies the standing
AF-embeddability hypothesis and the coefficient `B tensor C` is again
real-rank-zero AH.  This gives a new positive Problem XII subclass.

## Faithfulness audit

There are two different embeddings, and neither is inferred from the other.

1. `B rtimes_beta Z` embeds into the full diagonal crossed product by
   `b |-> b tensor 1` and by sending its implementing unitary to the
   diagonal implementing unitary.  The Fourier expectations intertwine, so
   the map is faithful.  This is what lets stable finiteness of the large
   algebra activate Brown's theorem on the AF factor.
2. The diagonal crossed product embeds into
   `(B rtimes_beta Z) tensor (C rtimes_gamma Z)` by sending its implementing
   unitary to the tensor product of the two factor unitaries.  Applying the
   tensor product of the two coefficient expectations kills every nonzero
   diagonal Fourier mode and is faithful on the coefficient algebra.  The
   map is therefore injective.

The second map is only an embedding into a larger `Z^2`-crossed product; it
is not claimed to be onto.  Amenability of `Z` makes the full/reduced choice
irrelevant.

Brown makes the first factor crossed product AF-embeddable.  The explicit
Floquet theorem makes the outer-periodic second factor crossed product
AF-embeddable.  Tensoring the two AF hosts and composing the diagonal
embedding finishes the construction.  No permanence of AF-embeddability
under extensions or inductive limits is used.

## Degenerate cases

The proof includes `gamma=id` (`n=1`), `beta=id`, finite-dimensional `B` or
`C`, and nontrivial kernels of the corresponding `Z`-actions.
Outer-periodicity is
required only on `gamma`; no power of `beta tensor gamma` need be inner.
Unitality is used exactly once, to obtain the coefficient copy
`b |-> b tensor 1_C` needed to detect `B rtimes_beta Z`.

## Strictly beyond both previous slices

Let

```text
C=A_theta
```

be an irrational rotation algebra.  It is a unital non-AF AT algebra of
real rank zero (`K_1(A_theta)=Z^2`), and its AF-embeddability is the original
Pimsner--Voiculescu irrational-rotation embedding theorem.  Let

```text
B=tensor_(k in Z) M_2
```

and let `beta` be the bilateral tensor shift; take `gamma=id_C`.  The
coefficient `B tensor A_theta` is AH of real rank zero.  It is not AF,
because the Kunneth calculation leaves nonzero `K_1`.  The automorphism
`beta tensor id_C` is outer-aperiodic.  Indeed, if a nonzero power were
implemented by a unitary `u in B tensor A_theta`, approximate `u` by an
element supported on finitely many CAR coordinates, with arbitrary
`A_theta` coefficients.  A matrix projection supported at a coordinate far
outside that finite set then approximately commutes with `u`, whereas the
shifted projection lies at a different tensor coordinate and has norm
distance one from the original.  Taking the approximation error sufficiently
small is a contradiction.

The example is nonvacuous: the bilateral shift preserves the unique CAR
trace and the identity preserves the faithful trace of `A_theta`.  Their
product, composed with the crossed-product expectation, is a faithful trace
on the diagonal crossed product, so that crossed product is stably finite
and the theorem actually embeds it into AF.

Thus this specialization is outside Brown's AF-coefficient theorem and
outside the existing periodic-action theorem simultaneously.  The new
result is a tensor-decomposition theorem, not a reformulation of either
input.

## Primary inputs

* Nathanial P. Brown, *AF Embeddability of Crossed Products of AF Algebras
  by the Integers*, Journal of Functional Analysis 160 (1998), 150--175,
  DOI `10.1006/jfan.1998.3339`.
* The in-repository Floquet construction
  `stw12-periodic-actions-over-af-embeddable-algebras`.
* M. Pimsner and D. Voiculescu, *Imbedding the irrational rotation
  C-star-algebra into an AF-algebra*, Journal of Operator Theory 4 (1980),
  201--210, for the strict example.
* Rordam's Proposition 4.1 AF-embeddability theorem for separable ASH,
  hence AH, algebras, imported at `ah-algebras-are-af-embeddable`.
