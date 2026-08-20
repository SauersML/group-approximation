# Schur--Toeplitz root-defect envelope

Date: 2026-08-20

## Exact construction

Fix a Schur packet `B_f` whose predicate has nonempty allowed and forbidden
sets. Over an odd finite splitting field `k`, let `P_f` be the central
idempotent of the forbidden packet summands and define

```text
R_f=k[B_f]*_k k<x,y>/(yx=1, 1-xy=P_f).
```

The packet algebra remains embedded. On a countably infinite faithful packet
module, choose an isomorphism from the whole space to the complement of the
`P_f` range; its inverse, extended by zero on that range, realizes `x,y`.
Thus the relation does not kill the contextual carrier algebraically.

Every finite quotient of `R_f` kills `P_f`, because finite rings are directly
finite. In characteristic `p`, every finite-dimensional unitary
representation of `St_5(R_f)` has finite image on each exponent-`p` root
subgroup. Intersecting the twenty root kernels and taking the generated ideal
produces a finite coefficient quotient. It kills `P_f`, so the explicit root
word `x_12(P_f)` dies in every finite-dimensional unitary representation.
The word itself remains nontrivial, as witnessed in `EL_5(R_f)`.

## Why this is the right coupling

The character-density formula previously left a word-conversion gap:

```text
P_f=2D(Z_C-Z_B)
```

is a finite linear combination, not a group element. Here `P_f` is used as a
coefficient and becomes the literal root element `x_12(P_f)`, while
`P_f=1-xy` gives it a proper-corner orientation. This evades the direct
relator-ideal no-go: `P_f` is nonzero in the ambient ring and disappears only
after passage to directly finite quotients.

## Remaining analytic theorem

The exact kernel intersection depends on matrix dimension. A complete proof
must replace it by a weighted root-character recurrence with a strict
contraction, or by a summable first-hit boundary decomposition. This is
`hs-schur-toeplitz-root-defect-collapse`. It is narrower than full HS
stability: only one named root must collapse. It is nevertheless the entire
nonhyperlinearity endpoint, so no conclusion is claimed before that modulus
is proved.

The canonical boundary candidates are

```text
e_n=x^nP_fy^n.
```

They are pairwise orthogonal idempotents. The root element attached to each
coefficient is a derived word of polynomial cost. Hence a viable proof need
not intersect a dimension-dependent family of kernels: it can charge each
root character at the first boundary coefficient it detects. What is not yet
proved is that the Steinberg multiplication relations transport a fixed
fraction of the `e_0` phase mass to a fresh first-hit layer rather than
allowing the additive-root characters to decouple from coefficient
multiplication.

## Fast falsification checks

1. Removing `yx=1` destroys direct-finite collapse.
2. Taking `P_f=0` or `1` destroys, respectively, the mark or the faithful
   unilateral-shift model.
3. Using characteristic zero destroys the finite root-image argument.
4. Using only packet covariance admits the finite-overgroup countermodels.
5. A forward union bound over root degrees cannot work; the number of kernel
   constraints grows with dimension. The required ledger must be contractive
   or summable.
