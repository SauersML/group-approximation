# Audit: real rank zero forces almost divisibility

Date: 2026-08-30

Claims audited:
`perera-rordam-large-matrix-blocks-real-rank-zero` and
`stw27-real-rank-zero-almost-divisibility`.

## Dependency check

The only imported theorem is the Perera--Rordam large-block criterion.  Its
hypotheses are applied to the unital real-rank-zero corner
`p(A tensor K)p`.  Simplicity and non-elementarity rule out every
finite-dimensional representation of that corner.

## Arithmetic check

For `r>=n(n-1)` and `k=floor(r/n)`, write `r=nk+s` with
`0<=s<=n-1`.  Then `k>=n-1>=s`, so

```text
nk <= r <= (n+1)k.
```

Thus a block of rank `r` supplies a divider made from `k` rank-one classes.
The direct-sum unit exactly recovers the corner projection, so summing the
block inequalities loses no class.

## Cuntz-semigroup check

Real rank zero supplies an increasing projection approximate unit in every
sigma-unital hereditary subalgebra.  Its Cuntz classes have supremum the
class of a strictly positive generator of that hereditary algebra.  Hence
`x'<<x` lies below one compact projection class, to which the block argument
applies.  Both almost-divisibility inequalities have the required
orientation.

## Scope check

The argument proves a class theorem, not unrestricted STW Problem XXVII.
No nuclearity or stable rank one enters the divisibility proof.  The
non-type-I assumption is essential for excluding finite-dimensional
corners.  The case `n=1` is handled separately.

## Outcome

The proof is internally complete modulo the explicitly isolated
Perera--Rordam citation and standard permanence/algebraicity facts for real
rank zero. An independent adversarial audit checked the source hypothesis,
corner argument, integer division, projection exhaustion, and strict-
comparison scope. It found one harmless exposition error about killed matrix
summands; that sentence was corrected, and the package passed.
