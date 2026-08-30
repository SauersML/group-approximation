# STW Problem XCIV: prime dimension-drop audit (2026-08-30)

## Source and exact imported theorem

The definition of separable `D`-stability used here is the one in footnote 21
of Schafhauser--Tikuisis--White,
[*Nuclear C\*-algebras: 99 problems*](https://arxiv.org/html/2506.10902v2):
every separable subset must lie in a separable `D`-stable subalgebra.

The compatibility issue in the new route was checked against the precise
standard theorem.  Toms--Winter,
[*Z-stable ASH algebras*](https://www.math.purdue.edu/~atoms/zash.pdf),
Proposition 2.2, takes a strongly self-absorbing, `K_1`-injective algebra `D`
written as the closure of an increasing union of nuclear subalgebras `D_i`.
For a separable `A`, it assumes only a unital homomorphism

```text
D_i -> Q(M(A)) intersect A'
```

for each `i` and concludes `D`-absorption.  The homomorphisms are not assumed
compatible; the proof extends lifts to `D` and diagonalizes them.  Apply this
with `D=Z`, `A=C` unital, and
`Q(M(C))=C_infinity`.  The same paper recalls immediately after Proposition
2.2 that `Z` may be written as an increasing union of nuclear prime
dimension-drop stages.  This is exactly the strength used in the route.

Two block facts were also checked.  Rordam--Winter,
[*The Jiang--Su algebra revisited*](https://arxiv.org/abs/0801.2259),
Proposition 3.3, proves that `Z_(p,q)` embeds unitally into `Z` whenever
`p,q` are relatively prime supernatural numbers, hence in particular for
finite consecutive `p=k,q=k+1`.  Conversely, for finite coprime `p,q`, choose
positive `r,s` with `sq-rp=1`; matrix amplification gives

```text
Z_(p,q) -> Z_(rp,sq)=I_(rp).
```

Therefore independent central embeddings of all `I_k` supply the individual
stage embeddings required by Toms--Winter.  No compatible family of the
`I_k` embeddings is asserted or needed.

## Audit against the existing XCIV graph

All XCIV claims and routes were searched before adding this node.  The
closest established claim,
`stw99-xciv-separable-zstability-iff-local-norm-central-z`, requires an
actual homomorphism from the whole infinite-dimensional algebra `Z` for each
finite test.  The new equivalence replaces that demand by an actual
homomorphism from one fixed finitely generated block `I_k` at a time.  Its
reverse proof is not a restriction of the old recursive construction:
different stages use different blocks and Toms--Winter's diagonal theorem
supplies the missing compatibility only after passage to the separable hull's
central sequence algebra.

The matrix-tower theorem is a sufficient positive subclass based on a
coherent AF tower and uniform Bratteli multiplicities.  No such tower occurs
here.  The finite norm-spectral-gap claim is only a sufficient negative
certificate forcing all approximately central elements to be nearly scalar.
The new lower bound against homomorphisms `I_k->B` is instead the exact
logical obstruction, and may hold without a scalar spectral-gap inequality.
The CAR-seed and property-(SI) routes use exact relative commutants and
tracial ultrapowers, respectively, and do not duplicate this criterion.

## Norm boundary and open root

Every approximation in the construction is in operator norm.  The diagonal
tests include dense subsets of every newly generated algebra, so the result
is a separable `Z`-stable hull containing the prescribed separable seed, not
a claim that the nonseparable ambient algebra itself absorbs `Z`.
Hyperfiniteness of `R` supplies `2`-norm finite-dimensional approximation,
but it does not verify the finite operator-norm commutator estimates for
`I_k`.  Thus the unrestricted Problem XCIV remains open.
