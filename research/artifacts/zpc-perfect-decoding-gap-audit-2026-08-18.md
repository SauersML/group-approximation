# 2026-08-18 — ZPC compiler audit: perfect decoding is not enough

**Status:** one literature-backed no-go plus the repaired quantitative target.
No nonhyperlinear group is claimed here.

The existing route `zpc-compiler-nonhyperlinear-route` uses the following
step:

```text
no perfect finite-dimensional strategy for L(G)
    => omega^q(L(G)) < 1.
```

That implication is false even for binary linear-system games.

William Slofstra, *The set of quantum correlations is not closed*
(arXiv:1703.08618), constructs a linear-system nonlocal game that has a
perfect strategy in `C_qa`, i.e. as a limit of finite-dimensional quantum
strategies, but no perfect strategy in `C_q` or even `C_qs`.  Therefore its
finite-dimensional quantum value is exactly one although no
finite-dimensional perfect strategy exists.

This is precisely the distinction relevant to hyperlinearity: approximate
representations are allowed to move to increasing dimensions.  A compiler
which only maps **perfect** finite-dimensional output strategies back to
perfect input strategies does not exclude a sequence of output strategies
whose values tend to one.

## Correct quantitative target

For the fixed game `G` supplied by `perfect-zpc-irs-quantum-gap-game`, a
sufficient compiler theorem is:

1. a perfect ZPC-IRS strategy for `G` gives a perfect commuting-operator
   strategy for `L(G)`;
2. there exists `eta>0` such that every finite-dimensional strategy for
   `L(G)` with value at least `1-eta` decodes to a finite-dimensional strategy
   for `G` with value strictly above `1/2`.

Since the source game has `omega*(G)<1/2`, clause 2 forces
`omega^q(L(G)) <= 1-eta`; clause 1 gives `omega^co(L(G))=1`.
The established `perfect-lcs-gap-implies-nonhyperlinear` then applies.

This is a local quantitative soundness theorem, not a new global idea.  The
weighted-algebra machinery of Mastel--Slofstra (arXiv:2404.00926) is the
natural language: their reductions track near-perfect strategy soundness
algebraically, and they explicitly introduce weighted homomorphisms for that
purpose.

## Explicitness

The separate claim `perfect-zpc-irs-quantum-gap-game` is existential: its
undecidability proof forces at least one finite tailored game with the desired
values, but does not identify a concrete input instance realizing the perfect
ZPC-IRS side.  Cairn's primary root says **Exhibit an explicit
non-hyperlinear group**.  A repaired root route must therefore also freeze a
specific game/linear system, or supply an effective selector which names one.
