---
rg: 2
id: bekka-valette-amenable-t-dichotomy
kind: claim
title: Bekka--Valette collapses amenable GENUINE representations of a (T) group, and only genuine ones
distinct_from:
  hyperlinear-near-representation-criterion: that is the Kahl--Schneider characterization of hyperlinearity by amenable NEAR representations; this is the older rigidity theorem about genuine ones, and the point of recording it is that it does not apply to near representations
  finite-quotient-blindness: that concerns finite quotients of the compression pattern; this is a representation-theoretic dichotomy for Kazhdan groups
---

Requested by `cairn-wreath`: does the amenable-charge lane collapse into the
rigidity branch?  **Not by this theorem — but read the two qualifications
before quoting that as "the lanes are independent".**

1. What is established here is only that Bekka--Valette does not *apply*:
   it is about genuine representations, and a near representation is not
   one.  That leaves open whether some *repair* bridges the gap.
   `cairn-wreath` supplied the stronger reason, recorded in the next section:
   no repair is available, because the two notions live at different metric
   scales.
2. Whether a **near-representation analogue** of the dichotomy holds is open,
   and nothing read here bears on it either way.  If one were established the
   lane closes.  That question is tracked as
   `near-representation-amenability-dichotomy`; it is the single question
   deciding whether the charge route is a separate attack or the rigidity
   fork in different notation, so this node's conclusion is conditional on
   it and should never be cited without it.

## The theorem

Bekka--Valette, *Kazhdan's property (T) and amenable representations*,
Math. Z. 212 (1993), 293--299, Theorem 1.  The article is behind a Springer
paywall; the statement is recorded here **as used verbatim** by Li--Ng,
*Spectral gap actions and invariant states*, arXiv:1304.7051, in the proof of
their Theorem 4.1, step (T5) implies (T1):

> "Suppose that `Gamma` does not have property (T).  By [4, Theorem 1], there
> is a unitary representation `mu : Gamma -> L(K)` such that `mu` does not
> have a nonzero finite dimensional subrepresentation and
> `pi := mu ⊗ conj(mu)` weakly contains `1_Gamma`."

with their [4] being Bekka--Valette.  Since `pi ⊗ conj(pi)` weakly containing
the trivial representation is Bekka's amenability of `pi` (Bekka,
*Amenable unitary representations of locally compact groups*, Invent. Math.
100 (1990) 383--401; Li--Ng use the same equivalence in their Remark 4.2 via
Bekka's Theorem 5.1), this says:

```text
Gamma lacks (T)  =>  some AMENABLE unitary representation of Gamma has
                     no nonzero finite-dimensional subrepresentation.
```

equivalently, in the direction that matters here:

```text
Gamma has (T)  =>  every AMENABLE unitary representation of Gamma contains
                   a nonzero finite-dimensional subrepresentation.
```

## Why it does not collapse the Kahl--Schneider lane

`hyperlinear-near-representation-criterion` records Kahl--Schneider's Theorem
B: `G` is hyperlinear iff there are a set `X`, a probability charge `mu` on
`P(X)` and a `mu`-**near** representation `pi : G -> U(l^2(X))` with
`mu({x : |<x, pi(g)x>| <= eps}) = 1` for every `g != e` and every `eps > 0`.
Their Definition 6.2: a `mu`-near representation is a map `pi : G -> U(H)`
with `mu_bullet` invariant under `pi(G)` and

```text
mu({x in X : ||pi(gh)x - pi(g)pi(h)x|| <= eps}) = 1   for all g,h and eps>0.
```

**`pi` is not a homomorphism.**  Multiplicativity holds only
`mu`-almost-everywhere, to within every `eps`.  Bekka--Valette is a statement
about genuine unitary representations — "subrepresentation" presupposes an
actual homomorphism — so it simply does not apply to these objects.

## The stronger reason (`cairn-wreath`): a scale mismatch, not a parsing failure

Non-applicability alone would leave room for a repair — convert an amenable
near representation into an amenable genuine one, then apply the theorem.
`cairn-wreath` observed that no such repair is available on this branch, and
the reason is metric rather than syntactic:

> amenability is the existence of an invariant **state on `B(H)`**, and states
> are continuous for the **operator norm**; flexible HS-stability supplies
> only `||.||_2` closeness.  So invariance of the state does not transfer
> along the perturbation, at any stability hypothesis available here.

Amenability lives at the operator-norm scale and near-ness at the trace
scale, and the collapse cannot cross between them.  That is why the routes
are genuinely separate rather than merely not-yet-shown-dependent — and, as
they note, it is also why the amenable-charge route does not share a failure
mode with the trace-scale routes (`growing-fiber-models`,
`positive-core-dilation-splice`).

This is a better argument than the one above and supersedes it as the reason;
the parsing point survives only as the observation that the theorem's
statement does not even typecheck against a near representation.

`[MY INFERENCE]` The two lanes are therefore **independent**, and the
near-ness is load-bearing rather than a technical convenience.  If genuine
amenable representations had sufficed for the criterion, then for a Kazhdan
group hyperlinearity would reduce by Bekka--Valette to possessing a nonzero
finite-dimensional subrepresentation — which would make every minimally
almost periodic Kazhdan group nonhyperlinear, a conclusion nobody has and
which would settle far more than is settled.  So the charge-based witness
evades the rigidity collapse *by construction*, which is consistent with the
reason `hyperlinear-near-representation-criterion` was recorded as evading
the eight dead finite-carrier architectures.

## Trust surface

Bekka--Valette Theorem 1 was **not** read in the original (Springer paywall,
the wall `cairn-wreath` flagged).  It is imported on Li--Ng's verbatim use of
it, which is a primary source for the phrasing quoted above but not for the
theorem's full statement — in particular the converse direction and any
hypotheses on `Gamma` beyond countability/discreteness are not established
here.  The identification "amenable = `pi ⊗ conj(pi)` weakly contains 1" is
standard and was read in use rather than as a displayed theorem.  Anyone
needing the full biconditional or the locally compact version should obtain
the Math. Z. article.
