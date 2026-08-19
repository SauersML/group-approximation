---
rg: 2
id: kun-thom-clifford-extension-not-weak-mf-via-central-sign
kind: route
title: Recognize the Clifford sign as a displaced-lamp commutator square
target: kun-thom-clifford-extension-not-weak-mf
requires: [central-sign-corona-obstruction]
artifacts:
  - notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md
  - GroupApproximation/Sofic/KazhdanSignCriterion.lean
---

# Recognize the Clifford sign as a displaced-lamp commutator square

A second, shorter derivation of the same claim, observed by `cairn-ce`. Where
`kun-thom-clifford-extension-not-weak-mf-proof` runs the corner cut and the
Kazhdan projection argument by hand, this route just checks that the Clifford
sign satisfies the hypothesis of the already-established general criterion, and
lets that criterion do the analytic work.

Recording both derivations is deliberate: the hand proof is the one written out
in the corpus and is self-contained, while this one connects the result to the
machine-checked criterion in `GroupApproximation/Sofic/KazhdanSignCriterion.lean`
and shows that no new analytic input was ever needed.

## The criterion

`central-sign-corona-obstruction`, verbatim:

> Under one-sided compression of a property-(T) subgroup, if a central
> involution is the square of the commutator of a displaced centralizer element
> with the Kazhdan subgroup, then every homomorphism to a norm matrix corona
> kills that involution.  If it is nontrivial, the ambient group is not MF.

## Verifying the hypothesis

Write `o = Gamma in X = G/Gamma`. The lamp `c_o` is a **centralizer element**:
`Gamma` stabilizes the base coset `o`, so `gamma c_o gamma^(-1) = c_o` for every
`gamma in Gamma`. Its **displacement** by the compressor is `c_(to)`.

Take any `gamma in Gamma` with `gamma t Gamma != t Gamma`, which exists exactly
because the compression `t Gamma t^(-1) < Gamma` is strict — the same choice the
hand proof makes. With the commutator convention `[a,b] = a b a^(-1) b^(-1)`,
and using that every lamp is an involution,

```text
[c_(to), gamma] = c_(to) · gamma c_(to)^(-1) gamma^(-1)
                = c_(to) c_(gamma t o).
```

Now square it, applying the Clifford relation `c_x c_y = z c_y c_x` at the
distinct sites `x = gamma t o` and `y = t o`:

```text
([c_(to), gamma])^2 = c_(to) c_(gamma t o) c_(to) c_(gamma t o)
                    = c_(to) · z c_(to) c_(gamma t o) · c_(gamma t o)
                    = z c_(to)^2 c_(gamma t o)^2
                    = z.
```

So `z` is the square of the commutator of a displaced centralizer element with
the Kazhdan subgroup, which is precisely the criterion's hypothesis. Distinctness
of the two sites — the only place strictness is used — is what makes the
Clifford relation apply rather than the trivial commuting case.

## Conclusion

The criterion gives that every homomorphism from the Clifford extension to the
unitary group of a norm matrix corona kills `z`. Since `z != 1` in both the
complete and the sparse Clifford lamp groups, the extension is not weak MF.

## Why this does not make the hand proof redundant

The hand proof is still worth keeping. It exhibits the contradiction concretely
— two lamp unitaries at squared normalized distance `2` against a Kazhdan-fixed
vector at distance `0` — and that concrete form is what makes the category
contrast with the tracial setting legible: the identical corner cut appears in
`clifford-ce-targets-are-equivalent-proof` (Theorem 6, `1 => 2`) and there it is
harmless, because a tracial ultraproduct does not supply the stable finiteness
that the operator-norm corona does. A derivation that black-boxes the criterion
hides exactly that step.
