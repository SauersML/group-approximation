# Finite-field port assessment for the root `(TT)` theorem

## Decision

Do not delay the binary paper for an all-finite-field theorem. The proposed
upgrade is mathematically plausible, but it is not a local generalization of
the current proof. It requires replacing the main quantitative free-root
engine, not merely changing the order-two fixed-part estimate.

## The local part that generalizes

`RankFourRelativeTT.norm_root03_fixedProjection_le` uses two
characteristic-two facts:

1. the target root lies in the column subgroup;
2. the target root has order two.

For characteristic `p`, iteration of the quasi-cocycle identity along
`1, r, ..., r^(p-1)` should replace the two-term identity. On the column-fixed
subspace every `rho(r)^i` is the identity, so the projected sum is `p` copies
of the fixed component. This should give a bound depending on `p` and the
defect. This is a genuine lemma to prove in a future port, but it is not the
current bottleneck.

## The nonlocal obstruction

The moving-projection estimate depends on the characteristic-two free-root
property `(T)` development, especially:

- `FreeAlgebraDegree.eq_sum_support_wordMonomial`, which uses that every
  nonzero coefficient of `ZMod 2` is exactly `1`;
- degree-bounded decompositions built from unweighted support words;
- the `FreeRootCharacterValuation` Fourier/valuation chain, which is
  specialized throughout to `FreeAlgebra (ZMod 2) X`;
- the control set and its quantitative rank-three estimate in
  `FreeElementaryPropertyT`;
- sign-free transpose/reversal identities used by the second embedded plane.

The coefficient-one lemma is not cosmetic. Over a larger finite field the
same polynomial is a scalar-weighted sum of word monomials, so the present
finite involution/Fourier bookkeeping does not transport verbatim. The
general `eq_sum_support_smul_wordMonomial` lemma exists, but every downstream
character and energy estimate would need to retain and control those scalar
weights.

## Bounded-attempt conclusion

An all-finite-field result needs a new parameterized free-root estimate over a
finite coefficient field, followed by a signed transpose audit and the
order-`p` fixed-projection lemma. That is a coherent sequel, not a wrapper.

The current paper therefore freezes the theorem over `F₂`. It may state the
finite-field extension as an open direction, with the precise obstruction
above, but it must not suggest that only the order-two line remains.
