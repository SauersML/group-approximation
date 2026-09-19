# FFGS local-HS examples: finite-presentation wrapper audit

## Exact source examples

The source is Fournier-Facio--Gerasimova--Spaas, *Local Hilbert--Schmidt
stability*, arXiv:2307.13155v2.

- Corollary 3.18 gives the locally finite examples `A_infty`, `S_infty`, and
  more generally locally virtually nilpotent groups.  The first two are not
  MAP (Example 3.19), but they are not finitely generated.
- Theorems 5.4 and 5.5 give the useful finitely generated examples
  `H=[[T]]'`, for minimal Cantor subshifts: `H` is infinite, simple,
  amenable, LEF, and locally HS-stable.  The paper records uncountably many
  pairwise nonisomorphic such groups.
- Proposition 4.12 and Example 4.13 give the explicit nonamenable examples
  `H x F_2`, still finitely generated and locally HS-stable.
- The introduction also records the alternating-enrichment permanence
  theorem of Dogon--Levit--Vigdorovich, but it does not provide finite
  presentation.

The topological-full-group input in Theorem 5.5 uses the Dudko--Medynets
character classification described there as recently announced.  The
wrapper deductions below are conditional only on the theorem as stated in
FFGS; they do not strengthen that source input.

## Exact wrapper classification

Fix one of the groups `H=[[T]]'`.

### The invisible mark survives every embedding

An infinite simple group has no nontrivial finite quotient.  Moreover every
finite-dimensional unitary representation of this finitely generated `H` is
trivial.  Its kernel is normal, so a nontrivial representation would be
faithful; Malcev residual finiteness for finitely generated linear groups
would then give a nontrivial finite quotient of `H`.

Thus, for any injective `i:H->G` and any `1!=h in H`, `i(h)` is nontrivial in
`G`, while every finite-dimensional representation of `G` kills `i(h)` after
restriction to `H`.  Higman or Clapham embeddings therefore preserve exactly
the algebraic mark required by the nonhyperlinearity criterion.

### Retract, product, and graph-product wrappers cannot become finitely presented

Retracts of finitely presented groups are finitely presented.  For an
idempotent `e:G->G` on a finite presentation `<S|R>`, add the finitely many
relations `s=e(s)` (using word representatives).  The resulting quotient is
`im(e)` because every element is identified with its `e`-image and `e` fixes
the image.

Hence none of the following can be a finitely presented wrapper of `H`:

- a split extension retracting onto `H`;
- `H x K` for any `K`;
- a graph product having `H` as a vertex group, since killing all other
  vertex groups is a canonical retraction;
- an HNN or amalgam wrapper in which the proposed map back to `H` makes the
  base inclusion split.

This also explains why the genuine local-stability permanence in FFGS
Proposition 4.12 does not solve the problem: `H x F_2` remains infinitely
presented.

### Finite extensions cannot become finitely presented

If `H` has finite index in `G` and `G` is finitely presented, the
Reidemeister--Schreier theorem makes `H` finitely presented.  Since `H` is
not finitely presented (finitely presented LEF would imply RF), finite
extensions are excluded before any stability question.

### What remains for Higman/Clapham wrappers

A nonsplit embedding into a finitely presented group avoids the preceding
formal obstructions and preserves the invisible mark.  It does not preserve
local HS stability: local stability is not an upward hereditary property,
and the FFGS product theorem is not an arbitrary-overgroup theorem.

The exact remaining compiler target is therefore:

```text
find one nonsplit finitely presented overgroup G of H
whose canonical normalized-HS microstates admit local correction.
```

If `G` were locally HS-stable, finite presentation would upgrade it to global
HS stability by FFGS Lemma 3.11.  Since `G` contains the finite-dimensionally
invisible nontrivial element `i(h)`, hyperlinearity would contradict that
correction.  Thus proving this wrapper property already proves `G`
nonhyperlinear; it is the desired theorem, not a free permanence step.

Primary source: https://arxiv.org/abs/2307.13155

