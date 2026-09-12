# Cairn ingestion: anchoring, non-co-hyperlinear IRSs, and hyperlinear profile

Date: 2026-08-20

Primary source bundles supplied by the user:

- Bavarian--Vidick--Yuen, *Anchored parallel repetition for nonlocal games*,
  arXiv:1509.07466v2.
- Aareyan Manzoor, *There is an equivalence relation whose von Neumann algebra
  is not Connes embeddable*, arXiv:2502.06697v2.
- William Slofstra, *A group with at least subexponential hyperlinear profile*,
  arXiv:1806.05267v1.

## What was new to the graph

The anchoring paper had appeared only as an internal ingredient in the prose
of `mipstar-equals-re-citation`; its own reusable statements were absent.  This
ingestion adds the exact one-copy affine value identity and the quantitative
dimension-sensitive parallel-repetition theorem as separate established
claims.  Scope fences explicitly prevent either theorem from being mistaken
for a normalized-HS group-relator compiler.

Manzoor's pseudo-subgroup hierarchy was already used by
`zpc-irs-value-computable-upper-hierarchy`, but the paper's unrestricted IRS
game gap and its two headline endpoints were absent as graph nodes.  This
ingestion adds the chain

```text
IRS/quantum game gap
  -> non-co-hyperlinear free-group IRS
  -> non-CE property-(T) ergodic relation factor.
```

The chain is fenced from `non-hyperlinear-group`: the IRS need not be a normal
Dirac mass, and a relation factor need not be a group factor.

## What was already present and was not duplicated

The Slofstra bundle was already represented accurately by
`slofstra-subexponential-hyperlinear-profile` and
`robust-clifford-capacity-bound`, including the construction, the quantitative
BORS embedding, the `2^(floor(n/2)-1)` Clifford capacity estimate, and the
`(n+1)^2` presentation-to-global-homomorphism loss.  Those nodes are retained
and this artifact is attached to them as the source-audit record.

## Strategic consequence

The three sources form a useful map but do not close the current goal:

- anchoring amplifies game soundness once a suitable finite game exists;
- Manzoor converts a tailored computability gap into a non-CE action/IRS object;
- Slofstra turns long approximate Clifford families into dimension pressure.

The live missing conversions remain exactly the ones Cairn already exposes:
groupifying a constant normalized-HS semantic gap, or converting the random
IRS/action endpoint to a normal Dirac/group endpoint without losing the gap.
