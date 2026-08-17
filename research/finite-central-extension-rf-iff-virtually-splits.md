---
rg: 2
id: finite-central-extension-rf-iff-virtually-splits
kind: claim
title: A finite central extension of a residually finite group is residually finite exactly when it virtually splits
distinct_from:
  oyakawa-graph-wreath-rf-iff-acting-group-rf: that is also a residual finiteness criterion, but for a semidirect product with a graph-product kernel, and it is discharged by properness and local finiteness of an action on a graph; this one has a finite central kernel and is decided by a cohomology class, with no action, no graph and no hyperbolicity in its statement
  non-residually-finite-hyperbolic-group: that is the open counterexample target; this is an established general criterion about arbitrary residually finite base groups, and it neither asserts nor denies that any hyperbolic group has a persistent class
  central-extension-twisted-sector-criterion: that is an MF criterion for a central order-two extension, phrased as nonemptiness of a twisted asymptotic sector over the quotient; this is a residual finiteness criterion for an arbitrary finite central kernel, phrased as vanishing of the extension class on a finite-index subgroup, and no approximation property appears in it
  mf-hyperlinear-of-finite-normal-quotient: that transports operator approximation properties across a finite normal subgroup; this decides residual finiteness of the total group from cohomology of the quotient
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Let `H` be residually finite, let `A` be a finite abelian group with trivial
`H`-action, and let `α ∈ H^2(H; A)` classify a central extension

```text
1 -> A -> E_α -> H -> 1.
```

Then the following are equivalent:

1. `E_α` is residually finite;
2. `res^H_(H_0)(α) = 0` for some finite-index subgroup `H_0 ≤ H`;
3. the extension splits over some finite-index subgroup of `H`.

Equivalently: `E_α` fails to be residually finite exactly when `α` defines a
nonzero element of the direct limit `lim_(H_0 ≤_f H) H^2(H_0; A)` under
restriction — a **persistent** class.

Classical folklore, not new here.  It is the mechanism behind Deligne's
non-residually-finite central extension of `Sp_4(ℤ)` and behind the arithmetic
constructions of Hill, *Non-residually finite extensions of arithmetic
groups*, Res. Number Theory (2019).  The graph carries it because a live route
to `non-residually-finite-hyperbolic-group` consumes it, and because it
converts a group-theoretic search into a cohomological one.

## The profinite half, which is the practical filter

If `α` lies in the image of the comparison map

```text
H^2_cont(H_hat; A) -> H^2(H; A),
```

then `E_α` is residually finite: pull the profinite extension back along
`H → H_hat`, and the pullback embeds in a product of a profinite group with
`H`, both residually finite.  So a persistent class must lie **outside** the
profinite image.  This is what makes the search hard rather than merely
unsolved — for the natural arithmetic candidates the known results say the
interesting classes are in that image.
