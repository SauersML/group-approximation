---
rg: 2
id: diracization-gap-equals-nonhyperlinear-group
kind: claim
title: A power-uniform Diracization gap is equivalent to a nonhyperlinear group, not a weakening of it
distinct_from:
  character-diracization-limit: that is the limit computation, true for every character and carrying no embeddability content; this grades the *quantitative* hypothesis that the proposed negative program adds on top of it
  hyperlinear-quotient-permanence-equivalence: that equates universal hyperlinearity with quotient permanence on the group side; this equates one specific trace-amplification hypothesis with the same target, and its content is the two degeneracies that kill the mechanism when the hypothesis is not assumed
  additive-index-instability: that is an amplification no-go for additive Fredholm indices; this is an equivalence for a trace-power hypothesis, with no index in it
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

ESTABLISHED.  `character-diracization-limit` maps every character to the
regular character of a quotient, so it invites the following negative
program: start from a known non-Connes-embeddable trace, apply
`tau |-> |tau|^{2k}`, and hope non-embeddability survives to the limit.  The
hypothesis such a program needs, in its general form, is

```text
(D)  there are a countable group Gamma, a character tau of Gamma, a finitely
     supported functional L on C[Gamma], and delta > 0 with

        inf_k  Re L(|tau|^{2k})  >=  sup_{sigma in CE(Gamma)} Re L(sigma) + delta.
```

**Theorem.**  `(D)` holds if and only if a nonhyperlinear group exists.

So `(D)` is a *reformulation* of the target, exactly as hard, and any general
argument establishing it -- gap amplification, parallel repetition, a coding
construction applied to an unspecified `tau` -- would already have produced a
nonhyperlinear group by itself.  This is recorded so that the mechanism is
not mistaken for a reduction.

## What survives as usable

The forward direction is a genuine tool, and the equivalence does not spoil
it: once `tau` is **pinned to a named construction**, `(D)` for that `tau` is
a specific, falsifiable statement that is no longer equivalent to the target
(the trivial witness used in the converse is unavailable).  The honest form of
the program is therefore "prove `(D)` for *this* trace", never "prove `(D)`".

## The two degeneracies, which are the practical content

Both follow from `ce-characters-closed-multiplicative-semigroup`.

1. **Trivial scalar kernel is fatal.**  If `K_tau = {e}` then the limit is
   `delta_e`, the regular character of `Gamma` itself.  For `Gamma` free --
   the case every stated version of the program uses, since every group is a
   free quotient -- that character is in `CE`, so `(D)` fails outright.  A
   usable `tau` must make some nontrivial word act as a **scalar** in its GNS
   algebra, and the `MIP^*`-derived traces come with no such control.
2. **An embeddable square is fatal.**  If `|tau|^2 in CE` then every
   `|tau|^{2k} = (|tau|^2)^k` is in `CE` and so is the limit, because `CE` is
   a closed sub-semigroup.  Non-embeddability of `tau` alone is not enough;
   the *square* must already fail, and fail uniformly.

Together these say the mechanism sees only the scalar locus of `tau` and
throws the rest away.  That is the general form of the verdict already
recorded for the IRS instance in `notes/FALSE_RECENT_LITERATURE_AUDIT.md` §3
-- "taking normal cores destroys the information in the currently available
examples" -- with Manzoor's non-co-hyperlinear IRS (arXiv:2502.06697) named
there as supplying the cleanest language for the target and no shortcut to it.

## First cheap experiments this leaves

Screening questions, in increasing cost, none of which is equivalent to the
target:

- Does any *named* non-embeddable character -- Manzoor's IRS character, a
  solution-group character, a `MIP^*` gap trace -- have a nontrivial scalar
  kernel `K_tau`?  Solution groups are the plausible source, since their
  distinguished central involution `J` acts by `-1` and is therefore scalar;
  note that `slofstra-involution-not-sofic-radical` settles a *different*
  question about the same element (it is visible in permutation
  ultraproducts) and does not answer this one.
- For such a `tau`, is `|tau|^2` embeddable?  Degeneracy 2 makes this a
  one-step kill.
