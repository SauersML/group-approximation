---
rg: 2
id: rips-kernel-without-finite-quotients
kind: claim
title: A hyperbolic Rips extension whose kernel has no nontrivial finite quotients
distinct_from:
  non-rf-relatively-hyperbolic-with-rf-peripherals: that asks for a relatively hyperbolic group with a residual-finiteness failure and well-behaved peripherals; this asks for a short exact sequence with hyperbolic middle term whose kernel is finite-quotient-free, and says nothing about relative hyperbolicity
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Produce a short exact sequence

```text
1 -> N -> G -> Q -> 1
```

with `G` word-hyperbolic, `Q` finitely presented and **not** residually
finite, and `N` having no nontrivial finite quotient — without assuming
beforehand that a non-residually-finite hyperbolic group exists.

## What is already available and what is missing

Belegradek--Osin, *Rips construction and Kazhdan property (T)*,
arXiv:math/0605553, abstract read from source 2026-08-17: "for any
non-elementary hyperbolic group `H` and any finitely presented group `Q`,
there exists a short exact sequence `1→N→G→Q→1`, where `G` is a hyperbolic
group and `N` is a quotient group of `H`."  Since non-residually-finite
finitely presented groups are abundant, everything in the display above is
supplied except the condition on `N`.

Their small-cancellation quotient theorem controls suitability, torsion,
relative hyperbolicity and the outer action.  It does not prescribe the finite
residual of `N`, and the paper's own applications record the reason to be
careful: to give `G` the same finite-dimensional representation theory as `Q`
they observe it would suffice to start from a hyperbolic group with no
nontrivial finite quotients, and that the existence of such a group is
*equivalent* to the existence of a non-residually-finite hyperbolic group.

Kapovich--Wise together with Belegradek--Osin shows that the claim is exactly
equivalent to the existence of a non-residually-finite hyperbolic group; see
[[rips-kernel-target-iff-hyperbolic-nonrf]]. Thus this target is circular at
the existence level even though a quotient of a residually finite group can,
in isolation, have no finite quotients.

## Attempts

- **Kill the finite quotients by property (T) plus perfectness.**  Choose the
  Rips input `H` Kazhdan; then `N` is a quotient of a Kazhdan group, hence
  Kazhdan and perfect, which removes abelian quotients.  It does not remove
  finite quotients — finite groups have property (T) — so this gets nowhere by
  itself.
- **Make `N` simple.**  A nontrivial simple `N` with no finite quotients is an
  infinite simple group, and the small-cancellation machinery does produce
  simple-ish quotients in the limit; but the Rips output `N` must be normal in
  a hyperbolic `G` with hyperbolic quotient behaviour, and an infinite normal
  subgroup of a hyperbolic group with hyperbolic quotient is exactly the
  configuration the construction supplies only in the direction it was built
  for.  No control over the finite residual comes out.
- **Use a quotient with no finite quotients, such as the Leavitt unit group
  (2026-09-12).** Over such a quotient the kernel stays the whole problem.
  - **Leavitt quotient.** By
    `acyclic-quotientless-extension-completion-is-kernel-completion`, over a
    perfect quotient `Q` with no finite quotients and `H_2(Q;Z) = 0` (for
    example `R^x`), every finite image of the kernel splits off:
    `G/K ≅ Q x N/K`. So `G` and `N` have the same finite quotients and
    profinite completion. `leavitt-kazhdan-cover-rf-iff-kernel-rf` then makes a
    torsion-free hyperbolic cover of `R^x` residually finite exactly when `N`
    is.
  - **Any quotient without finite quotients.** A finite-quotient-free `G` forces
    every finite image of `N` to be abelian. A Kazhdan `N` then contains the
    finite-index subgroup `[N,N]`, which has no finite quotient at all: this
    target again, one finite index down.
  - **Artifact.** `research/artifacts/hyperbolic-no-finite-quotient-leavitt-cover-2026-09-12.md`.
- **Where it stands.**  The route this claim serves is one implication away
  from the answer, and the missing implication is a strengthening of a
  published theorem that its authors flagged as adjacent to the open problem.
  Recorded as open, with the circularity risk stated rather than hidden.
