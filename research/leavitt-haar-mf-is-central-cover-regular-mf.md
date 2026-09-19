---
rg: 2
id: leavitt-haar-mf-is-central-cover-regular-mf
kind: claim
title: A Leavitt Haar-row MF character is exactly a regular-MF central cover
distinct_from:
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that asks to exclude the Haar-row character; this identifies exactly what such a character would produce and leaves the infinite central-cover case open.
  leavitt-regular-character-is-not-mf: that excludes the regular MF character of the elementary quotient; this proves why a hypothetical Haar-row model must retain an infinite part of the unstable Steinberg centre.
artifacts:
  - research/regular-mf-descends-finite-normal-quotients.md
---

Put

```text
Delta=St_20(L_(F_2)(1,2)),       H=EL_20(L_(F_2)(1,2)),
pi:Delta -> H,                   Z=ker(pi),
```

and let `N` be a full first-row or last-column root module.  The following
are equivalent.

1. There is an MF character `chi` of `Delta` whose restriction to `N` is
   `delta_1`.
2. There is a subgroup `K <= Z` such that the regular character of
   `Delta/K` is MF.

Moreover, every witness in (1) supplies such a subgroup canonically as

```text
K={g in Delta:|chi(g)|=1}.                              (LCM1)
```

For every possible witness, `Z/K` is infinite.  Indeed, if it were finite,
regular-character descent through finite normal quotients would make the
regular character of `H=(Delta/K)/(Z/K)` MF, contradicting
`leavitt-regular-character-is-not-mf`.

Consequently the known non-MF regular character downstairs does not by
itself exclude the Haar row upstairs.  The exact remaining obstruction is an
**infinite unstable-Steinberg-centre sector**.  Any witness would also force
`H` to be hyperlinear: `Delta/K` is hyperlinear from its regular MF model,
and hyperlinearity descends through central quotients.

DERIVATION
leavitt-haar-central-cover-reduction-proof
