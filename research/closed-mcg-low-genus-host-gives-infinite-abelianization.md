---
rg: 2
id: closed-mcg-low-genus-host-gives-infinite-abelianization
kind: claim
title: A genus-zero or genus-one punctured or bordered host for a finite-index subgroup of a closed-surface mapping class group forces virtual surjections onto Z
distinct_from:
  closed-mcg-punctured-host-forgetful-dichotomy: that sorts copies in hosts of every genus into two shapes by the first forgetful kernel; this follows every infinite subgroup down the forgetful tower of a genus-zero or genus-one host and produces a virtual surjection onto Z.
  closed-mcgs-virtually-embed-in-punctured-mcgs: that asks whether some host exists; this shows that a host of genus at most one would give a finite-index subgroup of Mod(S_g) with infinite abelianization.
---

**ESTABLISHED.** Let `g ≥ 3` and let `L ≤ Mod(S_g)` have finite index. Let `Σ′`
be an orientable finite-type surface of genus `h ≤ 1` with at least one puncture
or boundary component, and let `ι: L → Mod^±(Σ′)` be injective. Let
`L′ ≤ L` and `ρ′: L′ → PMod(S_(h,m))` be as in item 0 of
`closed-mcg-punctured-host-forgetful-dichotomy`. So `L′` has finite index in
`Mod(S_g)` and `ρ′` is injective.

**(a) Genus zero.** If `h = 0`, every nontrivial subgroup of `L′` surjects onto
`Z`. In particular:
- `L′` surjects onto `Z`;
- `L′` is torsion-free.

**(b) Genus one.** If `h = 1`, every infinite subgroup of `L′` has a subgroup of
finite index that surjects onto `Z`. In particular `L′` has a finite-index
subgroup `L″`, of finite index in `Mod(S_g)`, that surjects onto `Z`.

**Consequence.** If a finite-index subgroup of `Mod(S_g)` embeds in the extended
mapping class group of a surface of genus `≤ 1` with a puncture or boundary
component, then some finite-index subgroup of `Mod(S_g)` has infinite
abelianization. Equivalently: for any `g ≥ 3` for which `Mod(S_g)` does not
virtually surject onto `Z`, every host for
`closed-mcgs-virtually-embed-in-punctured-mcgs` has genus `≥ 2`. By the
dichotomy it then has either shape A with `h ≥ g`, or shape B with `h ≥ 2`.

**Status of the input conjecture (not settled here).** A. Putman and B. Wieland,
*Abelian quotients of subgroups of the mapping class group and higher Prym
representations*, arXiv:1106.2747. The abstract was fetched on 2026-09-16 and
reads in part:

> "A well-known conjecture asserts that the mapping class group of a surface
> (possibly with punctures/boundary) does not virtually surject onto $\Z$ if
> the genus of the surface is large. We prove that if this conjecture holds for
> some genus, then it also holds for all larger genera."

Whether that conjecture has since been proved in any genus was not verified.
This claim does not depend on it.

**Scope.**
- The claim is a reduction for hosts of genus `≤ 1`. It does not exclude them
  unconditionally.
- It says nothing about hosts of genus `≥ 2`.
- `ι` is only assumed injective.

The derivation is `closed-mcg-low-genus-host-abelianization-proof`.
