---
rg: 2
id: no-published-unconditional-codense-stable-host
kind: claim
title: No published group is both flexibly HS-stable and non-amenable with an infinite co-dense Kazhdan subgroup, and no permanence operation makes one
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  stable-group-with-codense-kazhdan-subgroup: that asks for such a host to build the goal; this is the survey result that none is currently published and that two fences prevent assembling one from known operations, so a genuinely new stability theorem is required.
  nonhyperlinear-conditional-routes-landscape: that maps the conditional routes; this is the specific negative census of stable-group hosts.
---

**Established by citation survey (2026-08-21).**  As of 2026-08 no group is
published as flexibly Hilbert--Schmidt stable (or weakly ucp-stable) that is
also non-amenable and contains an infinite finitely generated subgroup with
property (T) or (tau) that is co-dense (surjects onto every finite quotient).
Two fences show no known permanence operation produces one.

**Fence A (no infinite RF amenable quotient).**  If `A` has an infinite
residually finite amenable quotient `D` (in particular infinite
abelianization), no co-dense f.g. `C` has a uniform conjugation gap:
co-density forces `C` onto `D`'s growing finite quotients, whose Folner sets
give `C`-almost-invariant far-from-invariant vectors in the deformations
`rho (+) rho.chi_lambda` (`chi_lambda -> 1` through `D`), killing any uniform
Kazhdan constant.

**Fence B (non-LERF required).**  If `A` is LERF, every f.g. subgroup is
profinitely closed, so a proper f.g. `C` is never co-dense.

**The census.**  Every published non-amenable HS-stable group hits A or B:
free/virtually free groups and free products of virtually free groups
(Gerasimova--Shchepin arXiv:2107.10032; Hadwin--Shulman) are LERF (Hall,
Burns, Scott); one-relator groups with nontrivial center (Hadwin--Shulman
arXiv:1706.08405) are Seifert-fibered hence LERF and have infinite
abelianization; pincushion graph products (Atkinson arXiv:1808.04664) are
`finite x free-product` (LERF) or carry an infinite amenable factor; amalgams
/ HNN over finite subgroups (Gerasimova--Shchepin arXiv:2305.08720) preserve
LERF or reinstate an amenable quotient; products with amenable HS-stable
groups (Ioana--Spaas; via Ioana arXiv:1909.00282) contribute an infinite RF
amenable quotient; and `F_m x F_k` is NOT HS-stable (Ioana arXiv:2108.09589),
so no product bootstrapping to largeness.  The permanence operations (free
product, amalgam over finite, `x` amenable, finite extension) each preserve
fence A or B.  Weak ucp-stability does not rescue: LLP implies it (all
amenable groups qualify), but the HNN mechanism cannot consume weak ucp
(infinite-dimensional dilations resurrect `l^2(A/C)` and destroy the corner
traces).

**Conclusion.**  The first usable host requires a NEW stability theorem for a
group whose finite-dimensional representation theory is congruence-rigid --
exactly the S-arithmetic / higher-rank-lattice class.  The complete candidate
list, all with the same single open hypothesis: `SL_2(Z[1/p])` (the
Dogon--Vigdorovich question), `SL_2(Z[1/pq])`, `SL_3(Z[1/p]) supset SL_3(Z)`,
`Sp_4(Z)`, and `SL_n(Z)` (`n >= 3`) with a thin co-dense subgroup
(`sln-z-thin-codense-tau-pair`).  So the goal genuinely reduces to a new
flexible-stability theorem for one congruence-rigid group; nothing in the
current literature shortcuts it.
