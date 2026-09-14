---
rg: 2
id: simple-kazhdan-lef-program-open-problems-conjunction
kind: route
title: The program's open problems, as a conjunction
target: simple-kazhdan-lef-program-open-problems
requires:
  - lef-groups-have-lrf-minimal-topologically-free-actions
  - sofic-groups-embed-in-simple-kazhdan-sofic-groups
  - sofic-groups-have-measured-free-minimal-subshifts
  - free-minimal-subshifts-all-rf-iff-virtually-cyclic
  - free-minimal-subshift-el-groups-all-lef-iff-virtually-cyclic
  - labbe-wang-shift-crossed-product-is-exactly-matricial
  - subshift-crossed-product-ring-has-bass-stable-rank-at-most-two
  - minimal-cantor-crossed-product-is-an-exchange-ring
  - elementary-group-normal-subgroups-are-subsystem-kernels
  - subshift-elementary-groups-are-steinberg-groups-in-finite-rank
  - binary-subshift-elementary-groups-are-two-generated
  - subshift-elementary-groups-are-cstar-simple
  - subshift-crossed-product-algebraic-cartans-are-conjugate
  - subshift-elementary-group-lef-growth-at-least-exp-r-squared
  - subshift-elementary-group-lef-growth-tracks-complexity
  - accumulating-minimal-sets-el-restriction-kernel-elementary
  - fp-simple-finite-group-models-reduce-to-alternating-constituents
  - hyperlinear-groups-embed-in-simple-kazhdan-hyperlinear-groups
  - operator-mf-groups-embed-in-simple-kazhdan-mf-groups
  - simple-ring-el3-lef-forces-lef-ring
  - subshift-elementary-group-reduced-cstar-is-not-mf
  - fp-sofic-kazhdan-group-not-residually-finite
  - infinite-simple-kazhdan-limit-of-alternating-groups
  - subshift-group-finite-simple-shadows-are-ring-models
  - every-subshift-elementary-group-non-uniform-growth
  - topological-full-group-derived-uniform-exponential-growth
  - subshift-elementary-groups-are-exact
  - subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer
  - subshift-el-group-theory-computes-arithmetic-of-the-language
  - crossed-product-group-embeds-in-projective-elementary-group
---

Assembly only: the root is the conjunction of the listed open claims. This route makes each of them reachable from a
root, so the frontier report lists them as holes of this program.

Members added by sk-cairn-steward-2 (2026-09-13, sk landings from 20:00 on): `accumulating-minimal-sets-el-restriction-kernel-elementary` `fp-simple-finite-group-models-reduce-to-alternating-constituents` `hyperlinear-groups-embed-in-simple-kazhdan-hyperlinear-groups` `operator-mf-groups-embed-in-simple-kazhdan-mf-groups` `simple-ring-el3-lef-forces-lef-ring` `subshift-elementary-group-reduced-cstar-is-not-mf`.

Members added by sk-cairn-steward-2 (2026-09-13, second pass, sk landings to 22:34): `fp-sofic-kazhdan-group-not-residually-finite` `infinite-simple-kazhdan-limit-of-alternating-groups` `subshift-group-finite-simple-shadows-are-ring-models` `every-subshift-elementary-group-non-uniform-growth` `topological-full-group-derived-uniform-exponential-growth` `property-t-factors-contain-weakly-dense-popa-algebras`.

`erf-groups-have-decidable-simple-kazhdan-hosts` moved to the embedding theme (sk-cairn-steward-2, 2026-09-13): sk-decidable-host established it through `erf-groups-decidable-hosts-via-half-line-proof`.

Members added by sk-cairn-steward-2 (2026-09-13, third pass, sk landings to 22:47): `subshift-el-groups-have-bounded-conjugation-invariant-norms` `subshift-elementary-groups-are-exact`.

Members added by sk-cairn-steward-2 (2026-09-13, fourth pass, sk landings to 22:56): `subshift-el3-isomorphisms-recognize-diagonal-subgroups`.

`subshift-el-groups-have-bounded-conjugation-invariant-norms` moved to the structure theme (sk-cairn-steward-2, 2026-09-13): sk-free-6 established it.

Member added by sk-cairn-steward-5 (2026-09-14, wave-12 pass): `subshift-el-group-theory-computes-arithmetic-of-the-language`.

`property-t-factors-contain-weakly-dense-popa-algebras` moved to the approximation theme (sk-cairn-steward-5, 2026-09-14): Theorem P, `separable-ii1-factors-have-weakly-dense-popa-combs` (sk-popa-input2; sk-verify-20 PASS-WITH-FIXES), establishes it through `weakly-dense-popa-combs-exist-in-property-t-factors`.

Member added by sk-cairn-steward-5 (2026-09-14, final pass): `crossed-product-group-embeds-in-projective-elementary-group`, the restated Whitehead embedding (abelian unit groups, and derived subgroups of unit groups, in `EL_N` modulo its centre). It is open as a node: sk-subgroups demoted it after its only route, which used the false multiplicativity of `diag(a, a^-1, 1)`, was invalidated, and it was unreachable before.
