---
rg: 2
id: some-fp-rf-group-acts-on-no-regular-rooted-tree
kind: claim
title: Some finitely presented residually finite group has no faithful action on any regular rooted tree
distinct_from:
  every-fp-rf-group-embeds-in-fp-self-similar-group: that asserts every finitely presented residually finite group lies in a finitely presented self-similar group; this asserts that some finitely presented residually finite group acts faithfully on no regular rooted tree, which refutes that claim.
  fp-rf-group-with-unbounded-prime-torsion: that is one sufficient mechanism, torsion of infinitely many prime orders; this is the weaker target, which a group failing condition (N1) with boundedly many torsion primes would also reach.
  decidable-fp-groups-need-not-embed-in-rational-group: that excludes rational homeomorphism groups, i.e. finite-state hosts, through word-problem complexity; this excludes every group of tree automorphisms, finite-state or not, so it needs a structural obstruction rather than a complexity one.
---

**OPEN.** There is a finitely presented residually finite group `G` that
embeds in `Aut(T_d)` for no `d >= 2`.

If established, it refutes `every-fp-rf-group-embeds-in-fp-self-similar-group`,
because self-similar groups are subgroups of `Aut(T_d)`. The route
`fp-rf-boone-higman-via-fp-self-similar-overgroups` then dies.

## Necessary conditions on G

- **(N1) fails for every d.** `G` is residually `W_d` for no `d`, where (N1) is
  condition (N1) of `every-fp-rf-group-embeds-in-fp-self-similar-group`.
- **Not virtually residually-p.** Suppose `N` is a normal subgroup of index
  `i` that is residually-`p`.
  - If `g` is not in `N`, then `G/N` separates `g`, and its composition factors
    have order at most `i`.
  - If `g != 1` lies in `N`, pick `M` normal in `N` with `N/M` a `p`-group and
    `g` not in `M`. The core of `M` in `G` is normal in `G`. The quotient of `G`
    by that core has composition factors of order at most `max(p, i)`.

  A finite simple group of order at most `c` is a subgroup of `S_c`. So `G`
  would be residually `W_c` with `c = max(p, i)`.
- **Not linear.** Finitely generated linear groups are virtually residually-`p`
  for some prime `p`. This is classical and was not rechecked here.

## Attempts

1. **Unbounded prime torsion.** Route
   `fp-rf-tree-obstruction-via-unbounded-torsion`, whose open clause is
   `fp-rf-group-with-unbounded-prime-torsion`. That clause would follow from a
   residually finite Higman embedding of the two-generated group of
   `cycle-transposition-lef-group-has-no-regular-tree-action`.
2. **Profinite completions that are products of large simple groups.**
   Kassabov--Nikolov, *Cartesian products as profinite completions*
   (arXiv:math/0602446), realize topologically finitely generated products of
   alternating groups as profinite completions of finitely generated residually
   finite groups. Any such group fails (N1) for every `d`, but none is known here
   to be finitely presented.
   - Their construction goes through `EL_3` over a ring whose congruence
     completion has an extra factor `EL_3(U)`, which they remove by passing to a
     subgroup.
   - This session read that paper only in outline, and did not check whether
     finite presentation survives the passage to the subgroup.

   Not pursued further here.
