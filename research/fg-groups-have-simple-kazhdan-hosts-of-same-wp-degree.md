---
rg: 2
id: fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree
kind: claim
title: Every finitely generated group embeds in an infinite finitely generated simple Kazhdan group whose word problem has the same Turing degree
distinct_from:
  lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree: that needs the input to be LEF and gives an LEF host through the half-line overgroup; this drops every approximation hypothesis on the input and gives up only the LEF property of the host.
  lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts: that is the LEF equivalence with solvable word problem; this gives decidable simple Kazhdan hosts to every decidable input, LEF or not.
  erf-groups-have-decidable-simple-kazhdan-hosts: that covers effectively residually finite inputs; this covers all finitely generated inputs.
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that is the host for LEF acting groups with the LEF conclusion; this is the same host for every infinite finitely generated acting group, embedding the whole acting group through Whitehead's lemma.
  countable-group-embeds-in-fg-simple-kazhdan-group: that embeds every countable group in a simple Kazhdan group through small cancellation with no word problem control; this controls the Turing degree of the word problem.
  boone-higman-thompson-simple-envelope: that gives a decidable simple envelope that may split as an amalgam; this gives a decidable simple envelope with property (T), hence property FA.
  decidable-groups-embed-in-decidable-simple-fa-groups: that asks only for property FA and solvable word problem; this gives property (T) and the exact Turing degree for every finitely generated input.
artifacts: [research/artifacts/lamplighter-kazhdan-host-without-lef-2026-09-17.md]
---

**ESTABLISHED** through `fg-groups-simple-kazhdan-hosts-lamplighter-proof`.

Let `Γ` be a finitely generated group and `Δ = Γ × Z`. Put
`L = Z/2 ≀ Δ`, acting on `2^Δ` by shifts and finite flips, `R = LC(2^Δ, F_2) ⋊ L`
and `H = EL_3(R)`. Then:

1. `H` is an infinite, finitely generated, simple group with property (T), hence
   with property FA;
2. `γ ↦ diag(u_γ, u_γ^(-1), 1)` embeds `Γ` in `H`;
3. `WP(Γ) ≤_m WP(H) ≤_T WP(Γ)`.

In particular every finitely generated group with solvable word problem embeds
in an infinite finitely generated simple Kazhdan group with solvable word
problem.

## Why this matters

- It settles `decidable-groups-embed-in-decidable-simple-fa-groups`, the last
  missing prerequisite of part (D) of
  `finitary-permanence-closures-collapse-boone-higman-to-base`, and one of the
  two prerequisites of the route `boone-higman-from-simple-fa-inputs`.
- It makes Boone--Higman equivalent to its restriction to simple Kazhdan
  decidable inputs (`boone-higman-iff-simple-kazhdan-decidable-inputs`).
- It kills, for every decidable input, the class of permanence reductions
  mixing tree steps with infinitary steps
  (`mixed-permanence-closures-collapse-boone-higman-to-base`).

**The missing step, and why it was missed.** The LEF host was proved with the
hypothesis LEF throughout, but LEF is used only to prove that the host is LEF.
Minimality, topological freeness, ring simplicity, Steinberg simplicity of `EL_3`,
Ershov--Jaikin-Zapirain (T) and the word problem reduction need only an infinite
finitely generated acting group. The half-line overgroup was needed there to put
the input into a derived subgroup, because the host embedded only `[L,L]`;
`diag(u, u^(-1), 1)` lies in `E_2(R)` for every unit `u` by Whitehead's lemma, so
the whole of `L` embeds.

## Attempts

1. **Reread the lamplighter host without LEF (2026-09-17).** See the artifact. *Settles the claim.*
