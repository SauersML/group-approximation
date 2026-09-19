---
rg: 2
id: zaremsky-2-19c-every-gl-n-z-in-some-mv-resolved
kind: claim
title: "Zaremsky Problem 2.19(c) resolved: does every GL_n(Z) embed in some Brin-Thompson group mV?"
---

Part (c) of `zaremsky-2-19-embeddings-into-brin-thompson-groups`, verbatim from
the list: "Does every GL_n(Z) embed in some mV?"

This claim is the question. It is established only through an answer route,
`zaremsky-2-19c-by-yes` or `zaremsky-2-19c-by-no`. Lane z2-19-glnz-q-2v chooses
the answer claims. Suggested ids: `every-gl-n-z-embeds-in-some-brin-thompson-group`
and `some-gl-n-z-embeds-in-no-brin-thompson-group`. Never write a
`requires: []` route into this claim.

## Reading

- GL_n(Z) embeds in GL_(n+1)(Z), and jV embeds in kV for j < k. So a yes means
  that for each n some mV contains GL_n(Z).
- GL_1(Z) is finite. GL_2(Z) is virtually free, and free groups of finite rank
  embed in V, so GL_2(Z) embeds in V: a virtual embedding in nV gives an
  embedding in nV (Belk–Bleak–Matucci, arXiv:1602.08635, p. 2).
- The content starts at n = 3, where SL_3(Z) has property (T).

## Couplings

- **Yes.** SL_3(Z) embeds in some mV, so kV fails the Haagerup property for
  every k ≥ m (Problem 2.7).
- **Haagerup.** If nV has the Haagerup property for infinitely many n, this
  part has answer no.
- **Part (a).** A yes here embeds every cocompact lattice in Sp(k,1), k ≥ 2,
  in some nV. These lattices are infinite hyperbolic groups with property (T),
  so this gives partial progress on part (a). The argument, unreviewed:
  - Such lattices are arithmetic (Corlette; Gromov–Schoen).
  - A torsion-free finite-index subgroup of the arithmetic group maps
    injectively under the projection with compact kernel.
  - So the lattice virtually embeds in some GL_N(Z), and virtual embeddings in
    nV give embeddings.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv): recorded the reading and the couplings
  above. The attack belongs to lane z2-19-glnz-q-2v. Torsion local finiteness of
  mV, claimed by Kojima–Sheng (arXiv:2603.18410) but with an invalid proof for
  m >= 2 (`kojima-sheng-two-generator-torsion-criterion-fails-in-v`, a22c90a4a; the
  statement is open, `brin-thompson-2v-is-torsion-locally-finite`, `brin-thompson-groups-contain-infinite-periodic-groups`), would not
  obstruct GL_n(Z) even if true, since the finitely generated torsion subgroups of
  GL_n(Z) are finite.
