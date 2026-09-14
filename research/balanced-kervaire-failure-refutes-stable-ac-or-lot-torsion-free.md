---
rg: 2
id: balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free
kind: claim
title: A Kervaire killing failure over a deficiency-zero group refutes the stable Andrews--Curtis conjecture or produces a LOT group with torsion that is neither hyperlinear nor MF
distinct_from:
  deficiency-zero-kervaire-failure-yields-whitehead-counterexample: that turns a balanced killing failure into a finite Whitehead counterexample of no particular shape; this uses Howie's 3-deformation theorem to force that counterexample, whenever its contractible complex is stably AC-trivial, into a LOT complex whose group carries the torsion.
  contractible-2-complex-minus-a-cell-is-aspherical: that is the open one-cell case of Whitehead's conjecture; this is an implication from a balanced killing failure to the failure of stable AC or of torsion-freeness of LOT groups, and asserts neither.
  lot-groups-are-torsion-free: that is the open statement that every LOT group is torsion-free; this shows that it, together with stable AC, forbids balanced killing failures.
  stable-andrews-curtis-conjecture: that is the stable Andrews--Curtis conjecture itself; this only says what a balanced Kervaire failure would do to it.
artifacts:
  - research/artifacts/ideas-bridges-2-2026-09-14.md
---

**ESTABLISHED** through `balanced-kervaire-stable-ac-lot-proof`. Unreviewed.
No novelty is claimed: this composes
`deficiency-zero-kervaire-failure-yields-whitehead-counterexample` with Howie's
1983 theorem `howie-point-deformable-complex-minus-cell-deforms-to-lot` and
with Klyachko's theorem through item 2(c) of the former.

**Setting.** Let `G != 1` have a finite presentation
`<x_1, ..., x_n | r_1, ..., r_n>` with presentation complex `K`. Let
`w in G * <t>` satisfy `G_w = (G * <t>)/<<w>> = 1`, and let `W` be a word
representing `w`. Let `L` be the presentation complex of
`P_w = <x_1, ..., x_n, t | r_1, ..., r_n, W>`, and `e_W` its 2-cell attached
along `W`. By the bridge theorem, `P_w` is a balanced presentation of the
trivial group and `L` is a finite contractible 2-complex.

1. **Andrews--Curtis side.** Suppose `P_w` is stably AC-trivial (moves
   (AC1)--(AC5) of `stable-andrews-curtis-conjecture`), or more generally that
   `L` 3-deforms to a point. Then there is a labelled oriented tree `Gamma` whose
   LOT complex `K(Gamma)` is 3-deformation equivalent to `L - e_W = K v S^1`.
   For every such `Gamma`:
   - (a) the LOT group is `G(Gamma) = G * Z`;
   - (b) `G(Gamma)` has torsion, and it is neither hyperlinear nor MF;
   - (c) `K(Gamma)` is not aspherical.
2. **Converse direction.** If a LOT group `G(Gamma)` is isomorphic to `H * Z`
   with `H != 1`, then `H_1(H) = 0` and some `w in H * <s>` with exponent sum
   `+-1` in `s` satisfies `(H * <s>)/<<w>> = 1`. So `H` is a Kervaire killing
   failure, over a group of unknown deficiency.

**Consequence.** Assume `stable-andrews-curtis-conjecture`. Then any one of the
following implies `kervaire-killing-form-holds-over-nonnegative-deficiency-groups`:
- (i) every LOT group is torsion-free (`lot-groups-are-torsion-free`, route
  `kervaire-killing-form-via-stable-ac-and-torsion-free-lots`);
- (ii) every LOT group is hyperlinear;
- (iii) every LOT group is MF;
- (iv) no LOT group is a free product `H * Z` with `H != 1`.

Each of (i)--(iii) is implied by asphericity of all LOT complexes, and (i) also
by local indicability of all LOT groups. Both of those are open. By
Barreto--Minian (quoted in `lot-groups-are-torsion-free`), even (i) is open.

**Why it matters.** A certified balanced killing failure would already refute
Kervaire--Laudenbach and finite Whitehead, and give a finitely presented
non-hyperlinear group. By item 1 it would also refute stable Andrews--Curtis,
or put torsion into a LOT group. Recalled from Cerdeiro's summary of Howie
(1985), not read at source: LOT complexes are the spines of ribbon disc
complements in `D^4`. So the second alternative is a ribbon disc complement
with torsion in its fundamental group.
