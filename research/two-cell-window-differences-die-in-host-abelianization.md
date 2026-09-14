---
rg: 2
id: two-cell-window-differences-die-in-host-abelianization
kind: claim
title: The difference of a two-cell Garden-of-Eden window lies in the commutator subgroup of the table host
distinct_from:
  strict-automaton-tables-present-an-invisible-window-difference: that places a sofic-invisible difference in the window and names the table group where it must die; this specialises to a two-cell window and computes the resulting lattice membership test in the host's abelianization.
  sofic-radical-localizes-garden-of-eden-windows: that localizes a window difference in the sofic radical of the memory group; this draws the abelian consequence and turns it into a Smith normal form test on the forward partition.
  table-hosts-have-a-cell-count-betti-lower-bound: that bounds the rank of the host's abelianization by a cell count; this is a membership condition on one specific element of that abelianization.
artifacts:
  - research/artifacts/table-abelianization-and-cell-count-2026-09-12.md
---

**ESTABLISHED** by `two-cell-window-abelian-death-proof`.

Let a realization of a design over the canonical table host `H = Hol_M(E)` be
injective with a Garden of Eden on a two-cell window `Omega = {1, d}`. Then

```text
d in Rad_sof(H) subset [H, H].
```

If moreover `d = m_1 m_2^(-1)` with `m_1, m_2 in M`, as the overlap lemma of
`defect-window-automata-2026-09-12` forces for a two-cell window, then in
`H^(ab) = Z^(M \ {1}) / L`,

```text
e_(m_1) - e_(m_2)  in  L,
```

where `L` is the image of the integral cycle space of the decoder difference
graph under `e -> e_(m') - e_m`, with `e_1 = 0`.

**Mechanical test.** Compute a cycle basis of `Gamma_E`, form the integer matrix
of abelianized holonomies, and test lattice membership by Smith normal form. A
negative answer excludes the window for every alphabet, every rule pair with that
forward partition and every realization. Membership of the rational span does not
suffice: a nonzero torsion image survives in a finite cyclic quotient, which is
sofic.

**Corollary.** If no identification of the table is anchored, so that
`x_m -> 1` gives a surjection onto `Z`
(`table-hosts-have-a-cell-count-betti-lower-bound`), then no two-cell window
difference is a single memory letter.

**Scope.** The test is vacuous when `d` is a commutator of the host's generators,
since a commutator lies in `[H,H]` for free. That is exactly the case of the
defect window of `defect-window-automaton-over-leavitt-units`, where
`d = [u c u^(-1), l]`. So this filter screens single-letter and other
abelianization-visible windows, and says nothing about commutator windows.

Proof: Section 4 of the artifact.
