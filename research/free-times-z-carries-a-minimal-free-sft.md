---
rg: 2
id: free-times-z-carries-a-minimal-free-sft
kind: claim
title: For every n >= 1 the one-ended group F_n x Z, non-amenable for n >= 2, carries a nonempty minimal free (strongly aperiodic) subshift of finite type; so do unimodular GBS groups and BS(1,n)
distinct_from:
  minimal-aperiodic-wang-shift-exists: that is Labbé's minimal aperiodic Z^2 shift; this is its lift to F_n x Z along a flow on the tree, which gives the first non-amenable one-ended groups on main known to carry a minimal free SFT.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is the open (M2) for every decidable fp group; this records instances of it, since an SFT is effectively closed.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED (literature import, read at source 2026-09-18, lane bh-openq-papers).**
N. Aubrun, N. Bitar, S. Huriot-Tattegrain, *Strongly aperiodic SFTs on generalized
Baumslag–Solitar groups*, arXiv:2204.11492v3, TeX `main.tex`:
- l.755–757: "There exists a minimal strongly aperiodic SFT on F_n × Z."
- Corollary after it: "Unimodular GBS groups admit minimal strongly aperiodic SFTs. In
  particular, both Λ(n,m) and BS(n,n) admit minimal strongly aperiodic SFTs." (Λ(n,m) are the
  torus knot groups.)
- Section 6 opening: "Amenable Baumslag-Solitar groups BS(1,n) are known to have strongly
  aperiodic SFTs [Esnay–Moutot 2020] and even minimal strongly aperiodic SFTs [Aubrun–Schraudner,
  arXiv:2012.11037]."
- Theorem `thm:BSmn_strongly_aperiodic_SFT` (l.1148): non-residually-finite `BS(m,n)` admit strongly
  aperiodic SFTs. Minimality is not claimed there.

"Strongly aperiodic" means every point has trivial stabilizer, i.e. the action is free.

**Mechanism** (their §5). A minimal aperiodic Wang shift `X_0` on `Z^2` with an expansive direction
(Labbé–Mann–McLoud-Mann, cited there as Theorem `theorem:SFT_Labbe`) is laid on (flow line) × `Z`.
The flow is an SFT `Y_f` on `F_n` whose configurations single out one generator direction at every
vertex, following a bi-infinite word `W`. Minimality comes from minimality of `X_0` together with that of the flow subshift
(their Lemma `minflow`).

**Consequences on main.**
- *Instances of (M2).* An SFT is effectively closed, and a minimal SFT has decidable language.
  For the latter see Carrasco-Vargas's thesis arXiv:2505.14247, `Chapter_Medvedev.tex`, l.143:
  "Let G be a group with decidable word problem. A minimal G-SFT has decidable language". So
  `F_n × Z`, the unimodular GBS groups and `BS(1,n)` satisfy the conclusion of
  `decidable-fp-groups-have-effective-minimal-free-subshifts`.
- *For the master route.* The decisive object of the synthesis is a (quantum-rigid) free minimal
  SFT over a one-ended group. `F_n × Z` (`n ≥ 2`) is a one-ended, non-amenable, finitely presented,
  torsion-free group that carries one. Rigidity (gate G2) is not addressed by the source.

## Lesson for general BH

Minimal free SFTs are not an amenable or `Z^2`-only phenomenon. Take a minimal aperiodic `Z^2`
shift with an expansive direction and a finite-type flow on a tree; the flow transports the shift
to `F_n × Z`. So existence over one-ended non-amenable groups is available, and on this class the
remaining difficulty of the SFT gate is rigidity, not existence.
