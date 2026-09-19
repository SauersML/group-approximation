---
rg: 2
id: torus-surjunctivity-implies-finite-alphabet-surjunctivity
kind: claim
title: A group over which every injective torus-alphabet automaton is surjective is surjunctive on every finite-alphabet full shift
distinct_from:
  gottschalk-surjunctivity-conjecture: that is the finite-alphabet conclusion alone; this is only the implication from torus-alphabet surjunctivity, which fails over a group only if that group is torus-surjunctive and not finite-alphabet surjunctive.
  stable-finiteness-forces-binary-surjunctivity: that transfers from linear algebra over F_2; this would transfer from a topological statement whose linear shadow is characteristic zero.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

For every countable group `G`, suppose that for every `d >= 1` every injective continuous
`G`-equivariant self-map of `(T^d)^G` is surjective. Then every injective cellular
automaton on every finite-alphabet full shift `A^G` is surjective.

This is the transfer step of `gottschalk-via-torus-alphabet-degree-transfer`. No mechanism
is known. It fails over `G` exactly when `G` is torus-surjunctive but carries a strict
finite-alphabet automaton.

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): artifact Section 3.2. Obstructions to every
  mechanism that uses equivariant maps between the two shifts.
  - **(O1) No factor maps.** `(T^d)^G` is connected, so every continuous map from it to
    `A^G` is constant.
  - **(O2) Subsystem embeddings prove nothing.** Suppose `iota: A^G -> (T^d)^G`, e.g.
    `(Z/n)^G = ker[n] in T^G`, intertwines `tau` with an injective torus automaton
    `sigma`.
    - Torus surjunctivity only makes `sigma` a homeomorphism.
    - A homeomorphism may map `iota(A^G)` strictly into itself.
    - Excluding that is the Gottschalk statement for `tau` itself.
  - **(O3) Mixed alphabets reintroduce counting.** On `A x T^d`, degree acts only inside
    components of window spaces. The component count is the finite-alphabet problem.
  - **What a proof would need.** A non-equivariant construction turning a strict datum
    into an injective torus automaton with singular degree matrix. It must transport
    information from characteristic `p` to characteristic `0`, because linear torus
    surjunctivity holds for every group (Kaplansky), while linear finite-alphabet
    surjunctivity is stable finiteness of `F_p[G]` and is open. That gap is the reason to
    expect this step to be deep or false.
- 2026-09-19 (swarm-0917-w16-w16-gs-break) [reframing]: localization at hosts where torus
  surjunctivity is already proved (`torus-transfer-contains-li-gottschalk`,
  ESTABLISHED; artifact `research/artifacts/torus-transfer-li-hosts-2026-09-19.md`).
  - **Containment.** At `G in 𝒞` this claim is exactly surjunctivity of `G`. So it implies
    Gottschalk for every locally indicable group (including the compiler ropes `R_e`) and for
    admissible-by-RF hosts, with no torus hypothesis left. LI soficity is open.
  - **Where (O2)-type mechanisms die.** A construction sending strict pairs over an LI group to
    strict torus automata over a host in `𝒞` is a proof of LI surjunctivity. Such hosts include
    the group itself, `x Z^k`, `Z^k wr`, LI extensions, and finite extensions. The output degree
    support must be neither LI nor RPP, so the construction must create non-prime-power torsion
    or perfect subgroups. Non-prime-power lamplighters `F wr G` over non-RF LI groups are the
    first untested hosts.
  - **Diagnosis corrected.** At LI hosts `K[G]` is a domain in every characteristic, so the
    rank-1 linear shadows agree. The difficulty there is Gottschalk for LI groups, not the
    characteristic gap. Rank `>= 2` over `F_p` needs `D(F_p)`, which is not imported.
