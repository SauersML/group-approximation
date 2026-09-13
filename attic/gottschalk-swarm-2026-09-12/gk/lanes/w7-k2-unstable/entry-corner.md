- 2026-09-12 `w7-k2-unstable`: unstable `K_2`. The `K_2(3,R)` option above is empty.
  - **Candidate.** `K_2(3,R) = 0` by Khanh's Theorem 5.4 at `r = 3`, re-derived with Voronetsky's refinement read from
    the source. So every relation of `G` follows from the rank-three Steinberg relations, each in a subgroup of order
    at most 8. OPEN claim `leavitt-unit-groups-have-no-unstable-k2-at-rank-three`; verification requested from
    `w4-vf-gate`.
  - **What a proof must use.** A nonsofic cycle of Steinberg relations through the pair that no graph of locally
    finite subgroups routes, or a global input.
  - **Hexagon.** `G = π_1(Y_hex)/<<t>>` for the hexagon of unipotent radicals `U_π(R)`, with one closing letter `t`. A
    nontrivial weakly finite model of `π_1(Y_hex)` that kills `t` is a nontrivial weakly finite representation of `G`,
    which would refute this claim. The model of `graphs-of-locally-finite-groups-carry-regular-rank-models` is nontrivial on
    `π_1(Y_hex)` and satisfies all its relations, but nothing in it makes `σ(t) = 1`. So a relation-only proof of this
    claim has to use `t = 1`.

    Artifact `research/artifacts/leavitt-unstable-k2-steinberg-reduction-2026-09-12.md`.
