- **Unstable `K_2` (w7-k2-unstable, 2026-09-12): the `K_2(3,R)` option above is empty, and two options remain.**
  * **Candidate** (artifact `research/artifacts/leavitt-unstable-k2-steinberg-reduction-2026-09-12.md`; OPEN claim
    `leavitt-unit-groups-have-no-unstable-k2-at-rank-three`; verification requested from `w4-vf-gate`):
    - `K_2(3,R) = 0` for `R = L_(F_2)(1,2)`: Khanh's Theorem 5.4 at `r = 3` (`leavitt-steinberg-map-iso-from-rank-three`),
      re-derived with Voronetsky's refinement (Proposition 1 at `n = 4`, read from the source);
    - the same for `L_(F_3)(1,2)`, by `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` with `B = F_3`;
    - `K_*(R) = 0` for both, so `K_2(3,R) -> K_2(R)` is injective because both groups vanish.
  * **Effect on the w6-mismatch-c2 list.** Every relation of `R^x` follows from the rank-three Steinberg relations
    alone, each in a subgroup of order at most 8. A relation-only proof of `theta < 1` must use a cycle of Steinberg
    relations that no graph of locally finite subgroups routes, or a global input. There are no symbols and no global
    `K_2` element to model-test.
  * **Hexagon presentation, not a firewall.** `R^x = π_1(Y_hex)/<<t>>`: the six unipotent radicals `U_π(R)` of
    `steinberg-group-is-glued-over-the-permutohedron`, amalgamated around one hexagon, with `t` the closing letter.
    Theorem 1.1 of the firewall artifact models `π_1(Y_hex)` with `σ(t)` a matching permutation, and a model descends
    to `R^x` only when it kills `t`. The `U_π` contain no cylinder frames, so this gives no `D_A` statement, and a frame
    vertex breaks the one-letter quotient.
