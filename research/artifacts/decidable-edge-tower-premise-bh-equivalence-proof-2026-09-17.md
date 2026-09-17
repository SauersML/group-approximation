# Push the decidable FA envelope into a base piece

*Attempt artifact (2026-09-17), formerly route `decidable-edge-tower-premise-bh-equivalence-proof` into `decidable-edge-tower-premise-is-equivalent-to-boone-higman`, requires [decidable-groups-have-decidable-fa-envelopes, fa-subgroups-of-graph-towers-lie-in-base-pieces]. Demoted from the graph because one of three referee votes was lost; the two returned votes found no gap. Restore it as a route once a full referee pass survives.*

**(a)** Let `G` be finitely generated with solvable word problem. By
`decidable-groups-have-decidable-fa-envelopes`, `G <= W_G`, where `W_G` is
finitely generated, has solvable word problem and has property FA. Since `C` is
tree-universal, `W_G` embeds in a graph tower `K` over bases `B_1, ..., B_r` in
`C`. The image of `W_G` is an FA subgroup of `K`, so by
`fa-subgroups-of-graph-towers-lie-in-base-pieces` it is conjugate into some
`B_i`. Hence `G <= W_G` embeds in `B_i`, which is in `C`.

**(b)** (`=>`) Assume `decidable-groups-embed-in-decidable-edge-towers`. Let `C`
be the class of finitely generated groups that embed in a finitely presented
simple group. The premise yields, for every decidable input, an iterated HNN
extension over a single base `B` in `C`. This is a graph tower over `C` (the
decidability of the edges is not used here), so `C` is tree-universal. By (a),
every decidable `G` embeds in a member of `C`, and hence in a finitely
presented simple group. That is `boone-higman-conjecture`.

(`<=`) Assume `boone-higman-conjecture` and let `G` be decidable. Take `B = G`,
which embeds in a finitely presented simple group, and the tower of length
`n = 0`. Then `G <= K_0`.

**(c)** A reduction of the stated form certifies the conjecture exactly when
`C` is tree-universal for decidable groups. By (a), `C` then contains a copy of
each `W_G`, and every decidable `G` embeds in a member of `C`, which by
hypothesis has a finitely presented simple envelope. So the permanence step is
unused. `∎`

## Consequence for the edge-tower route

In `boone-higman-via-decidable-edge-towers`, the first premise alone already
implies the target, and the second premise
`bh-embeddability-survives-decidable-edge-hnn` is idle. The route is valid but
is not a reduction.
