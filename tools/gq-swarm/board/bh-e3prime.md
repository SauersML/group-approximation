# bh-e3prime
Direction (09-18 ~15:30): make E3′ (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) the primary E3 gate and prove it beyond finite-state codings.
Status: pass done (09-18 ~16:30). Landed 1908f110d1:
- nonascending-hnn-end-shifts-satisfy-e3-prime (+ -proof), ESTABLISHED lane proof:
  - E3′ at F_n for end shifts of non-ascending HNN extensions of F_n groups H under the half-tree condition (TF);
  - Li ex:ZS (II) on (C_2 × C_E) ⋈ 𝔊 with units = the edge groups;
  - calibration: BS(m,k) with |m|≠|k|.
- finite-type-e3-prime-hosts-carry-complexity-in-units, ESTABLISHED: in finite Zappa–Szép k-graph codings WP(host) ≈ WP(units) up to an exponential, and the units are RF; emitter lemma for tree hosts.
- The E3′ gate node now lists the new instance and the "primary form" reading.
Open, named: (SS-hard)_k = RF groupoids of type F_2 with finite self-similar k-graph structure and arbitrarily hard WP. Unknown even for k = 1. Candidates to test: KMS solvable RF groups (self-similarity unknown).
No MSI used.
- 58fb2e8438: faithful-finite-index-hnn-upgrades-to-half-tree-free (BS twist on A×Z: faithful ⟹ TF). So (SS-hard)_1 = attempt 5 of the complexity root = the finite-index case of hard self-similar groups. KMS structure lemma and test: every available commensuration shape is dead; (SS-hard)_1 stays OPEN. Next: Σ^1 of the KMS metabelian layer.
- 843b30d33d: kms-metabelian-layer-commensurations-have-finite-order (hexagon rank norm; no homothety; KMS renormalization dead mod T-preservation; division is the only shape left; next candidate: Noetherian hard layer). Told bh-invent-11 via its board.
- 230b629b42: grigorchuk-type-vertex-groups-fail-ss-hard-at-the-emitter (Grigorchuk substitution HNN is an emitter: [G:φ(G)]=∞ via θ onto D_8; branch groups are not known to be fp; hardness needs infinitely many types; abelian-by-polycyclic probably bounded, lane sketch). Conclusion: (IE) is decisive.
- a6ed9fc3c2: grigorchuk-envelope-emitter-reduces-to-ie-prime-for-grigorchuk (branch set = free orbits of G via sections; blow-up needs (IE′) for G itself; open; not a concrete instance).
- a0adfac690: grigorchuk-schreier-tip-seeds-a-non-free-orbit (one-defect lemma; Schreier-tip branch seed for G/P isolated and dense; finite type and free orbits open; growth obstruction to Cannon seeds not proved).
