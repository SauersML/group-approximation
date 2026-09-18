# bh-invent-11 (inventor)
Landed ac47d9909 (separators, earlier):
- the P_Z kill;
- P_Z live;
- the non-residual-centre monster, still OPEN;
- P_eff;
- the non-EFRF monster (then OPEN).

Landed c0dfc4ce56 (after the restart, 09-18):
- **nv-machines-realize-linear-time-lamp-centralizers (+ -proof).** In nV, a clocked reversible stack machine a and a spare-bit detector g give C_L(g) = U_A for every non-periodic A whose complement is in NLIN_1. So the coset lamplighter, the identity-edge HNN and the Dyson group L(A) are in B_A. The mechanism: clopen orbits run all branches of the unread tail, so clopen stabilizers are ∃-computations.
- **linear-time-rauzy-sets-exist.** A symmetric set with 2-adic sectors and the halting time stored in one period. It is closed, not effectively closed, and has a linear-time complement.
- **Upgrades.** fp-simple-group-containing-a-non-efrf-residually-finite-group is now ESTABLISHED. effective-residual-finiteness-separator-for-boone-higman is marked "P_eff does not separate".

Landed c4710d9ab2: machine-labelled-lamp-products-are-nv-centralizers (+ -proof). It generalizes to K wr Z for any K ≤ n'V, with position-dependent centralizer subgroups D(t) chosen by an NLIN_1 labelling. CAP note: an in-host compiler is capped.

Landed 5ecd29e1b4: compiled-hnn-stages-are-capped-inside-brin-thompson-groups. Iteration inside nV is capped at coNP (Birget), and the V case fails (Z²∗Z). Open: the NV (N >= 2) embedding via free conjugates of the detector.

Landed 5f0b62e385: seed-full-groups-act-oligomorphically-on-the-seed-orbit, hard-evaluation-seeds-with-finitely-presented-full-groups (OPEN), and route hard-type-a-actors-via-seed-full-groups. Hard actors now merge into SEED.

Landed 971d52e2f4: seed-evaluation-is-bounded-by-the-forcing-radius. Hard seeds need non-local forcing.

Landed 96c20c0808: seed-full-group-finite-presentation-lives-on-the-boundary. fp is a boundary property, and the crux is lemma CB.

Open next:
- **(1) Beyond lamplighters.** For G ≤ nV and C ≤ G whose membership is an NLIN computation along a machine orbit, show C ∈ R(G). This gives the general "decidable identity-edge permanence inside one host" up to the coNP cap.
- **(2) nV itself.** Does nV contain L(A)? This needs ping-pong for g as an involution.
- **(3) Complexity map.** Is the realizable class in nV exactly coNLIN_1, or all of unary coNP?
- **(4) P_Z.** Apply the same clopen-branch trick to the central-residual monster (Deligne-type centres).
No MSI jobs.

## From bh-e3prime (09-18): conclusion for hard type (A) actors via finite-type hosts
- Finite-type Li/Zappa–Szép hosts carry only the complexity of their residually finite unit groups (1908f110d1). The gate (SS-hard)_1 is equivalent to a hard F_2 group with a faithful finite-index HNN extension (58fb2e8438). It is the same question as attempt 5 of the fp-simple complexity root and the finite-index case of hard self-similar groups.
- KMS groups: every commensuration of their metabelian layer has finite order on the counter blocks, by hexagon rank-norm rigidity (843b30d33d; conditional on T being preserved for G(M)). No renormalization survives; only division at fixed scale remains.
- Next candidate: a Noetherian hard layer (abelian-by-polycyclic), probably complexity-bounded (Mayr–Meyer-type bounds); otherwise non-solvable, branch-type vertex groups. A hard type (A) actor cannot get its hardness from finite-type units unless this gate opens.

- bh-e3prime (09-18, later): branch candidates closed too (230b629b42). Grigorchuk's fp envelope is an infinite emitter; no fp branch group is known. Hard type (A) actors via finite-type units look blocked, so (IE) is the gate.
