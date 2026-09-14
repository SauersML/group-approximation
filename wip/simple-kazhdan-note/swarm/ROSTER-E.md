# SK roster E: wave 7 (~19:35)

- Rev1 is on main at 5b1890ce6c (md5 8e04b341…). Read it with `git show "${T}:simple_kazhdan_sofic_group.tex"`.
- Main's decision log: `sk/drafts/rev2-decisions.md`.
- Queue review requests with `sk/queue/sk-verify-5.txt`.

## sk-characters-rigidity-a and sk-characters-rigidity-b
Target: every extreme character of G_X is 1 or δ_e. Then every ergodic invariant random subgroup is trivial, and L(G_X) is the only II_1 factor representation of G_X.

What is known: sk-characters' Theorem A (18375ec10e; `research/artifacts/sk-characters-root-continuity-2026-09-13.md`) says that characters continuous on small root elements are trivial. So the missing step is that every non-regular extreme character tends to 1 on small root elements.
- Start (a): property (T) and angles between the fixed spaces of the finite groups SL_n(F_{2^k}) inside G_X that contain the generators, in a Peterson–Thom-style argument.
- Start (b): replace the Dudko–Medynets endgame using germ projections and Kakutani–Rokhlin partitions, or restrict to the lattice EL_3(F_2[u^{±1}]) and import character rigidity of lattices.
- A counterexample, a nontrivial character, counts equally.

Peers: each other.

## sk-lef-growth-all
Target: L_X(r) ≥ exp(c r²) for every infinite minimal subshift X.
- sk-lef-growth (45a8a34e9e) proved exp(Θ(r²)) for every Sturmian X.
- It also proved the short-tower criterion: a clopen W with no returns up to 2m, whose transvections have O(m) letters, forces L_X(r) ≥ 2^{d(d−1)/2} with d = 3(2m+1).
- Find such cheap towers for every X, or an X whose LEF growth is smaller.

## sk-k2-subsystems
Does the unstable K_2(3, LC(Y,F_2)⋊Z) vanish for every aperiodic subshift Y? If so, normal subgroups of EL_3(R_X) correspond exactly to closed invariant subsets (sk-open-1, d2384bf1e8; open claim `aperiodic-subshift-ring-unstable-k2-vanishes`).

Routes:
- van der Kallen stability;
- Steinberg relations with local units on towers;
- Stepanov condition (b) (sk-stable-rank-b, 7ff75787cb).

## sk-labbe-matricial
Is LC(X,F_2)⋊Z² exactly matricial, i.e. LEF as a ring, for Labbé's minimal aperiodic 19-tile SFT? Equivalently: does it have periodic quantum tilings at every scale? Read the Labbé ring nodes on main (grep `labbe`) and sk-fp-sofic-b's firewalls.
- A yes gives simple Kazhdan LEF groups with no periodic approximations.
- A no, together with finite presentation of the ring, gives non-LEF simple Kazhdan groups over Z². This bears on the question of a finitely presented sofic simple Kazhdan group.
