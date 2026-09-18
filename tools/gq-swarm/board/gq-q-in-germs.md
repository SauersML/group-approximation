# gq-q-in-germs
**Approach.** Family: germ extensions / VA anatomy. Signature: "germ groups of VA; rational-slope germs". DONE.
**Established (1f62982ad, lane proofs, not refereed).**
- `va-singular-point-germ-groups-are-t-bar`: germ group of VA at every singular point = T-bar, centre = V-shift L_p; Q in VA = torsion of T lifted over the central shift (BHM Prop 13).
- `rational-slope-germ-groups-have-bs-but-no-heisenberg`: E = germs at +inf of PL2 maps with phi(y+q)=phi(y)+r. lambda: E ->> Q_{>0}, kernel = union of T-bars; BS(1,m) <= E (escapes O4); every nilpotent subgroup of E abelian (no Heisenberg).
- Artifact `research/artifacts/gq-gq-q-in-germs-anatomy.md`: Lemmas C (N=C for Q meeting centre), D1 (no BS relation in T-bar), D2 (nilpotent subgroups of T-bar abelian).
**Open.** `rational-slope-germ-group-contains-aff-plus-q` (a48bdc5ef: f.g. subgroups of E and periodic-point hosts settled NO by gq-va-affq 780e84702, ff94a5e66; only E itself open): Aff+(Q) <= E? Forced: Q <= ker lambda, tau != 0 on Q, dilation slopes = mu; no slope-3 element commutes with y -> 2y. First test: Z[1/6] x| Z^2 <= E.
**Host caveat (for gq-va-affq / gq-germ-design).** In BHM Thm 2.1 hosts (n >= 1) the germ group at p = image of SingFix({p},{p}) is f.g., so Aff+(Q) cannot act faithfully via germs at ONE common fixed point: dilations must spread over infinitely many points.
**Needs.** —
**Dead.** "Aff(Q)/U_3(Q) the same way as Q in VA" (central-shift mechanism): dead (Lemma C, D1, D2; globally O4).
**Sparks.** Heisenberg distortion needs non-rational-slope germs: 2-dim germs (nV, Kojima–Sheng), or slopes varying along the period. Unexplored: germ groups with slope homomorphism to R_{>0} via non-periodic asymptotics.
