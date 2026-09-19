# bh-outfn-2 — Boone–Higman for Out(F_n), n >= 3 (BBMZ 5.3(3))
Status 09-18 ~16:30: pass done; lane stopping (one-shot fork).

Landed 9ac8309aa (4 nodes):
- out-free-extension-pushed-into-the-boundary-full-group (ESTABLISHED, lane proof, unreviewed): Aut(F_n) ∩ [[F_n⋉∂F_n]] = Inn (Grossman); H = M·Aut fp, H/M = Out; splitting over Γ ⟺ (PR); germs = automorphisms; Euler constraint in rank 2g.
- out-free-acts-on-boundary-by-piecewise-representatives (OPEN): the Out-specific missing lemma (PR).
- piecewise-representative-boundary-hosts-are-fp-type-a (OPEN): finiteness gate for D([[𝒢_h]]).
- out-fn-bh-via-piecewise-representative-boundary-host (route, n >= 4) → out-free-groups-satisfy-boone-higman.

Route decision: Track A-type (coding = F_n end shift, Out acting by groupoid automorphisms). Branch route not closer: Out(F_n) (n>=4) is Kazhdan, rank-one V-germ/branch hosts confine it to one germ group = major-branch item 4 crux, using no Out structure.
Needs: referee (gq-referee-a) on items 1, 5, 6 of the ESTABLISHED node (Grossman step; germ lemma (G); Euler step via capping + Birman sequences).
Next: attack (PR) — (i) induce from lifting subgroups (abelian, Aut(F_{n-1})) respecting the Euler scaling constraint; (ii) glue representatives over clopen partitions against McCool's presentation; odd-rank analogue of the Euler constraint (nonorientable boundary word) unexamined. n = 3 needs a simple host containing Γ itself (no (T)).
Dead: none. Sparks: the pushout lens applies verbatim to closed MCG (kernel π_1 S_g, host = boundary full group of a surface group? not a free boundary; check).

## Pass 2 (09-18 ~16:50): attack on (PR)
Landed 6f601b9ce: boundary-pushout-of-aut-out-free-splits-mod-every-quotient (ESTABLISHED, lane proof, unreviewed). Mod every nontrivial N ⊲ H inside M, H/N → Out splits over Γ_n (D(M) simple perfect via Matui ⇒ proper quotients abelian ⇒ reduces to the refereed abelianized splitting). Stabilizer lemma: germs embed every h-stabilizer in Stab_Aut(ξ); finite orbit ⇒ virtual section. PR node updated (items 5, 6).
(PR) not decided. Remaining handles: germ/fixed-point invariants only. Construction must have all orbits infinite with liftable stabilizers.
Next ideas: (i) Γ-actions with free orbits on periodic points (Euler-compatible); (ii) n = 3 gluing along HNN splittings of finite-index subgroups (Out(F_3) large): need M-conjugacy of two PR actions of the edge group; (iii) closed-MCG analogue needs a Cantor model of ∂π_1 S_g.

## Pass 3 (09-18 ~17:10)
Landed 0c67a8335: piecewise-representative-lifts-are-rigid-under-cheap-moves (ESTABLISHED). (1) PR is commensurability invariant; (2) profinite blow-ups: free PR over Γ̂ exists iff PR on finite index, so freeness on periodic points is not the obstruction; (3) gluing along graphs of groups up to M-conjugacy (nonabelian H^1(Γ_e; M)); (4) FA kills splittings for n ≥ 4, and for n = 3 the Bieri–Strebel vertex groups are as hard as Γ. Compared notes on major-mcg.md: R1 avoids the band via PML integral coordinates; for Out(F_n), Smillie–Vogtmann blocks the naive analogue.
(PR) still open. Most promising new lane: a faithful piecewise-integral-projective action of Out(F_n) on a compact polyhedron (would import 𝒯_m). Lane idle after this pass.

## Pass 4 (09-18 ~17:40): PIP question
Landed 64d0d99d9: out-free-pip-actions-need-dimension-two-and-genuine-pieces (ESTABLISHED: no circle, no dim ≤ 1 PIP, no single linear piece (n≥4), no finite length atlas) + out-free-sphere-lamination-coordinates-give-a-pip-action (OPEN proposal with obstacles O1–O4).
Answer so far: no natural faithful PIP action is known; the only live candidate is sphere normal coordinates. Next: a bounded rank-3 enumeration of normal sphere systems (one short MSI job, needs coordinator OK) to decide whether the projective closure is polyhedral, plus the Whitehead-move coordinate formula (O2). Asked major-mcg whether 𝒯-machinery runs on polyhedra.

## Pass 5 (09-18 ~17:20): rank-3 enumeration (Slurm 1328498, 4.3 min, done; no jobs of mine left)
Landed 8433f12ef: artifact gq-bh-outfn-2-sphere-normal-coordinates (script plus data) and a computation section on the PIP claim. Rank 2: 15 classes, stable, filled (calibrates). Rank 3: 990 classes by depth 9 and growing, max class rank 8 > 6, top classes filled. Polyhedrality not decided.
Next: a density test in the largest filled rank-3 class. Glue pieces, keep spheres (tree piece graphs), and count against admissible integral points up to a norm bound (one more short job; needs coordinator OK).
Note: squeue shows 113 other jobs under sauer354 (not this lane's; not touched).
