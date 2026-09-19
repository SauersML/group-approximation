direction: problem-list hunt (AIM, Oberwolfach, Bestvina, BMS list, MathOverflow, Thompson problem lists) for BH/fp-simple open questions
landed 054ee2eb8: artifact gq-bh-openq-lists.md; nodes higman-group-embeds-in-no-lodha-moore-or-monod-group (ESTABLISHED corollary, answers OWR 2018 Q110 no), fp-simple-group-with-commutator-width-at-least-two, neumann-alternating-product-group-embeds-in-fp-rf-group, e-of-finitely-presented-group-is-recursively-presented (OPEN); provenance lines on fp-infinite-simple-group-not-two-generated and free-minimal-zn-derived-full-groups-are-never-fp. Done.
pass 2, landed 625352151: fg-decidable-group-whose-e-is-not-recursively-presented (ESTABLISHED, lane proof) = f.g. version of MO 412219 answered NO; fp version OPEN with the gap on its node (Attempt 2). The second-pass lists are in artifact §E. The AimPL 3.1(c) node was corrected by bh-free-19 (Caprace–Fujiwara). Done.
pass 3, landed b0dde339c: `dendrite-rearrangement-group-g3-has-simple-commutator-subgroup` (ESTABLISHED, lane proof) answers Tarocchi's question, so [G_n,G_n] is simple for all n ≥ 3. There are 5 new OPEN nodes from 2024–26 papers (graph Houghton BH, dendrite fp, f.g. weakly branch in V, G_0(n) ≤ PPSL, Der of minimal piecewise full groups); see artifact §F. The E(G) sparks were posted on bh-free-08's board.
pass 4 (INSIGHT FIRST), landed 030fa449a: `efrf-groups-frattini-embed-in-efrf-branch-groups` (lit. import plus a lane remark) reduces BBMZ 5.3(2),(3),(7),(12) to EFRF^+ spinal branch groups; `rf-decidable-groups-embed-in-decidable-fg-branch-groups` (Bishop–Schesler Q1.1) is OPEN and reformulated. LESSONS lines appended (4 in total from this lane).

[bh-integrate 11:21, pass 4] MO 412219 cluster. `e-of-finitely-presented-group-is-recursively-presented` is REFUTED (by bh-free-08's node), yet three ESTABLISHED nodes list it in `requires:` for its reformulation E(G) = (G*Z)/J_1(G) (item 2): `fp-decidable-group-whose-e-is-not-recursively-presented`, `mixed-identities-encode-normal-closure-commutation` and `nonrecursive-a2-kernel-makes-e-of-wreath-not-rec-presented`. A dependency on a refuted node reads as broken. Please split the reformulation into its own ESTABLISHED node and repoint the requires. Also, research/artifacts/gq-bh-openq-lists.md row A4 still reads open.

pass 5 (after the restart), landed ca38e5c7b.
- Recovery: nothing was unlanded; all work copies were either the same as main or stale.
- The Grigorchuk-in-fp-RF question is NOT a named problem: Kourovka v46, Grigorchuk's 2005 survey and BGS
  *Branch groups* were searched in full. It is the first test case of Rauzy's printed sufficiency question
  (arXiv:2002.02540v2), and the node is updated.
- NEW OPEN `torsion-free-fp-metabelian-self-similar-group-contains-z-wr-z` = Kourovka 21.41. Kochloukova–Luiz
  conjecture NO. The lane lemma "Z wr Z is linear over no global field" excludes affine witnesses.
- PRIORITY: Kochloukova–Luiz arXiv:2509.05798 already prove Baumslag's group is not self-similar, which is main's
  09-12 node. A citation is added there.
- PRIORITY CHECK (coordinator, arXiv:2607.17477, van Doorn–Judin–Monticone–Morrison, v1 2026-07-20): it claims
  Kourovka 3.46, 18.50, 19.25, 20.125, 21.8, 21.24, 21.147 and 21.150. There is NO overlap with ours (17.57,
  17.59, 17.60, 17.61, 21.73, 21.74(b,c), 21.75; 21.74(a) partial; 5.15 lit; 14.10(c)). Their 21.8
  (CT_(k) ≅ S_{lcm(2..k)}) is a different, finite statement with no conflict, and our 21.75 node already cites it.
- Next: Kourovka 21.140 (Witzel–Zaremsky, torsion-free F_∞ of infinite cd without F?) is unowned and the best
  BH-adjacent issue-21 lead.
pass 6, landed 6dc3f9d10: Kourovka 21.140 = Zaremsky 2.8, and the root now carries the Kourovka number.
- NEW ESTABLISHED `thompson-f-free-groups-closed-under-extensions-and-unions`: F-free groups are closed under
  extensions and unions, so ascending HNN extensions of RF groups omit F.
- NEW route `basilica-hnn-fp-infinity-answers-kourovka-21-140`: B~ is fp, torsion-free, of infinite cd and
  F-free, so 21.140 has answer NO as soon as B~ is FP_∞. The "F non-amenable" premise is
  dropped.
- Next for whoever takes it: FP_3 for B~ (crux `basilica-hnn-extension-is-fp-infinity`).
pass 7 (crux FP_3 of B~), landed 83b85aaed.
- NEW ESTABLISHED `basilica-hnn-has-no-finitely-presented-ascending-base`: B~ is not an ascending HNN extension of
  ANY fp group. Mechanism: the section-inverting σ plus Erschler's theorem (fp covers of B contain F_2). The
  general statement covers any self-similar G with a section-inverting σ, Grigorchuk included.
- Consequence: the homotopical base-change route to F_3 is dead. With the recalled Bieri–Renz criterion,
  Σ^2(B~) = ∅.
- Literature: nothing on FP_n (n ≥ 3) of B~ in BV, GZ, BGdlH or Hartung (Hartung only conjectures the Dwyer
  quotients).
- FP_3 itself is NOT settled.
- Next: (a) de Cornulier's FP_2-cover upgrade for Basilica, which would also kill FP_2 bases; (b) an F_3 certificate
  from a 2-complex on which B acts with Z^k stabilizers; (c) degree-3 Alexander test via H_3(B), using
  St_B(1) ≅ B ×_Z B (the fiber product over ε_a, seen this pass, not landed).
pass 8, landed f36b70ab7.
- NEW ESTABLISHED `basilica-fp2-covers-contain-free-subgroups`: de Cornulier's argument (BGdlH Prop 5.11) transfers,
  since the Basilica standard cover is F_2 and the approximants G_n are residually soluble. So every FP_2 cover of B
  contains F_2, and B is NOT FP_2.
- The ascending-base node gains item 3: no FP_2 ascending base.
- Bieri–Renz was read at source: it has no ascending-HNN characterization of Σ^m for m ≥ 2, so my earlier
  remark is corrected.
- Crux: the certificate constraints are recorded; B must act without a fixed vertex, otherwise the problem regresses.
- FP_3 is still OPEN.
- Next: build B~'s action on Nekrashevych's self-similarity complex (or a Farley diagram complex) and test Brown's
  filtration criterion.
pass 9, landed 615d598a5.
- NEW ESTABLISHED `basilica-hnn-self-similar-geometry-gives-no-brown-certificate`:
  - Nekrashevych's self-similarity graph carries no B-action (it models the shift on J_B).
  - B~ acts faithfully on T_3 fixing an end, extending the self-similar action, but every vertex stabilizer is a
    strictly increasing union ⋃ t^n St_B(1^n u) t^(−n), so it is infinitely generated. Brown's criterion does not apply.
- Crux now carries the exact FP_3 criterion: α = 1 − tσ_* onto H_2(B; ∏ZB~) and injective on H_1(B; ∏ZB~).
- FP_3 is still OPEN.
- Next: that product-coefficient computation through the L-presentation relation module, or a free Morse complex
  (diagram-group test).
