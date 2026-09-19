# bh-pal-steinberg (Palomar BH megasubmission: T1, Kourovka 14.10(c) / BBMZ 2.7, St_10(R_L))

Direction: prove T1 `explicit_fp_overgroup_of_all_gl_n_q` in Lean (Mathlib only) and wire it into
`Palomar/BooneHigmanSolution.lean`.

## Established (on main)
- GroupApproximation/SteinbergFP/* (12 modules), green on MSI, axioms propext/Classical.choice/Quot.sound:
  6bcb1cdd2 (R_L, St_{d+5}(R_L) f.p., doubling, diagonal, swap, intertwine, room, Morita),
  1637708b6 (Swindle + Embedding: every GL_n(Q) ↪ St_10(R_L), St_10(R_L) f.p.),
  2539180c0 (Challenge.lean: the statement over byte-identical copies of the challenge's defs),
  6fefc9b9c (docstrings); f8d46d836 (ElemFPKMRoots elaboration fix).
- 09-18 14:30 relaunch: all lane work files are identical to origin/main; nothing was lost.

## Done 15:40
- a7d68b30b: route node gl-n-q-all-n-in-st-10-of-resolvent-ring records the Lean proof (four parts to modules) + lesson.
- LESSONS append (swindle needs no field; ring side owes only the K-gate). Prefix registered in LEAN-OWNERS.
- T1 wiring HANDED OFF to bh-pal-surface (owner of Palomar/BooneHigman*, scripts/PalomarBooneHigman*, yaml):
  drafts in work/bh-pal-steinberg/{Palomar/BooneHigmanSolution.lean, scripts/PalomarBooneHigmanAxioms.lean,
  formalization.yaml}, base ddeea47ea; the gate passes; gqprobe of Palomar.BooneHigmanSolution queued 15:35.

- 16:25 (user order "land everything"): the three drafts are bh-pal-surface files and its v2 rewrite is in flight, so I SENT them to it (SendMessage with a drop-in snippet) instead of landing them. My SteinbergFP modules are green, so no fix nodes are needed.

- 16:50: bh-pal-surface wired T1 in surface v3 (654ec6838). T1 is proved outright in the Solution, and the Axioms driver and yaml are updated. My drafts are SUPERSEDED (do not land them), and my probe of the old draft was withdrawn. The surface owns the v3 probe.

## Next
- The char-p twin: an f.p. F_p-Leavitt-resolvent ring (LESSONS 116). The swindle and Morita already hold
  for any ring, so only the ring presentation, its faithful module and F_p ⊆ center are new.

## Sparks
- Swindle is stated for any ring S with a binary Leavitt family and any injective φ : F →+* S commuting
  with t₀, t₁ (F ANY ring with St_V(F) perfect; `exists_injective_elementary`), so the same proof gives GL_n(F) ↪ St_10 over a
  char-p Leavitt-resolvent ring (the F_2 route in LESSONS 116) once that ring's f.p. is stated.
