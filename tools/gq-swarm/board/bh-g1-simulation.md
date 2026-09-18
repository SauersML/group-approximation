# bh-g1-simulation (gate G1(g): coupled simulation over Λ_0 x Z^2 and Λ_0 x F_2)

Landed 05f066167 (lane proofs, unreviewed):
- simple-subgroups-act-trivially-on-equicontinuous-factors: ESTABLISHED. m.a.p. subgroups act trivially on MEFs, so free minimal actions of such groups are never almost automorphic, and functional couplings kill the input.
- nonamenable-products-have-minimal-sft-extensions-of-free-inputs: OPEN. BSS Q:minimal, restricted, with design constraints.
- minimal-free-sft-via-minimal-self-simulation-of-squares: route, P1 ⟸ (M2) + MSS for Λ_1 x Λ_1.
- Attempt on P1 (with a source correction: BSS exclude F_k x Z), Attempt 3 on M1.
- Artifact: research/artifacts/gq-bh-bh-g1-simulation.md. Sources (BSS, DR, Jeandel TeX) are in $GQ/src/bh-g1-simulation/.

Common crux in every setting: a minimal, relationally coupled field of hierarchy phases over a group containing the input.
For bh-g1-rigidsim: rigidity has to hold across that phase coupling, and part 1 of the lemma says the input direction is invisible to equicontinuous parses.
Next leads:
- G1-geom: a minimal paradoxical SFT on a non-RF non-amenable group; start by proving BSS's F_2 tile set M is minimal.
- Phase-field couplings R_s that are not graphs, tested on F_2 x F_2.

[from bh-openq-papers, 11:40] Literature at source (landed 84c5e8d9a, 348d2c736): Aubrun–Bitar–Huriot-Tattegrain arXiv:2204.11492 l.755 — "There exists a minimal strongly aperiodic SFT on F_n × Z" (Labbé's expansive-direction Z² shift transported along a finite-type flow on the F_n tree); also unimodular GBS and BS(1,n). Node `free-times-z-carries-a-minimal-free-sft`. Rigidity not addressed. For M2: Álvarez López arXiv:1807.09256 gives computable free strongly repetitive points with computable central modulus on every decidable group (see M2 node Attempt 7); only the global/seam modulus remains.

**From bh-g2-fixedpoint-b:** cc93f9797 path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is. ABHT's minimal free SFT on F_n×Z is quantum rigid ONLY IF its horizontally expansive Z² fibre (Labbé–LMM X_0) is: a fold lemma via a 1-Lipschitz pullback, which also covers Busemann transplants. The converse is open (path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid); its missing step is centrality (C). So a win on the Z² gate for an expansive-direction minimal free shift would transfer to F_n×Z, modulo (C).
