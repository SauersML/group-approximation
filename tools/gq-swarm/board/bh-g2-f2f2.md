# bh-g2-f2f2 (gate G2(c): quantum-rigid free minimal SFT over F₂×F₂)

Landed e9de95fc2. Lane proofs, unreviewed.

Theorems:
- coset-invariant-sft-rigidity-descends-along-double-cosets (+ proof): the descent criterion over Δ\Λ/Δ.
- cornulier-regime-coset-sfts-are-quantum-rigid: finite Δ\Λ/Δ ⇒ every coset shift is rigid, and the crossed product is fp.
- set-transitive-coset-shifts-have-only-constant-minimal-sets: (IS) ⇒ every closed invariant set contains a constant.
- two-sided-free-group-coset-sfts-collapse-under-cyclic-descent (+ proof): over F₂×F₂/diagonal, conjugate-short pairs commute for free, but local cyclic descent ⇒ Z finite.

OPEN:
- f2-times-f2-has-a-quantum-rigid-free-minimal-sft: the target; Attempt 1 is recorded there.
- finite-double-coset-space-with-free-minimal-coset-sft: the Cornulier shortcut.

Next leads for a successor:
- coset spaces whose point stabilizers fix a direction (cyclic or parabolic subgroups of the diagonal, e.g. ⟨(a,a)⟩);
- descent with a complexity other than cyclic length;
- (IS)-failing finite double-coset spaces.
Artifact: research/artifacts/gq-bh-g2-f2f2-coset-rigidity.md.

[from bh-openq-papers, 11:40] Literature at source (landed 84c5e8d9a, 348d2c736): Aubrun–Bitar–Huriot-Tattegrain arXiv:2204.11492 l.755 — "There exists a minimal strongly aperiodic SFT on F_n × Z" (Labbé's expansive-direction Z² shift transported along a finite-type flow on the F_n tree); also unimodular GBS and BS(1,n). Node `free-times-z-carries-a-minimal-free-sft`. Rigidity not addressed. For M2: Álvarez López arXiv:1807.09256 gives computable free strongly repetitive points with computable central modulus on every decidable group (see M2 node Attempt 7); only the global/seam modulus remains.

**From bh-g2-fixedpoint-b (11:5x):** free-group-boundary-shifts-are-quantum-rigid landed (201fb24d4). The end shift of F_n is D-rigid for every D over every field (monotone-chain proof). With product stability, ∂T_m ⊠ ∂T_n over F_m×F_n is rigid, minimal and topologically free, but not free. For building-lattice transplants: on products of trees, (H_Ω) and boundary rigidity both hold, so only (C) and Z²-rigidity of Y remain.
