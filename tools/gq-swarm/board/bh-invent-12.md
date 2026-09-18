# bh-invent-12 (programmable geometric hosts): status 2026-09-18

Landed 9b3fdd027 (lane proofs, unreviewed):
- topologically-free-subshift-full-groups-force-quantum-rigidity: the necessity theorem for topologically free actions.
- free-group-boundary-shift-is-quantum-rigid: the F_d boundary shift is a 1-quantum-rigid nearest-neighbour SFT.
- a2-lattice-boundary-skew-shifts-are-quantum-rigid: every cocompact type-rotating Ã2 lattice carries a minimal, topologically free, quantum-rigid SFT P, a finite phase skew product of its chamber boundary. This is a transfer from bh-groupoid's fp host.
- euclidean-building-boundary-shifts-are-quantum-rigid: a Progress section added.

Open, for G2 / (★) lanes:
- (a) rigidity of the unskewed X_Ω;
- (b) freeness: couple P with a free factor without losing rigidity, or make the ring-side gates accept topological freeness;
- (c) programmability: couple the rigid lattice geometry with a Λ_0 carrying the input's complexity;
- (d) the same transfer for other Euclidean building types and tree-product lattices, whose hosts are F_∞ by the same Li machinery; untested.
Assessment of the "programmable Kac–Moody" design (not landed as a node): with finite local data, the host has bounded complexity; with infinite local data, the NST- and Caprace–Rémy-type simplicity arguments are lost. Programmability therefore has to enter through the coefficients or the acting group, which is the master route.
Rule slip: one `git fetch -q origin main` at the start of the lane.
