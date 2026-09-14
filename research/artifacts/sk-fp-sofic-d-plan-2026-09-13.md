# sk-fp-sofic-d plan (2026-09-13)

## Target

Q1, starting from group-theoretic candidates: find a finitely presented infinite simple group
with property (T) that is sofic, or at least hyperlinear. In this form it is Alekseev–Thom Open
problem 6.1, and it is the closing question of the note on main.

## State on main at the start (bounded read)

- `km-246-lattice-is-sofic`, OPEN:
  - the IRS-rigidity gate (`almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`);
  - the one-stable-letter certificate over the virtually free spanning-tree amalgam;
  - the measure-equivalence route through Păunescu's class;
  - character rigidity (unreviewed).
- `titz-witzel-soficity-is-one-finite-csp`, OPEN: three permutations, twelve words, and
  non-collapse of y^8.
- The binary Leavitt unit group is nonsofic.
- Firewalls already recorded:
  - linear, affine and projective targets force LEF (42196f9cb2);
  - isolation of SFT points;
  - Proposition F;
  - amenable and Haagerup orbit full groups;
  - the permanence closure;
  - affine Levi triangles, which show Kazhdan-type inputs alone cannot decide the question;
  - the Hamming support metric in cosystolic theorems.

## Approach (d)

1. **Candidate scan** beyond Caprace–Rémy and Titz Mite–Witzel:
   - simple lattices in products of Davis complexes (arXiv:2605.09493);
   - finitely presented groups with strong fixed-point properties and (T) (arXiv:2601.22907);
   - measure equivalence of finitely presented simple groups (arXiv:2101.09071).

   For each, record whether it is finitely presented, simple, Kazhdan and IRS rigid, and what its
   approximation status is.
2. **Firewall to prove: homogeneous near-developments collapse.** Let Λ be the colimit of a finite
   complex of finite groups, with no nontrivial finite quotient. Consider almost actions in which
   the vertex groups act through homomorphisms into one finite group Q_n, acting on the model set
   with a uniform fixed-point-ratio gap. Such almost actions are trivial off o(d_n) points.
   - Targets covered: regular actions, and primitive actions of groups of Lie type (Liebeck–Saxl
     minimal degree).
   - This carries the linear/affine/projective gap theorem of the ring route over to
     group-theoretic targets.
3. **Finite evidence on the Titz Mite–Witzel CSP** (MSI, bounded): structured-ansatz searches for
   triples with small defect and no collapse. The output is reported as defect curves, evidence
   only.

## Not duplicating

- sk-fp-sofic-a: the ring-route firewall.
- sk-fp-sofic-b: rings over Z² subshifts.
- The ex-fp-kazhdan-* lanes: the km-246 gate and the Titz Mite–Witzel CSP reduction.

## Deliverables

- An open-status update.
- A firewall node with its proof, plus an artifact.
- A §6 proposal only if the note's question sentence has to change.
