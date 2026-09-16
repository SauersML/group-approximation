# hyperbolic-groups-virtually-torsion-free — frontier swarm lane, 2026-09-16

Agent label: `hi-fron-hyperbolic-groups-virtually-to`. Angle: FRONTIER (map the open
holes under the root, attack the one with the best leverage × tractability).

Status: DONE for this lane. Outcome: partial progress. The hole stays OPEN.

## 1. Frontier map (subtree of the root, 2026-09-16)

I read the root section of `research/FRONTIER.md`, which lists about 145 ids
under the root. The open holes fall into three families.

- **Positive direction.** The route is
  `hyperbolic-virtual-torsionfree-via-finite-residual` →
  `hyperbolic-finite-residual-is-torsion-free`. One sub-route goes through
  `every-hyperbolic-group-is-good`. That is Serre goodness for all hyperbolic
  groups, which is at least as hard as the root. No tractable sub-hole.
- **Triangle-of-groups direction.** The chain is
  `non-vtf-hyperbolic-from-non-vtf-triangle` →
  `hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free` →
  `hyperbolic-simple-triangle-group-without-finite-quotients`. This is a
  hyperbolic Neumann–Neumann problem. It needs a global obstruction to every
  finite quotient, and no candidate is in the tree.
- **Non-RF direction.** The hub is `non-residually-finite-hyperbolic-group`.
  The root is equivalent to it via `hyperbolic-rf-question-equals-vtf-question`
  and `universal-hyperbolic-vtf-iff-rf`. Its open sub-routes are:
  - the MF, nonsofic, quotientless, residual prime torsion and torsion-free
    variants;
  - local restricted Burnside at a large odd exponent;
  - the central Rips pullback, i.e. excluding one prime from the centres of
    finite quotients;
  - Chapman–Peled random complexes, via a Cheeger constant against the
    triangle count;
  - persistent degree-two classes;
  - `non-rf-hyperbolic-via-kms-reflected-root-word`.

  The refuted routes (✗) are: compression transplant, free lamps, Hull
  routing, periodic Higman, the Oyakawa graph wreath, the lattice-forced
  quotient and odd-period exclusion.

Only the KMS route is an explicit finite presentation with a proved
geometric half. Its sibling `kms-hc1-reflected-root-word-is-nontrivial` is
✓: `Gamma_p` is hyperbolic with (T), and `w_p` has infinite order. So the
whole root reduces to one universally quantified identity in finite groups.
Every other non-RF sub-route still lacks its candidate group.

## 2. Chosen hole and why

Hole: `kms-hc1-finite-images-kill-reflected-root-word`. It was locked for this
lane with `--ttl 180m`.

- **Leverage.** If the hole is proved, `non-rf-hyperbolic-via-kms-reflected-root-word`
  closes. That gives `non-residually-finite-hyperbolic-group`, so the root is
  settled NEGATIVELY. If the hole is refuted for every `p>=7`, this concrete
  candidate family dies, which is also useful pruning.
- **Tractability.** The statement is concrete: finitely many relators, one
  word, and a finite-group identity. It can be tested on explicit finite
  images and finite-index subgroups. Its local structure (Heisenberg vertex
  groups) is fully computable. An intermediate quotient could make the
  statement geometric.
- **Deliberately not chosen.**
  - `every-hyperbolic-group-is-good`: at least as hard as the root.
  - The random-complex Cheeger hole: a probabilistic estimate with no
    handle on its constants in this lane.
  - Local restricted Burnside: a known hard problem in finite group theory.

## 3. External gate

(to be filled)

## 4. Mathematics

(to be filled)

## 5. Where approaches die

(to be filled)

## 6. What to try next

(to be filled)
