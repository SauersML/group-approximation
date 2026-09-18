# bh-free-33 (free lane: BH from first principles)

**Direction chosen.** Host-construction side for the inputs BH actually reduces to
(`boone-higman-iff-simple-kazhdan-decidable-inputs`: f.g. simple Kazhdan FA with solvable WP),
rather than the input side, which is already reduced.

**Landed 47becd6b0** (lane proofs, unreviewed, no novelty claimed):
- `fw-window-zero-descending-sign-forces-trivial-core` + `fw-window-zero-descending-sign-proof`.
  Strengthens `fw-inputs-admit-no-twisted-shell-normalization`, which closed the ascending sign
  and left the strict descending inclusion open. For an FW input with all supports infinite,
  `s rho(P) s^-1 = rho(theta(P))` forces every element of the core `intersection theta^j(P)` to be
  finitary, hence the core is trivial. So window zero fails at BOTH signs for every co-Hopfian FW
  input (e.g. SL_n(Z), n >= 3, co-Hopfianity cited not read).
  Routing corollary on the node: for Kazhdan inputs the genuine-action shell route needs a window
  N >= 1 with f.p. window group, or a non-co-Hopfian input with trivial core; its only positive
  family (eventually periodic, hence virtually abelian) is never Kazhdan, so it is disjoint from
  the reduced input class.

**Duplicate checks that came out negative (no landing needed).**
- AimPL 3.1(c), fp simple group of commutator width >= 2: already ANSWERED on main via
  Caprace–Fujiwara (`fp-simple-group-with-commutator-width-at-least-two`); I re-read
  arXiv:0809.0470 TeX (Cor `cor:KM:simple`, answering Kourovka 14.13) before finding the node.
  Source at /projects/standard/hsiehph/sauer354/gqsrc/bh-free-33/cf.tex.
- "BH reduces to a computable sequence of single groups, one per exact Dehn bound":
  blocked, and already documented. Exact-bound classes D_f have uniformly solvable WP but are
  co-c.e., not c.e., so part 2 of `common-decidable-hosts-iff-uniform-word-problem` does not
  apply; that node's corollary already records that no f.g. decidable host exists even for
  Dehn function <= n^18 (constants unbounded).
- The input side is already maximally reduced (simple + Kazhdan + FA), so no gain there.

**Open leads for successors.**
- Does any f.g. simple Kazhdan group admit an injective endomorphism with trivial core?
  A "no" would close window zero for the whole reduced input class outright.
- Window N >= 1 for a Kazhdan input, with f.p. window group W_N (see bh-shell-germ's
  `fp-window-group-makes-shell-germ-group-fp`): the one surviving shell shape.
