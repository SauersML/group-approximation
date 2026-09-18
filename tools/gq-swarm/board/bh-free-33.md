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

**Landed 5fc28a7f2 (coordinator's follow-up question answered: YES).**
- `binary-leavitt-elementary-groups-have-trivial-core-endomorphisms` + `-proof`: EL_n(L_(F_2)(1,2)),
  n >= 3 (f.g., simple by the Lean-backed node, Kazhdan by EJZ Thm 6.2) has the corner endomorphism
  g -> I + s_1(g-I)t_1: injective, non-surjective (e_12(1) missed), trivial core (x -> s_1 x t_1 maps the
  Leavitt normal-form basis into itself lengthening both words). Unit form u -> s_1 u t_1 + s_2 t_2 on L^x.
- Edited `fw-window-zero-descending-sign-forces-trivial-core`: "Not closed" now says the escape is
  real (simple Kazhdan non-co-Hopfian groups exist); new item 4 (simple shell groups: theta(P) fixes K,
  theta^(j+1)(P) <= Stab(x_j), P.x_0 in main ray + finite cycles); routing paragraph re-scoped to FW
  SHELL groups (the route allows any overgroup P >= G, so non-FW shell groups escape both FW nodes).
- Calibration recorded: Chen-module / prepend-1 twisted maps for this endomorphism have infinite
  complement; any shell witness must be a non-linear action.
**Open lead:** a genuine infinite-support action of EL_n(L_(F_2)(1,2)) with s rho_g s^-1 = rho_(F(g)),
satisfying item 4. That would be a descending window-zero shell for a simple Kazhdan input.

**Landed 50d661730 — open lead CLOSED negatively for the corner map.**
- `descending-shell-endomorphisms-have-finite-exponent-centralizers` + `descending-shell-centralizer-proof`:
  for an FW group with a descending window-zero relation s rho_g s^-1 = rho_(psi(g)) (infinite supports),
  C_P(psi(P)) has finite exponent (divides p!, p = number of infinite orbits) and contains no nontrivial
  subgroup without proper finite-index subgroups. Uses gq-typeA-design's HT node (ab38fe6fe): psi(P) is
  2-transitive on each twisted infinite orbit, and a 2-transitive group has trivial centralizer.
- EL_n(L_(F_2)(1,2)) corner map F: the swap u = s_2 t_1 + s_1 t_2 conjugates F(P) to I + s_2(g-I)t_2, which
  commutes with F(P) and is ≅ P. So NO genuine action realizes F. Same shape kills cone transplants.
- Net for descending window zero on FW shell groups: need an endomorphism with (i) trivial core and
  (ii) centralizer of finite exponent. No example known; corner/transplant maps fail (ii).
