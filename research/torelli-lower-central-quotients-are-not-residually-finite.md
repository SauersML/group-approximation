---
rg: 2
id: torelli-lower-central-quotients-are-not-residually-finite
kind: claim
title: For g >= 3 and c >= 2 the Kazhdan groups Mod(S_g)/T_g[c+1] are not residually finite; up to a finite central kernel they contain a group commensurable with a Deligne lattice over Sp_2g(Z)
distinct_from:
  torelli-lower-central-quotients-do-not-virtually-split: that is the non-splitting input; this uses it, with Borel and Deligne, to produce a nontrivial finite residual.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that is Deligne's lattice itself; this finds a commensurable copy (modulo a finite central subgroup) inside the Torelli lower-central quotients, so their non-residual-finiteness is inherited from Deligne's theorem.
  deligne-lattice-satisfies-boone-higman: that is the BH test case for Deligne's Sp_4 lattice; this places Deligne-type lattices over Sp_2g (g >= 3) inside the Nowak quotients, so a BH host for a Nowak quotient contains one.
requires:
  - torelli-lower-central-quotients-do-not-virtually-split
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
artifacts:
  - research/artifacts/gq-bh-bh-free-38-torelli-quotients.md
---

**ESTABLISHED** by `torelli-lower-central-quotients-not-rf-proof`. This is a lane
proof, not reviewed, and no priority is claimed. Its inputs are cited:
- Nowak's paper, read in TeX;
- Hain's central line, as quoted by Nowak;
- Margulis superrigidity and vanishing of H^1;
- the Levi decomposition of the relative completion;
- Borel's computation of H^2;
- Deligne's theorem, via the repo's citation nodes.

**Statement.** Let `g >= 3`, `c >= 2`, and `Q_{g,c} = Mod(S_g)/T_g[c+1]`
(notation of `torelli-lower-central-quotients-do-not-virtually-split`).
1. `Q_{g,c}` contains a subgroup `E` with a finite central subgroup `F` such that
   `E/F` is a central extension of a finite-index subgroup `S` of `Sp_2g(Z)` by
   `Z`. Its class has infinite order. `E/F` is commensurable with the Deligne
   lattice `S~`, the preimage of `S` in the universal cover of `Sp_2g(R)`.
2. The finite residual of `E/F` contains a nontrivial central element. Hence
   `E/F`, `E` and `Q_{g,c}` are not residually finite.

Nowak (arXiv:2609.12196) proved that these groups have property (T) and are not
linear over any field. Non-linearity does not by itself exclude residual
finiteness. This node shows that residual finiteness fails too, through a
Deligne-type central extension.

**Consequences.**
- Every group containing `Q_{g,c}` is non-residually-finite. That excludes, as
  hosts, every residually finite group: linear groups, groups acting faithfully on
  locally finite rooted trees (`self-similar-hosts-contain-only-residually-finite-groups`),
  and automaton groups.
- The McKinsey–Mal'cev route to a solvable word problem is unavailable. The word
  problem is recorded as open in `torelli-lower-central-quotients-satisfy-boone-higman`.
- **The mechanism.** Hain's rational central line (weight −2, in
  `t_g[2] \ t_g[3]`) is killed in the relative completion. In the discrete group
  it shows up as a central `Z` whose extension class restricts, on a virtual
  section over `Sp_2g(Z)`, to a nonzero rational multiple of the class of the
  universal cover of `Sp_2g(R)`. This matches Nowak's remark (l.2498–2500) that
  "property (T) and superrigidity force the representation to kill Hain's central
  subgroup".

**Trust surface.**
- Borel's stable range must cover degree 2 for `Sp_2g` at the given `g`. It is
  quoted for `g >= 3` (range `k <= g-1`) and not read at source. If the true
  range is smaller, the statement holds for those `g` inside it.
- A remark in the proof gives a Borel-free alternative (Deligne's
  continuous-cohomology argument), but it is not written out in full.
