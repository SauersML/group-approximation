---
rg: 2
id: simple-nonsofic-width-over-towers-with-symmetric-levels
kind: claim
title: A finitely presented simple nonsofic group has bounded relator width over iterated wreath products mixing bounded-degree levels with full symmetric levels of any degree
distinct_from:
  simple-nonsofic-relator-width-over-iterated-wreath-products: that bounds the width over towers of bounded degree for every group without finite quotients; this allows levels Sym(n) of unbounded degree and uses nonsoficity for them.
  simple-nonsofic-width-over-bounded-base-symmetric-wreath: that is depth two with a bounded base; this allows any depth, with bases that are themselves mixed towers of unbounded size.
  transitive-wreath-towers-bounded-commutator-width: that bounds the commutator width of bounded-degree towers; this adds symmetric levels, where every even permutation is a single commutator.
---

**ESTABLISHED** through `simple-nonsofic-width-over-towers-with-symmetric-levels-proof`. Unreviewed.

Let `G = <X | R>` be an infinite finitely presented simple group that is not sofic, and `w_Q(a)` the
relator width.

**Theorem.** Fix `m`. Call a tower `W = T_1 wr ... wr T_d` *admissible* if every vertex group is either a
transitive group of degree `<= m` or a full symmetric group `Sym(n_i)` in its natural action, with `n_i`
arbitrary. There is `K = K(G, m)` such that `w_W(a) <= K` for every admissible tower, every depth, all
degrees `n_i`, and every `a in W^X`.

**Two lemmas proved along the way.**
1. **Even permutations are commutators (elementary).** Every even permutation is a product of two
   conjugate involutions, hence a commutator in `Sym(n)`.
2. **Commutator width of admissible towers.** Every element of `[W, W]` is a product of at most
   `3(m! + m + 2)` commutators, for every admissible tower.
   - *Bounded levels:* as in `transitive-wreath-towers-bounded-commutator-width`.
   - *Symmetric levels:* one move with an `n`-cycle, lemma 1 for the top, and three-for-two absorption.

**Consequence.** Weak models of `G`, with any bi-invariant lengths, cannot take values in such towers. This
covers unbounded bases under symmetric tops whenever the base is itself an admissible tower, for
example `C_2 wr Sym(n_1) wr C_3 wr Sym(n_2) wr ...` with arbitrary `n_i`.

**Mechanism.** The template argument of `relator-width-over-towers-of-bounded-commutator-width`, with two
changes at a symmetric level whose root tuple moves a set `Omega_0` of size `n' > N_1`:
- **The top.** An exponent block, then a balanced Rodgers block `r*^k r*^-k` covering `Alt(Omega_0)`. Here
  `r*` has root support `>= eps_0 n'` by Lemma 1.2 of `simple-group-support-and-semisimple-rank-models-collapse-proof`.
- **The base.** Dipoles along a Hamiltonian path of `Omega_0` in at most `2 ceil(2/eps_0)` rounds, placed by
  `Sym(Omega_0)`-conjugation, as in `simple-nonsofic-width-over-bounded-base-symmetric-wreath-proof`.

All conjugators fix `Omega \ Omega_0` pointwise, so the coordinates fixed by the root tuple are handled
recursively. Small moved sets are treated like bounded-degree levels.
