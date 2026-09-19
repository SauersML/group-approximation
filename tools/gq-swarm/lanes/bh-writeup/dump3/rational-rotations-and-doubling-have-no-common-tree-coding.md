---
rg: 2
id: rational-rotations-and-doubling-have-no-common-tree-coding
kind: claim
title: No tree coding of the rationally Cantorized circle makes all rational rotations and the d-fold covering almost-automorphisms, so register copies of Q admit no bounded natural dilation
distinct_from:
  rationals-embed-in-brin-thompson-group-2v: that builds a register copy of Q in 2V from rotations of a mixed-radix register; this shows that no coding of such a register makes a dilation acting naturally on it bounded.
  twisted-bt-point-fixing-actor-elements-are-divisible: that gives register roots of any coordinate-ignoring element; this shows those register copies of Q cannot be normalized as x -> d x by an element that acts on the register through the covering map.
  affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q: that excludes the 2-adic (translation on Z_2) model of Q x| <2> in finitely generated affine 2V_H hosts; this excludes the real-place (register) model in every host whose local maps on the register coordinate are prefix replacements.
  rational-stepping-stones-in-nv-need-bs12-or-heisenberg: that says any nV host of Aff(Q) must contain BS(1,2); this kills one natural construction shape for Q x| <2>, whether or not BS(1,2) embeds in nV.
artifacts:
  - research/artifacts/gq-bh-bh-free-16-rational-bs12-register.md
---

**ESTABLISHED** by `rational-rotations-doubling-no-common-tree-coding-proof` (lane proof,
elementary, not reviewed; no priority claimed). It proves in coding-free form the heuristic
"registers versus dilations" obstruction of `research/artifacts/gq-bt-kojima-mechanism.md` §4.2.

**Setting.** `D` is the circle `R/Z` Cantorized at `S = Q/Z`: each `s ∈ S` is replaced by two
points `s^-, s^+`, with the order topology. `D` is a Cantor space. It carries
- the rotations `R_q(x) = x + q` for `q ∈ Q/Z`, which are homeomorphisms;
- for an integer `d >= 2`, the pieces `D_i` (`0 <= i < d`) over the arcs `[i/d, (i+1)/d]`, and the
  covering branches `β_i : D_i → D`, `x ↦ d x mod 1`, which are homeomorphisms onto `D`.

A mixed-radix register in which every prime divides some radix (Kojima–Sheng use radices
`2, 3, 4, …`; see `rationals-embed-in-brin-thompson-group-2v` and
`twisted-bt-point-fixing-actor-elements-are-divisible`) is this space `D`, in the digit coding, with
`Q/Z` acting by `R_q`: every rational has a finite expansion, so the split points are all of `S`.

**Coding.** A *tree coding* is a rooted locally finite tree `T` without leaves, with a homeomorphism
`φ : ∂T → D`. A homeomorphism between clopen subsets of `D` is *`T`-almost-automorphic* if there is
a finite partition of its domain into vertex sets `φ(∂T_v)` on each of which it is induced by an
isomorphism of rooted subtrees `T_v ≅ T_w`. For the binary tree these are exactly the pieces of
elements of Thompson's `V`.

**Theorem.** Let `T` be a tree coding of `D`, and suppose the covering branches `β_0, …, β_(d-1)`
are `T`-almost-automorphic. Then there is an integer `M >= 1` coprime to `d` such that every
rotation `R_q` that is `T`-almost-automorphic has `q ∈ (1/M) Z[1/d] / Z`. In particular, `R_(1/p)`
is not `T`-almost-automorphic for every prime `p` not dividing `dM`.

**Calibration.**
- Thompson `T` in the dyadic coding (`d = 2`, `M = 1`): the doubling branches are prefix
  deletions, and the only rotations that are almost-automorphic are the dyadic ones.
- The Kojima–Sheng register (radices `2, 3, 4, …`): every `R_q` is almost-automorphic, so by the
  theorem no covering map `β` for any `d` is.

**Consequence for hosts.** Let `H` be a group of homeomorphisms of a product of Cantor spaces in
which every element acts, on each piece of a finite box partition, by a prefix replacement in a
fixed coordinate `k`. Examples: Brin–Thompson `nV`; the KEP hosts `2V_τ` and `2V_H` on their free
colour (`odometer-2v-is-fp-simple-and-contains-bs12`, `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`);
any twisted Brin–Thompson group `SV_G` and any coordinate `k` (a skew product over coordinate `k`
is locally induced by elements of `V ≀_S G` whose `G`-part fixes `k`). Fix any
identification of coordinate `k` with `D`. Then `H` contains no family of elements such that
- for infinitely many primes `p`, some element acts as a skew product over coordinate `k` with base
  map `R_(1/p)`; and
- some element acts as a skew product over coordinate `k` whose base map is, on each `D_i`, a rotation
  composed with `β_i` (by the Scope note below, the base map of a dilation is automatically
  of this form).
So a copy of `Q x| <d>` built from a register copy of `Q` on one coordinate, with the dilation
acting on the register through the covering map, does not exist in any of these hosts. This is the
design recorded in `research/artifacts/gq-bh-bh-free-16-rational-bs12-register.md`, and in
`gq-bt-kojima-mechanism.md` §3–§4.

**Scope.**
- The consequence assumes the dilation acts as a skew product over the register coordinate. An
  element with `δ R_q δ^-1 = R_(dq)` that mixes the register with other coordinates is not covered.
  For skew products, the base map of such a `δ` is forced to be a rotation composed with the covering
  map, because it intertwines `R_q` with `R_(dq)` on a dense orbit.
- Exotic actions of `Q` (as in Belk–Hyde–Matucci's `Q <= T̄`), and hosts whose local maps on the
  register coordinate are not almost-automorphisms (automaton or odometer germs), are not covered.
- It says nothing about whether `BS(1,2)`, `Q x| <2>` or `Aff(Q)` embed in `nV`.
