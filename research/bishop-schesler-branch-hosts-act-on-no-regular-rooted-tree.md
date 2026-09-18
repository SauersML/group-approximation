---
rg: 2
id: bishop-schesler-branch-hosts-act-on-no-regular-rooted-tree
kind: claim
title: For infinite G the Bishop–Schesler branch group Γ contains Alt(|G/N_n|+5) for every n, hence every finite group, so it acts faithfully on no regular rooted tree and lies in no self-similar or automaton group on a regular tree
requires:
  - efrf-groups-frattini-embed-in-efrf-branch-groups
distinct_from:
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that asks whether some finitely presented residually finite INPUT acts on no regular tree (open); this is about the branch HOST Γ built from any infinite input, and is unconditional.
  computable-tree-involution-escapes-local-self-similar-hulls: that shows one computable involution of T_2 escapes every fixed computable re-encoding into a finitely generated self-similar group; this shows the whole branch host has no faithful regular-tree action at all, under any encoding.
  decidable-fp-groups-need-not-embed-in-rational-group: that excludes finite-state (rational) hosts through word-problem complexity; this excludes every group of automorphisms of a regular rooted tree, finite-state or not, through finite subgroups.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

**Setting.** `G` is infinite and finitely generated, `(N_n)` is a residual chain of finite-index
normal subgroups, `Q_n = G/N_n`, `X_n = Q_n ∪ {x_n, y_n, z_n, p_n, q_n}`, and
`Γ = Γ_0 = ⟨H̃^[0], B_0⟩ ≤ Aut(T_X)` is the branch group of Bishop–Schesler
(arXiv:2509.12161v2 §3, read at source on MSI), with `B_ℓ = Alt(X_(ℓ+1))` rooted at the root of
`T_X^[ℓ]`.

**Theorem.**
1. `Γ` contains a subgroup isomorphic to `Alt(X_n)` for every `n ≥ 1`. Since `|X_n| = |Q_n| + 5`
   is unbounded, `Γ` contains every finite group.
2. `Γ` embeds in `Aut(T_d)` for no `d ≥ 2`. So no re-encoding of the growing-alphabet tree,
   finite-state counter or not, turns `Γ` into a group of automorphisms of a regular rooted tree.
   In particular `Γ` lies in no self-similar group, no automaton group and no functionally
   recursive group acting on a regular tree.
3. `Γ` is not residually `W_d` for any `d`, where `W_d` ranges over the finite iterated wreath
   products of `S_d`. It is not linear over any field.

**Proof.**
1. Bishop–Schesler Lemma `lem:branch-group-arg` gives `Γ_ℓ ≅ Γ_(ℓ+1) ≀_(X_(ℓ+1)) B_ℓ`, and its
   proof shows `a·Γ_(ℓ+1) ≤ Γ_ℓ` for every first-level vertex `a`. Iterating, `Γ_0` contains a copy
   of `Γ_ℓ` rooted at a level-`ℓ` vertex, and `Γ_ℓ ⊇ B_ℓ ≅ Alt(X_(ℓ+1))`. Every finite `F`
   embeds in `Alt(|F| + 2)`, and `Alt(m) ≤ Alt(m')` for `m ≤ m'`.
2. A finite subgroup `F ≤ Aut(T_d)` acts faithfully on the vertices of some finite level `k`, so
   `F ≤ W_k(S_d)`. Every composition factor of `W_k(S_d)` is a composition factor of `S_d`, and so
   has order at most `d!`. `Alt(m)` is simple of order `m!/2 > d!` once `m > d` and `m ≥ 5`. So
   `Alt(m) ⊄ Aut(T_d)` for large `m`, contradicting item 1.
3. A residually `W_d` group has all finite subgroups inside finite quotients with composition
   factors of order at most `d!`, which is excluded by item 1. Finitely generated linear groups
   contain `Alt(m)` for only boundedly many `m` (Jordan in characteristic 0; bounded dimension
   over `\bar F_p`). This is classical and was not rechecked.

**Consequence for the branch route.** The branch host of any infinite input already has no
regular-tree action. So the Bishop–Schesler reduction and the self-similar route
`fp-rf-boone-higman-via-fp-self-similar-overgroups` never share a host. Any host of `Γ` must be a
Cantor group that is not a tree-automorphism group, e.g. a Thompson-like group, which contains all
finite groups. The next node, `branch-host-v-recodings-need-recurrent-residual-chains`, puts `Γ`
into such a host and shows what finite presentation then needs.

**Lesson for general BH.** Growing alphabets are free in Thompson-like hosts and fatal in tree
hosts. Every finite group lives in `V`, but only boundedly many alternating groups live in
`Aut(T_d)`. A branch host with unbounded level alphabets therefore forces the host out of the
regular-tree world, where "self-similar" can no longer mean a wreath recursion on one tree. What
has to survive is a finite rule transporting depth `n` to depth `n + 1` in the recoded Cantor
action; see the next node.
