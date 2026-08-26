---
rg: 2
id: centralizing-hnn-sofic-via-regular-edge-centralizer
kind: claim
title: A centralizing HNN extension of a residually finite base is sofic if random edge-centralizer letters separate Britton-reduced words
distinct_from:
  sofic-safe-finite-presentation-compiler: that asks for the whole compiler; this isolates the single group-theoretic step it needs, and supplies the construction of the stable letter, leaving one probabilistic separation lemma.
  centralizing-hnn-over-conjugate-basis-is-always-sofic: that proves soficity for the conjugate-basis family through a right-angled Artin kernel, a mechanism unavailable for Mikhailova-type edges; this is the general strategy for an arbitrary edge subgroup of a residually finite base.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that decides residual finiteness; this concerns soficity, which the compiler needs precisely because residual finiteness fails.
---

OPEN, with the construction supplied and one lemma isolated.

**Setting.**  Let `K` be residually finite with finite quotients
`q_n : K -> Q_n` separating a given finite set, let `L <= K` be any
subgroup, and let

```text
Gamma = < K, v | [v, L] = 1 > = K *_L (L x Z).
```

Write `L_n = q_n(L) <= Q_n` and let `pi_n : K -> Sym(Q_n)` be the left
translation action.

**What is proved here.**

1. `pi_n` restricted to `L` is *free*: left translations of a group by a
   subgroup have trivial point stabilizers.  Its orbits are the right
   cosets `L_n g`, and there are `[Q_n : L_n]` of them, a number that
   tends to infinity exactly when `L` has infinite index in `K` and the
   quotients are chosen accordingly.
2. Consequently the centralizer of `pi_n(L)` in `Sym(Q_n)` is the full
   `L`-equivariant bijection group of a free `L_n`-set, i.e.

```text
C_n := C_{Sym(Q_n)}(pi_n(L)) ~= L_n wr Sym(O_n),   O_n = L_n \ Q_n,   (CE1)
```

   acting by choosing a permutation of the orbits and an element of `L_n`
   per orbit.  In particular any `sigma_v in C_n` satisfies the defining
   relation `[sigma_v, pi_n(L)] = 1` **exactly**, not approximately.
3. Therefore `(pi_n, sigma_v)` is an exact finite model of the
   presentation of `Gamma` for every choice of `sigma_v in C_n`; the only
   thing to check is that it separates: Britton-reduced words must be far
   from the identity in normalized Hamming distance.

**The remaining lemma.**  Choose `sigma_v` uniformly at random from
`C_n` (uniform orbit permutation, uniform `L_n`-labels).  For every
Britton-reduced word

```text
w = k_0 v^{e_1} k_1 ... v^{e_m} k_m,   k_i notin L at the pinches,
```

show that with probability tending to one the permutation
`pi_n(k_0) sigma_v^{e_1} ... sigma_v^{e_m} pi_n(k_m)` moves at least a
fixed fraction of `Q_n`.  This is the sofic analogue of Ueda's reduced
normal form, and it is the only missing step: everything else in the
construction is exact.

**Why the obvious obstruction does not apply.**  The recorded no-go for
random sofic approximations (a Haar-random model of `L` has trivial
centralizer) concerns approximations chosen at random *for `L`*; here the
model of `L` is the restriction of a left-translation model of `K`, whose
`L`-part is free by 1, so the centralizer (CE1) is as large as possible.
The randomness is moved from the model to the stable letter.

**Consequence if the lemma holds.**  `Gamma_e` of the MF-safe compiler is
sofic (its `K_e` is a finite direct product of free groups, hence
residually finite, and `L_e` has infinite index), which is the first of the
two steps of [[sofic-safe-finite-presentation-compiler]]; the second is the
final rope edge, where the permutation Fell absorption recorded there
already makes the two edge embeddings exactly conjugate.

## Attempts

*Amplification (dies).*  Taking `sigma_v` to be a permutation of an
auxiliary factor, i.e. replacing the model by `Q_n x [k]` and letting
`sigma_v` act on `[k]`, satisfies the relation exactly but also commutes
with all of `pi_n(K)`, so every pinch `[v, k]` with `k notin L` maps to
the identity and the model is not separating.  This is why the stable
letter must be chosen inside the *edge* centralizer (CE1) and not inside
the centralizer of the whole base.

*Random model of the edge (dies).*  If the finite model of `L` is chosen
at random rather than as the restriction of a base model, its centralizer
is trivial with high probability and no stable letter exists at all; this
is the recorded no-go, and clause 1 above is exactly what avoids it.

*Where the remaining lemma is delicate.*  A random `sigma_v in C_n` moves
whole `L_n`-cosets, so a pinch `sigma_v pi_n(k) sigma_v^{-1} pi_n(k)^{-1}`
compares the `K`-action with its conjugate by a random coset permutation.
The comparison is favourable when `[Q_n : L_n]` grows, but the labels in
`L_n wr Sym(O_n)` interact with the `K`-action along the cosets, so the
estimate is not the standard random-permutation independence argument and
has not been carried out here.
