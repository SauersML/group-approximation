---
rg: 2
id: centralizing-hnn-sofic-via-regular-edge-centralizer
kind: claim
title: Quotient models cannot make a centralizing HNN extension sofic, and the exact edge centralizer they do supply
distinct_from:
  sofic-safe-finite-presentation-compiler: that asks for the whole compiler; this isolates the single group-theoretic step it needs, and supplies the construction of the stable letter, leaving one probabilistic separation lemma.
  centralizing-hnn-over-conjugate-basis-is-always-sofic: that proves soficity for the conjugate-basis family through a right-angled Artin kernel, a mechanism unavailable for Mikhailova-type edges; this is the general strategy for an arbitrary edge subgroup of a residually finite base.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that decides residual finiteness; this concerns soficity, which the compiler needs precisely because residual finiteness fails.
---

ESTABLISHED as a no-go, with the surviving construction recorded.

**Headline.**  For a centralizing HNN extension `Gamma = <K, v | [v, L] = 1>`
whose edge `L` is not closed in the profinite topology of `K`, *no* finite
model in which `K` acts through a finite quotient can separate the pinch
words, however the stable letter is chosen.  Since the compiler's edge is
deliberately non-closed (that is how it encodes the recursive kernel), the
soficity question there cannot be answered by quotient models, and this
rules out the most natural attack.

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

**The no-go.**  Let `k` lie in the profinite closure of `L` in `K` but not
in `L` (such `k` exist exactly when `L` is not closed, which is the case
for the compiler's Mikhailova-type edge and for every family that encodes
a non-recursive kernel).  Then `q_n(k) in L_n` for every finite quotient
`q_n` in which `L_n` contains the image of `L`, because the closure is the
intersection of the preimages of the images of `L`.  Any `sigma_v` in the
centralizer (CE1) commutes with `pi_n(L_n)` and therefore with `pi_n(k)`,
so the Britton-reduced, hence nontrivial, pinch `[v, k]` maps to the
identity: the model is not separating, at *every* scale and for *every*
choice of stable letter.  This is the exact finite-model shadow of
[[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]].

**What survives.**  Clauses 1--3 remain true and say something usable: an
approximate model of `K` in which `L` acts freely has a full wreath
centralizer, so a stable letter satisfying the relation *exactly* always
exists once the edge action is free.  A successful sofic construction must
therefore use approximations of `K` that do **not** factor through finite
quotients --- they must keep `L` acting freely while separating the
closure points `cl(L) \ L` --- and only then choose the stable letter in
the centralizer.  Both requirements are simultaneously satisfiable only by
genuinely approximate (perturbed) models, which is precisely the content
of the open lemma below.

**The remaining lemma (restated).**  Choose `sigma_v` uniformly at random from
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

*Quotient models (dies, proved above).*  Any model factoring through a
finite quotient of `K` kills the pinches at closure points of `L`.  The
approximation must be perturbed away from a quotient model.

*Where the remaining lemma is delicate.*  A random `sigma_v in C_n` moves
whole `L_n`-cosets, so a pinch `sigma_v pi_n(k) sigma_v^{-1} pi_n(k)^{-1}`
compares the `K`-action with its conjugate by a random coset permutation.
The comparison is favourable when `[Q_n : L_n]` grows, but the labels in
`L_n wr Sym(O_n)` interact with the `K`-action along the cosets, so the
estimate is not the standard random-permutation independence argument and
has not been carried out here.

## The finitely generated case: the route is equivalent to separability

Suppose the edge `L` is finitely generated, as it is for the compiler
(the Mikhailova subgroup `M_e` is generated by the finitely many elements
`(x, x)` and `(r, 1)`).  Then the quotient-model route is *equivalent* to
separability of `L` in `K`, and therefore dies for a Mikhailova edge.

1. **Sufficiency, pinch case.**  Let `q : K -> Q` be a finite quotient,
   `H = q(L)`, and let `K` act on `Q` by left translation.  The action of
   `H` is free, so by (CE1) the centralizer of `pi(H)` is `H wr Sym(H\Q)`,
   and the double centralizer of a free action is the group of left
   translations by `H` itself.  Hence for `g in Q`,

```text
   g centralizes the whole edge centralizer   iff   g in H.
```

   So a stable letter `sigma_v` in the centralizer with
   `[sigma_v, pi(g)] != 1` exists **iff** `q(k) notin q(L)`.

2. **Necessity.**  If `q(k) in q(L)` then every element of the centralizer
   commutes with `pi(q(k))`, and the pinch dies, as in the no-go above.

3. **The finitely generated edge collapses the two conditions.**  Taking
   balls large enough to contain a generating set of `L`, the subgroup
   generated by the ball's edge elements is all of `L`, so the requirement
   in 1 becomes: for every `k in K \ L` some finite quotient has
   `q(k) notin q(L)` --- exactly separability of `L` in the profinite
   topology of `K`.

4. **Mikhailova edges are not separable.**  For a finitely presented `H`
   with unsolvable word problem, `M = {(u, v) in F x F : u = v in H}` is
   finitely generated, and membership in `M` is undecidable (Mikhailova).
   A separable finitely generated subgroup of a finitely presented group
   has decidable membership: non-membership is certified by a finite
   quotient and membership is recursively enumerable, so both sides are
   r.e.  Hence `M` is not separable, and by 2 and 3 the quotient-model
   route cannot work for the compiler's rope.

**Consequence.**  Any proof that the compiler's rope is sofic --- or even
LEF --- must use finite models whose restriction to `K_e` is *not* a
homomorphism onto a finite quotient: local models are only required to be
multiplicative on a ball, and that extra freedom is exactly what the
argument above shows to be necessary.
