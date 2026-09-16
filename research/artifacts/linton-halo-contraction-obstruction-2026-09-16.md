# A contraction obstruction to set-halo presentations of Linton shells

Date: 2026-09-16.  Target hole: `linton-radical-has-equivariant-sofic-halo`.
Companion scripts: `experiments/linton-halo-contraction-obstruction-2026-09-16/`.

## 0. Summary

Section 1 fixes conventions.  The definitions of halos are quoted from the
verbatim audit in `research/artifacts/or-linton-halo-2026-09-12.md`.

- **Theorem 1** (Section 2) is a necessary condition for any set-theoretic halo
  presentation `E = L(X) semidirect F0`.  If `e` in `E` conjugates a finitely
  generated subgroup `H <= L(X)` into itself, then some positive power of `e`
  acts on `H` as an inner automorphism of `L(X)`.
  - It uses neither soficity of the pieces nor the intersection axiom.
  - It does not depend on which complement `F0` is chosen.
- **Lemma 3** (Section 3) is self-contained.  In a locally free group, a
  finitely generated subgroup cannot be conjugated properly into itself.
- **Corollary 4.**  If `R` is locally free, no element of a shell with a halo
  presentation contracts a finitely generated subgroup of `R`.
- **Proposition 5** (Section 4) is about `G0 = <a,s | s a s^-1 = [a, s^-1 a s]>`.
  - Its Linton radical is perfect, nontrivial and locally free.
  - The shell at the least valid stage (`n = 0`, `F0 = Z`) has no halo
    presentation, for any complement.
  - At every stage `n >= 1` the conclusion of the target holds.
- **Proposition 6** (Section 5) is a family.  Fix `d >= 0` and
  `u in F(p,q)^(d) \ F(p,q)^(d+1)`, and put
  `G_u = <a,p,q | u a u^-1 = [a, u^-1 a u]>`.
  - Every stage `n` is valid.
  - For `n <= d` the shell has no halo presentation.
  - For `n >= d+1` the conclusion of the target holds.
- **Section 6** gives the consequences.
  - The target is false if "the finite rational-derived shell" means the least
    valid stage, or every valid stage.
  - It is not refuted if the stage is existential.
  - Any proof must pick a stage deeper than every contraction.
  - All groups here are sofic, so this is an obstruction to one method, not
    evidence against soficity.

Convention: `[g,h] = g h g^-1 h^-1`, `c_g(x) = g x g^-1`.

## 1. Conventions

**Halos** (Alekseev--Bradford, arXiv:2601.18742v1, Definitions 2.1 and 2.4;
the audited quotations are in `or-linton-halo-2026-09-12.md`, lines 131--158).

A *halo of groups* over a set `X` is a family `L(Y)`, `Y <= X`, with:

- (i) `L(Z) <= L(Y)` for `Z <= Y`;
- (ii) `L(empty) = 1` and `L(X) = < L(Y) : Y finite >`;
- (iii) `L(Y cap Z) = L(Y) cap L(Z)`.

A *set-theoretic halo* is a covariant functor `L` from sets with injections to
groups with monomorphisms, such that for every `X` the images
`L(iota_Y)(L(Y))`, for the inclusions `iota_Y : Y -> X`, form a halo over `X`.
We identify `L(Y)` with its image in `L(X)`.

**Halo presentations.**  Let `E` be a group with a normal subgroup `R` and a
complement `F0`, so that `E = R semidirect_alpha F0` with
`alpha(f) = c_f|_R`.  A *halo presentation* of `(E, R, F0)` consists of:

- an `F0`-set `X`, i.e. a homomorphism `pi : F0 -> Sym(X)`;
- a set-theoretic halo `L`;
- an isomorphism `theta : L(X) -> R` with
  `theta o L(pi(f)) = alpha(f) o theta` for all `f` in `F0`.

The target claim asks for a halo presentation of the Linton shell with sofic
finite pieces.  No soficity is used in Sections 2--3.

**Shells.**  For a one-relator group `G` with Linton radical
`R = G_Q^(omega)`, a stage `n` is *valid* if `G_Q^(n)/R` is free.
[[one-relator-soficity-localizes-at-rational-derived-stage]] shows that some
`n <= |w|` is valid.  The quotient `G/R` is residually rationally solvable, and
its lemma gives `G_Q^(n)/R = (G/R)_Q^(n)`.  Subgroups of free groups are free,
so the valid stages form an up-set of the nonnegative integers.  At a valid
stage, `E_n = G_Q^(n) = R semidirect F0`, where `F0` is any lift of a free basis
of `E_n/R`.

## 2. Invariant conjugations are virtually inner

**Theorem 1.**  Let `(X, L, theta)` be a halo presentation of
`(E, R, F0)`.  Let `e` in `E` and let `H <= R` be finitely generated with
`e H e^-1 <= H`.  Then there are `N >= 1` and `rho'` in `R` with

    e^N h e^-N = rho' h rho'^-1   for all h in H.

*Proof.*

*Step 1: a finite support.*  Transport everything to `L(X)` through
`theta`.  Axiom (ii) and monotonicity make `L(X)` the directed union of the
`L(Y)` over finite `Y`.  Hence each of the finitely many generators of `H`
lies in some finite piece, and there is one finite `Y <= X` with
`H <= L(Y)`.

*Step 2: agreement on a piece.*  Let `sigma, tau` be bijections of `X` that
agree on `Y`.  Then `sigma o iota_Y = tau o iota_Y` as injections `Y -> X`.
By functoriality,

    L(sigma) o L(iota_Y) = L(sigma o iota_Y) = L(tau o iota_Y) = L(tau) o L(iota_Y) ,

so `L(sigma)` and `L(tau)` agree on `L(Y)`.

*Step 3: a finitary replacement.*  Write `e = rho f` with `rho` in `R` and
`f` in `F0`; this is possible for every `e` because `E = R F0`.  Put
`Y' = Y cup pi(f)(Y)`, a finite set.  The map `pi(f)|_Y : Y -> pi(f)(Y)` is a
bijection between finite subsets of `Y'` of equal size.  So it extends to a
permutation of `Y'`: map `Y' \ Y` bijectively onto `Y' \ pi(f)(Y)`.  Extend by
the identity outside `Y'`.  The result is a permutation `sigma` of `X` with
finite support, agreeing with `pi(f)` on `Y`.  Let `N` be its order, which is
finite.

*Step 4: compute in a larger semidirect product.*  Form
`P = L(X) semidirect Sym(X)`, with `Sym(X)` acting through `L`; `L(sigma)` is
an automorphism with inverse `L(sigma^-1)`.  Multiplication is
`(g1, s1)(g2, s2) = (g1 L(s1)(g2), s1 s2)`.

- Put `r = theta^-1(rho)` and `eps = (r, sigma)` in `P`.
- On `L(X)`, `c_eps = c_r o L(sigma)`.
- Transported to `L(X)`, `c_e|_R` is `c_r o L(pi(f))`.
- By Step 2 these agree on `L(Y)`, hence on `H`.

Both maps send `H` into `H`: `c_e` by hypothesis, so `c_eps` too.  By induction
on `k`, `c_e^k|_H = c_eps^k|_H` for all `k >= 0`: if
`c_e^k(h) = c_eps^k(h)` lies in `H`, apply the common restriction to `H` once
more.

*Step 5: the power.*  In `P`,

    eps^N = ( r L(sigma)(r) L(sigma^2)(r) ... L(sigma^(N-1))(r) , sigma^N ) = (r_sigma, 1)

with `r_sigma` in `L(X)`.  So `c_eps^N = c_(eps^N)` restricts to `c_(r_sigma)`
on `L(X)`.  Therefore `c_e^N|_H = c_(r_sigma)|_H`, and `rho' = theta(r_sigma)`
works.  ∎

**Remarks.**

1. Only three ingredients were used: functoriality on injections,
   monotonicity, and generation by finite pieces.  The intersection axiom
   (iii) and the soficity of the pieces were not used.  So the obstruction
   holds for every set-theoretic halo presentation, sofic or not.
2. Nothing depends on the choice of complement.  The hypothesis and the
   conclusion mention only `E`, `R`, `e` and `H`.
3. The argument needs finitary permutations of `X` in the domain category of
   `L`.  It does not apply to graph-theoretic halos, whose morphisms are
   inclusions of induced subgraphs.  This is consistent with Attempt 3 of the
   target, which names graph halos as a separate refinement.

**Corollary 2.**  Under the hypotheses of Theorem 1, for every finitely
generated `H <= R` the group

    N_E(H) / ( N_R(H) C_E(H) )

is a torsion group.

*Proof.*

- `N_R(H) = N_E(H) cap R` and `C_E(H)` are both normal in `N_E(H)`, so their
  product is a normal subgroup.
- Let `e` be in `N_E(H)`, and take `N` and `rho'` as in Theorem 1.  Then
  `c_(rho')(H) = c_(e^N)(H) = H`, so `rho'` is in `N_R(H)`.
- Also `rho'^-1 e^N` centralizes `H`.
- Hence `e^N = rho' (rho'^-1 e^N)` lies in `N_R(H) C_E(H)`.  ∎

## 3. Locally free radicals

**Lemma 3.**  Let `R` be a locally free group, `H <= R` finitely generated and
`rho` in `R` with `rho H rho^-1 <= H`.  Then `rho H rho^-1 = H`.

*Proof.*  We may assume `H != 1`.  Suppose, for a contradiction, that
`rho H rho^-1 < H` is strict.  Put `psi = c_rho|_H : H -> H`.  This is an
injective endomorphism which is not surjective.

*(a) The chain is strict and `rho` has no power in `H`.*

- By induction, `rho^j H rho^-j <= rho H rho^-1 < H` for every `j >= 1`.
- If `rho^j` lay in `H` for some `j >= 1`, then `rho^j H rho^-j = H`, a
  contradiction.
- If `rho^-j` lay in `H`, then so would `rho^j`.
- So `rho^j` is not in `H` for all `j != 0`.

*(b) `D = <H, rho>` is the ascending HNN extension.*  Let
`M = < H, t | t h t^-1 = psi(h) (h in H) >`, and let `Phi : M -> D` be the
identity on `H` with `t -> rho`.  It is well defined and onto.

- Using `t h = psi(h) t` and `h t^-1 = t^-1 psi(h)`, every element of `M` has
  the form `t^-m h t^k` with `m, k >= 0` and `h` in `H`.
- Suppose `Phi(t^-m h t^k) = rho^-m h rho^k = 1`.  Then `h = rho^(m-k)`.
- By (a), `m = k` and `h = 1`, so the element was trivial.

Hence `Phi` is an isomorphism.

*(c) Homology.*  `D` is a finitely generated subgroup of `R`, hence free of
finite rank `d >= 1`.  Put `r = rank(H)`.  The Mayer--Vietoris sequence of the
HNN extension `M` in rational homology reads

    0 -> H_2(M) -> H_1(H) --(psi_* - 1)--> H_1(H) -> H_1(M) -> H_0(H) --0--> H_0(H) -> H_0(M) -> 0 .

It uses `H_i(H; Q) = 0` for `i >= 2`, since `H` is free.  It gives
`dim H_2(M;Q) = dim ker(psi_* - 1)` and
`dim H_1(M;Q) = r - rank(psi_* - 1) + 1`.

- `M = D` is free, so `H_2(M;Q) = 0`.  Hence `psi_* - 1` is injective on
  `Q^r`, so it has rank `r`.
- Then `dim H_1(M;Q) = 1`, so `d = 1` and `D` is infinite cyclic.
- So `D` is abelian and `rho H rho^-1 = H`, a contradiction.  ∎

**Corollary 4.**  Let `(X, L, theta)` be a halo presentation of `(E, R, F0)`
with `R` locally free.  Let `H <= R` be finitely generated and `e` in `E` with
`e H e^-1 <= H`.  Then `e H e^-1 = H`.

*Proof.*  Take `N >= 1` and `rho'` from Theorem 1.  Then

    rho' H rho'^-1 = e^N H e^-N <= e H e^-1 <= H .

By Lemma 3 the outer terms are equal, so `e H e^-1 = H`.  ∎

**Remark (finite outer action).**  Let `R` be locally free and `H <= R`
finitely generated noncyclic.  Two classical facts are used below; their
bibliographic details were not re-fetched in this session and are recorded
as unverified.

- In a free group, a nontrivial finitely generated normal subgroup has finite
  index, and Schreier's formula `rank(H) - 1 = [K:H](rank(K) - 1)` holds.
  Hence every finitely generated `K` with `H <= K <= N_R(H)` has
  `[K:H] <= rank(H) - 1`.  So `N_R(H)` is a finite extension of `H`.
- `Out(F_r)` is virtually torsion-free, so its torsion subgroups are finite.

Corollary 2 then shows that `N_E(H)` acts on `H` through a *finite* subgroup of
`Out(H)`.  This remark is not used below.

## 4. The stage-zero example `G0`

Let

    G0 = < a, s | s a s^-1 = [a, s^-1 a s] > .

Reduced, the relator is `w = s a s^-2 a s a s^-1 a^-1 s a^-1`.  It is
cyclically reduced of length 11, with exponent sums `0` in `s` and `1` in `a`
(checked by `check_words.py`).  Put `a_i = s^i a s^-i`.  Conjugating the
relation by `s^i` gives

    a_(i+1) = [a_i, a_(i-1)]   for all i in Z .                      (4.1)

**Proposition 5.**

1. **Ascending HNN form.**  Let `B = F(x,y)` and `phi(x) = y`,
   `phi(y) = [y,x]`.  Then `G0` is the ascending HNN extension `B *_phi`, with
   `x = a_(-1)`, `y = a_0` and stable letter `s`.  The endomorphism `phi` is
   injective but not surjective.
2. **The kernel.**  Let `R = ker(G0 -> Z)`, where `s -> 1` and `a -> 0`.
   - `R` is the normal closure of `a`.
   - `R` is the directed union of the free groups `B_k = s^-k B s^k`, each
     equal to `F(a_(-k-1), a_(-k))`.
   - So `R` is nontrivial and locally free.
   - Also `c_s(B) = phi(B) < B`.
3. **Perfect radical.**  `R` is perfect, and `R` is the Linton radical of
   `G0`.
4. **Stages.**
   - At stage 0, `E_0 = G0 = R semidirect <s>` with `F0 = Z`.
   - At every stage `n >= 1`, `E_n = R` and `F0 = 1`.
   - All stages are valid, and the least valid stage is `0`.
5. **No halo at stage 0.**  For no complement of `R` in `G0` does
   `(G0, R, F0)` admit a halo presentation, with or without sofic pieces.
6. **Halo at stages `n >= 1`.**  The conclusion of the target holds.
7. **Soficity.**  `G0` is residually finite, hence sofic.

*Proof.*

(1) *HNN form.*  The HNN extension
`< x, y, s | s x s^-1 = y, s y s^-1 = [y,x] >` becomes the presentation of
`G0` after eliminating `y = s x s^-1` and writing `a = y`, `x = s^-1 a s`.
The script checks this identity letter by letter.

*`phi` is injective.*

- `phi(B) = < y, [y,x] >`.
- Since `[y,x]^-1 y = x y x^-1`, this equals `< y, x y x^-1 >`.
- The set `{y, x y x^-1}` is Nielsen reduced (checked exhaustively by the
  script), so it is a free basis of a rank-2 subgroup.
- Thus `phi` maps `F2` onto a free group of rank 2.  Free groups of finite
  rank are Hopfian, so `phi` is injective.

*`phi` is not surjective.*  `phi(B)` lies in the normal closure of `y`, and `x`
does not.

(2) *The kernel.*

- Every element of `G0` is `rho s^i` with `rho` in the subgroup generated by
  the `a_j`.  That subgroup is normal, since it is invariant under `s^(+-1)`.
  So `R = <<a>> = < a_j : j in Z >`.
- `s B s^-1 = phi(B) <= B`, so `B <= s^-1 B s`, i.e. `B_k <= B_(k+1)`.
- For `i <= 0`, `a_i` lies in `B_(-i)`.  For `i >= 1`, `a_i` lies in
  `s^i B s^-i <= B`.
- So the union of the `B_k` is a subgroup of `R` containing all generators,
  hence equals `R`.
- The base group `B` embeds in the HNN extension, so `R != 1`.
- Every finitely generated subgroup of `R` lies in some `B_k`, which is free of
  rank 2.

(3) *Perfect radical.*  By (4.1), every generator `a_(i+1)` of `R` is a
commutator of elements of `R`, so `R = [R,R]`.

- `G0^ab = Z` is generated by `s` (the relator abelianizes to `a = 0`), so
  `G0_Q^(1) = ker(G0 -> Q) = R`.
- `R` is perfect, so `R_Q^(1) = R`.
- Hence `G0_Q^(n) = R` for all `n >= 1`, and `G0_Q^(omega) = R`.

(4) *Stages.*  `G0/R = Z` and `(G0/R)_Q^(n) = 1` for `n >= 1`.  Both are free,
so all stages are valid.

(5) *No halo at stage 0.*

- Complements of `R` in `G0` are the groups `< rho s >` with `rho` in `R`.  A
  halo presentation for any of them gives, by Corollary 4 with `e = s` and
  `H = B`, `s B s^-1 = B`.
- But `s B s^-1 = phi(B) < B` by (1).
- `R` is locally free by (2), so Corollary 4 applies.  This is a
  contradiction.

A direct check, without Lemma 3, is also available.  Theorem 1 gives `rho'` in
`R` with `rho' B rho'^-1 = phi^N(B)`.

- By Step (b) of Lemma 3, `D = < B, rho' >` is isomorphic to `B *_(phi^N)`.
- `phi` abelianizes to the nilpotent map `x -> y -> 0`.  So the relation matrix
  of `B *_(phi^N)` has invertible `2 x 2` block, and `H_1(D; Z) = Z`.  The script
  computes this for `N = 1..6`; the case `N >= 2` is the zero map.
- A free group with abelianization `Z` is infinite cyclic, but `D` contains
  `B = F2`.  Contradiction.

(6) *Halo at stages `n >= 1`.*

- `F0 = 1`, `X` is a point, `L(Y) = *_Y R` and `theta` is the identity.
- The finite pieces are finite free powers of `R`.
- `R` is locally free, hence sofic, since soficity is local.
- Finite free products of sofic groups are sofic.

This is part 4 of [[permuted-free-product-linton-radical-gives-sofic-shell]].

(7) *Soficity.*  Borisov--Sapir (arXiv:math/0309121, Invent. Math., DOI
10.1007/s00222-004-0411-2) prove that every mapping torus of a free group
endomorphism is residually finite.  `G0` is the mapping torus of `phi`.  ∎

So the halo conclusion fails at the least valid stage for a group that is
sofic, and even residually finite.  Soficity of a shell `E_n` does not imply a
halo presentation of `E_n`.

## 5. A family failing exactly at the stages `n <= d`

Let `F = F(p,q)`.  For free groups the rational derived series is the derived
series: each `F^(i)/F^(i+1) = H_1(F^(i); Z)` is free abelian.

Fix `d >= 0`.  For `d >= 1`, `F^(d)` is a nonabelian free group, so
`F^(d+1) != F^(d)`; also `F^(0) != F^(1)`.  Pick any `u` in `F^(d) \ F^(d+1)`.

- `d = 0`: `u = p`.
- `d = 1`: `u = [p,q]`.  The script checks that the Fox derivatives of `u^k`
  do not vanish in `Z[Z^2]`, so `u^k` is not in `F''`.  This is not needed
  below; it only calibrates the torsion-freeness argument.

Put

    G_u = < a, p, q | u a u^-1 = [a, u^-1 a u] >  =  G0 *_(s = u) F .

This is an amalgam over infinite cyclic groups, as `s` and `u` both have
infinite order.  Substituting `s = u` into the relator of `G0` gives the
displayed one-relator presentation.

**Proposition 6.**

1. `R = <<a>>` is the Linton radical of `G_u` and `G_u/R = F`.  Every stage `n`
   is valid, and `E_n = G_Q^(n) = R semidirect F^(n)`.
2. With `C = <u>` and `R0 = ker(G0 -> Z)` from Proposition 5,

       R = *_( gC in F/C ) g R0 g^-1 .

   This is an internal free product permuted by `F` by left multiplication on
   `F/C`.  In particular `R` is perfect and locally free.
3. For `n <= d`, the shell `E_n` admits no halo presentation, for any
   complement of `R` in `E_n`.
4. For `n >= d+1`, the shell `E_n`, with complement `F^(n) <= F`, admits a halo
   presentation with sofic finite pieces.  So the conclusion of the target
   holds at these stages.
5. `G_u` is sofic.

*Proof.*

(2) *The free product.*  Let `psi : G_u -> F` be the identity on `F`, send
`R0` to `1` and send `s` to `u`.  It is well defined on the amalgam, and its
kernel `K` contains `<<a>>`.  Since `G_u / <<a>> = < p, q | > = F`, we get
`K = <<a>>`.  Let `K` act on the Bass--Serre tree `T` of the amalgam.

- *Edge stabilizers* are conjugates of `C`.  `psi` is injective on `C`, so
  `K` meets them trivially.
- *Vertex stabilizers:* `K cap g G0 g^-1 = g R0 g^-1`, because
  `K cap G0 = ker(G0 -> C) = R0`.  Also `K cap g F g^-1 = 1`.
- *The quotient graph* `K \ T` is a star.  Since `K` is normal and
  `G_u / K = F`:
  - the `G0`-type vertices are indexed by `K\G_u/G0 = F/C`;
  - there is one `F`-type vertex, since `K\G_u/F = F/F`;
  - the edges are indexed by `K\G_u/C = F/C`;
  - each `G0`-vertex `gC` is joined to the centre by the single edge `gC`.

A graph of groups on a tree with trivial edge groups gives the free product of
its vertex groups.  Lifting the star by coset representatives `g` of `F/C`
gives the displayed decomposition.

- `g R0 g^-1` depends only on `gC`, since `u = s` normalizes `R0`.
- For `f` in `F`, `f (g R0 g^-1) f^-1 = (fg) R0 (fg)^-1`, which is the
  permutation action.

A free product of perfect groups is perfect.  A finitely generated subgroup of
a free product lies in a finite free product of finitely generated subgroups of
the factors, hence in a free product of free groups, which is free.  So `R` is
locally free.

(1) *Radical and stages.*

- `G_u/R = F` has trivial rational derived intersection, since free groups are
  residually torsion-free nilpotent.  So `G_Q^(omega) <= R`.
- A perfect normal subgroup lies in every `G_Q^(i)`, by induction: if `R` lies
  in `G_Q^(i)`, it dies in `H_1(G_Q^(i); Q)` because it is perfect.  So
  `R <= G_Q^(omega)`, and `R` is the Linton radical.
- By the lemma of [[one-relator-soficity-localizes-at-rational-derived-stage]],
  `G_Q^(n)/R = F_Q^(n) = F^(n)`, which is free.  So every `n` is valid.
- `F <= G_u` is a complement of `R`, so `F^(n)` is a complement of `R` in
  `E_n`.

(3) *No halo for `n <= d`.*

- `u` lies in `F^(d) <= F^(n) <= E_n`.
- In the amalgam `u = s`, and `B = F(a_(-1), a_0) <= R0 <= R` satisfies
  `u B u^-1 = phi(B) < B` by Proposition 5(1).
- `R` is locally free, so Corollary 4 forbids a halo presentation, whatever
  the complement.

(4) *Halo for `n >= d+1`.*  `F^(n)` acts on `X = F/C` by left multiplication.

- *Stabilizers:* the stabilizer of `gC` is
  `F^(n) cap g C g^-1 = g (F^(n) cap C) g^-1`, since `F^(n)` is normal in `F`.
- *They are trivial:* if `u^k` lay in `F^(n) <= F^(d+1)` for some `k != 0`,
  then `u` would lie in `F^(d+1)`, because `F^(d)/F^(d+1)` is torsion-free.
  That contradicts the choice of `u`.
- *Theorem A(3) applies:* by (2), `R` is the internal free product of the
  factors `R_(gC) = g R0 g^-1`, all isomorphic to `R0`.  The action of `F^(n)`
  permutes them freely.  `R0` is locally free, hence sofic.

So part 3 of [[permuted-free-product-linton-radical-gives-sofic-shell]]
supplies the halo `Y -> *_Y R0` and the `F^(n)`-equivariant isomorphism.

(5) *Soficity.*  The stabilizers of the `F`-action on `X` are the cyclic groups
`g C g^-1`, and the factors are sofic.  So part 2 of the same theorem makes
`G_u` sofic.  Alternatively, `G_u` is an amalgam of the residually finite group
`G0` with `F` over `Z`.  Such amalgams of sofic groups over amenable subgroups
are sofic by Elek--Szabo (arXiv:1010.3424, Theorem 1), as cited in that
theorem's proof route.  ∎

Examples.

- `d = 0`, `u = p`: `G_p = G0 * <q>`.  It fails only at stage 0.
- `d = 1`, `u = [p,q]`: it fails at stages 0 and 1 and succeeds from stage 2
  on.  The relator has length `6|u| + 5 = 29`.

## 6. Consequences for `linton-radical-has-equivariant-sofic-halo`

The target reads: "Let `E = R semidirect_alpha F0` be the finite
rational-derived shell of a one-relator group.  There exist ... [a halo
presentation with sofic finite pieces]".  The stage `n` of the shell is not
fixed by [[one-relator-soficity-localizes-at-rational-derived-stage]], which
only asserts that some `n <= |w|` is valid.

1. *Least valid stage.*  The target is **false** for `G0`, with `n = 0`, by
   Proposition 5(5).
2. *Every valid stage.*  It is false for the same reason, and for `G_u` at all
   `n <= d`.
3. *Some valid stage.*  The target is **not refuted** by these examples: they
   satisfy it at every stage beyond `d` (Propositions 5(6), 6(4)).  Nor does
   soficity decide anything, since all the examples are sofic.
4. *What any proof must do.*  Let `R` be locally free.  Then a halo
   presentation at stage `n` requires that no element of `G_Q^(n)` conjugate a
   finitely generated subgroup of `R` properly into itself.  More generally,
   Corollary 2 must hold at that stage.
   - For the permuted-free-product class, the stage must be deep enough for
     `F^(n)` to meet every stabilizer containing a contracting element
     trivially.
   - For `G_u`, the least admissible stage is `d+1`, where `d` is the
     derived depth of `u`.
   - Since `d` is arbitrary, the least admissible stage is not bounded by a
     universal constant.  It depends on the relator.
5. *Downstream routes.*  Soficity of `G` is equivalent to soficity of `E_n` at
   any valid `n` (part 3 of the localization claim).  So the routes
   `linton-halo-gives-radical-sofic`, `linton-halo-gives-action-sofic` and
   `linton-shell-sofic-via-sofic-action` lose nothing if the shell is taken at
   a deeper stage.  The obstruction therefore does not invalidate them.  It
   pins down which reading of the target they can use.
6. *Open (all-stage refutation).*  Is there a one-relator group `G` such that,
   at every valid stage `n`, `G_Q^(n)` violates Corollary 2 for some finitely
   generated `H <= R`?  Examples would be a contraction, or an automorphism of
   infinite outer order on a noncyclic `H` when `R` is locally free.  Such a
   `G` would refute the existential reading.
   - Amalgams of `G0` along a single word `u` cannot do this, because the
     contraction depth is the derived depth of one fixed word.
   - A contraction at every depth needs contracting elements in `F0^(n)` for
     every `n`.  Composites of contractions of one subgroup are positive words
     in the contracting letters, and positive words never lie in `F'`.
   - An infinite-order outer action of a non-solvable subgroup of `F0` on a
     fixed noncyclic `H` would work at every depth.  No one-relator example is
     known to us.

## 7. Sources

- V. Alekseev, H. Bradford, *Sofic actions, halo products, and metric
  approximations of groups*, arXiv:2601.18742v1 (submitted 2026-01-26; abstract
  page fetched 2026-09-16, still v1).  Definitions 2.1 and 2.4 are quoted from
  the audit in `research/artifacts/or-linton-halo-2026-09-12.md`.
- M. Linton, *Residually rationally solvable one-relator groups*,
  arXiv:2407.09272 (v1 2024-07-12, v2 2025-09-19, to appear in Bull. LMS;
  abstract page fetched 2026-09-16).
- A. Borisov, M. Sapir, *Polynomial maps over finite fields and residual
  finiteness of mapping tori of group endomorphisms*, arXiv:math/0309121,
  Invent. Math., DOI 10.1007/s00222-004-0411-2 (abstract page fetched
  2026-09-16).
- F. Berlai, *A new family of sofic one-relator groups*, arXiv:2502.05064
  (February 2025; seen in an arXiv listing on 2026-09-16, calibration only).
- G. Elek, E. Szabo, arXiv:1010.3424, Theorem 1.  Cited as in the landed route
  `permuted-free-product-linton-radical-gives-sofic-shell-proof`; not
  re-fetched.
- Classical, not re-fetched and so unverified here: Takahasi's chain condition
  for bounded-rank subgroups of free groups (1951), which also gives Lemma 3;
  Schreier's index formula; virtual torsion-freeness of `Out(F_r)`.  Lemma 3 is
  proved above without them.  The last two are used only in the unused Remark
  of Section 3.
- An arXiv listing search on 2026-09-16 ("sofic one-relator", "halo products
  sofic", "rational derived series one-relator", "ascending HNN free group
  sofic") found no 2024--2026 paper on halo presentations of one-relator
  radicals or on this obstruction.  The web-search quota was exhausted, so
  coverage beyond arXiv listings was not checked.
