# The K1 route to Toms--Winter: constraint map (2026-09-11)

Lane `lix-toms-winter-1`. Question: can the repository's LIX mechanism
(characteristic-class obstructions to K1-injectivity that survive an
inductive limit) produce a counterexample to STW Problem XVIII?

The route. Jiang proved that a unital Z-stable C*-algebra is K1-bijective.
So a simple separable unital nuclear non-elementary algebra with strict
comparison that is **not** K1-injective refutes Problem XVIII. Call such an
algebra a *K1-witness*.

Summary of what this note proves or imports.

1. Every unital simple AH algebra with strict comparison is Z-stable, hence
   K1-injective. In particular every LIX algebra of the `stw59-*` region
   fails strict comparison, and no strict-comparison upgrade that stays AH
   can be a K1-witness. (Imports: Toms, Winter, Jiang.)
2. A K1-witness `A` has: nonempty trace space and stable finiteness; stable
   rank at least two; a non-surjective rank map `Gamma`, so all ranks do not
   occur, tracial approximate oscillation zero fails and `A` is not pure; `A`
   is not AH; the extreme tracial boundary is not compact finite-dimensional
   and fails Lin's condition (C). Consequently a K1-witness refutes
   **both** Problem XVIII and the Rank Problem XXIII. (Imports: Rieffel,
   Cuntz, Lin twice, Toms--White--Winter.)
3. Two elementary structural propositions, proved here, locate where the
   LIX mechanism has to spend topology: (D) a homogeneous tower that fails
   K1-injectivity has a block with spectrum dimension at least twice its
   rank at every late stage; (E) pullback-plus-untwisted-point-evaluation
   connecting maps kill every K1-null unitary after one step, so the
   Villadsen line-bundle twist on the tracially dominant summands of the
   LIX towers is not decoration but the whole mechanism.

Nothing here refutes or proves Problem XVIII. The route survives only
outside AH algebras, with rank gaps and wild trace simplices.

## 1. Sources checked on 2026-09-11

- X. Jiang, *Nonstable K-theory for Z-stable C*-algebras*,
  [arXiv:math/9707228](https://arxiv.org/abs/math/9707228). Abstract: the
  homotopy groups of `U(A)` are stable invariants, `pi_i(U(A)) = K_(i-1)(A)`,
  for unital Z-stable `A`. Theorem 2.8 (as already used by
  `stw99-lxxvi-z-stable-unitary-kernel-proof`) says every canonical
  matrix-stabilization map induces isomorphisms on all homotopy groups. For
  `i=0` this is K1-bijectivity: `U(A)/U_0(A) -> K_1(A)` is an isomorphism.
- A. S. Toms, *Characterizing classifiable AH algebras*,
  [arXiv:1102.0932](https://arxiv.org/abs/1102.0932) (3 pages; closes a gap in
  Theorem 1.2 of arXiv:0910.2061). Abstract verbatim: "We observe almost
  divisibility for the original Cuntz semigroup of a simple AH algebra with
  strict comparison. As a consequence, the properties of strict comparison,
  finite nuclear dimension, and Z-stability are equivalent for such
  algebras". The Z-stability step is Winter's theorem (pure plus locally
  finite nuclear dimension gives Z-stability, Invent. Math. 2012), the same
  chain written out in `toms-gamma-counterexample-strict-comparison-proof`.
  The journal reference was not verified in this pass; the arXiv statement
  is what is imported.
- H. Lin, *Strict comparison and stable rank one*,
  [arXiv:2301.09250v2](https://arxiv.org/abs/2301.09250), J. Funct. Anal. 289
  (2025), 111065. Theorem 1.1 verbatim: "Let A be a sigma-unital
  non-elementary simple C*-algebra with strict comparison (which is not
  purely infinite). Then the following are equivalent: (1) The canonical map
  Gamma: Cu(A) -> LAff_+(QT~(A)) is surjective. (2) A has tracial
  approximate oscillation zero. Moreover, if (1) or (2) hold, then A has
  stable rank one." The paper requires `QT~(A) != {0}`. Here `LAff_+(S)`
  consists of pointwise increasing limits of functions that are strictly
  positive continuous affine or zero. The introduction also states: "At this
  moment, we do not even know, in general, a separable amenable finite simple
  C*-algebra with strict comparison has stable rank one."
- H. Lin, *Tracial oscillation zero and Z-stability*,
  [arXiv:2112.12036v6](https://arxiv.org/abs/2112.12036), to appear in Adv.
  Math. Theorem 5.6: a separable non-elementary simple amenable C*-algebra
  whose tracial cone has a basis satisfying condition (C) is Z-stable if and
  only if it has strict comparison. Condition (C): the extreme boundary is a
  countable union of compact finite-dimensional pieces `X_n` (pairwise
  disjoint from index 2 on) with the closed-convex-hull compatibility
  conditions of the paper. Examples include one-point compactifications of
  countable disjoint unions of cubes, finite-dimensional Bauer simplices, and
  certain countably supported non-Bauer simplices.
- Toms--White--Winter (finite-dimensional compact boundary), already imported
  as `stw18-finite-trace-boundary-toms-winter`.
- Rieffel, Proc. London Math. Soc. 46 (1983), Theorem 10.12 (stable rank one
  gives `U(A)/U_0(A) ~= K_1(A)`), and Cuntz, Ann. of Math. 113 (1981) (simple
  purely infinite algebras are K1-injective), both as recorded in
  `stw58-simple-pure-k1-bijective-proof`.

## 2. Theorem A: AH algebras cannot carry the K1 route

**Theorem A.** Let `A` be a unital simple AH algebra with strict comparison.
Then `A` is Z-stable and `U(A)/U_0(A) -> K_1(A)` is bijective.

*Proof.* Toms's theorem gives Z-stability; Jiang's theorem gives
K1-bijectivity. Square.

**Corollary A1.** Every LIX algebra fails strict comparison. This covers the
order-two algebra of `stw59-simple-ah-non-k1-injective` and every algebra
`A_G` of `stw59-exact-finite-abelian-unitary-component-groups` (the cyclic and
factorial families are special cases).

*Proof.* The building blocks are `Gamma(X_i, End E_i)` over finite CW
complexes. Embedding `E_i` in a trivial bundle `theta^n` with projection `p`
identifies the block with the corner `p M_n(C(X_i)) p`, so the algebras are
AH. They are simple, unital and not K1-injective. Theorem A forbids strict
comparison. Square.

For the monotracial families there is a second, independent proof: unique
trace plus strict comparison gives Z-stability by Toms--White--Winter.

**Consequence for the route.** Any strict-comparison upgrade of the LIX
towers that keeps homogeneous building blocks and unital connecting maps is
still AH, so it is K1-injective. The route "upgrade the LIX tower to strict
comparison" is dead as long as the result is AH.

## 3. Theorem B: what a K1-witness must look like

Let `A` be a K1-witness: simple, separable, unital, nuclear, non-elementary,
with strict comparison, and not K1-injective.

(i) *Traces and finiteness.* `A` is not purely infinite, since simple purely
infinite algebras are K1-injective (Cuntz). Strict comparison is taken, as
in Lin's theorem and in `stw63-strict-comparison-sr1-uniqueness`, with
respect to a nonempty quasitrace simplex; without that convention the
condition is vacuous. Nuclearity gives exactness, so quasitraces are traces
(Haagerup). A trace on a simple algebra is faithful, so `A` is stably finite.

(ii) *Stable rank.* `sr(A) >= 2`, by Rieffel.

(iii) *Ranks.* By (i), Lin's Theorem 1.1 applies. If `Gamma` were
surjective, `A` would have stable rank one, contradicting (ii). So `Gamma` is
not surjective and tracial approximate oscillation zero fails. For unital
separable exact `A`, `T(A)` is a metrizable Choquet simplex, and every lower
semicontinuous affine `f: T(A) -> (0, infinity]` is an increasing limit of
continuous affine functions `g_n` (Edwards). Compactness and `min f > 0` make
`g_n > min f / 2` for all large `n`. So restricting `LAff_+(QT~(A))` to the
normalized traces gives exactly zero together with these `f`, and some such
`f` is not the rank of any positive element of `A tensor K`. The algebra is also not
pure: pure unital simple algebras are K1-bijective
(`stw58-simple-pure-k1-bijective`).

(iv) *Not AH.* Theorem A.

(v) *Not Z-stable.* Jiang. So `A` refutes Problem XVIII.

(vi) *Wild trace simplex.* The extreme tracial boundary is not compact
finite-dimensional (Toms--White--Winter), and the tracial cone admits no basis
satisfying Lin's condition (C) (Lin, Theorem 5.6).

(vii) *Rank Problem.* By (i) and (iii), `A` is a unital simple separable
stably finite non-elementary algebra in which not all ranks occur, so `A`
refutes STW Problem XXIII.

So the K1 route to XVIII is at least as hard as refuting the Rank Problem
inside strict-comparison algebras. The XXIII node records that no candidate
for failure of the Rank Problem is currently known.

The XVIII root also records the published implication "strict comparison
plus uniform property Gamma gives Z-stability"; a K1-witness therefore also
lacks uniform property Gamma. That item is not imported as a separate node in
this pass.

## 4. The stable range lemma used below

**Lemma C.** Let `X` be a finite CW complex of dimension `d` and `F` a complex
vector bundle of constant rank `r`. If `d+1 <= 2r`, the canonical map
`pi_0 U(Gamma(X, End F)) -> K_1(Gamma(X, End F))` is an isomorphism, and every
stabilization `pi_0 U(Gamma End(nF)) -> pi_0 U(Gamma End((n+1)F))` is an
isomorphism.

This is the `k=0` case of the lemma proved in Section 3 of
[stw59-unique-trace-and-matrix-stability-2026-09-05.md](stw59-unique-trace-and-matrix-stability-2026-09-05.md)
(Stiefel connectivity plus relative cellular obstruction theory plus the
polar-lift gauge fibration). For a bundle `E ⊕ theta^N` the same lemma
applies with `r` replaced by `rank E + N`.

## 5. Proposition D: dimension needed at every late stage

**Proposition D.** Let `A = lim (A_j, phi_j)` with unital injective
connecting maps and

```text
A_j = direct-sum_(k=1..n_j) Gamma(X_(j,k), End E_(j,k)),
```

where each `X_(j,k)` is a finite CW complex of dimension `d_(j,k)` and
`E_(j,k)` has constant positive rank `r_(j,k)`. If for infinitely many `j`
every block satisfies `d_(j,k) + 1 <= 2 r_(j,k)`, then `A` is K1-injective.
Equivalently, if `A` is not K1-injective, then for all sufficiently large `j`
some block of `A_j` has `d_(j,k) >= 2 r_(j,k)`.

*Proof.* Let `u in U(A)` have `[u]=0` in `K_1(A)`. Then `u ⊕ 1_n` lies in
`U_0(M_(n+1)(A))` for some `n`. Choose a stage `i` and `u_i in U(A_i)` whose
image is within distance `1` of `u`; the principal logarithm joins the two in
`U(A)`, so the image of `u_i ⊕ 1_n` is null-homotopic in `M_(n+1)(A)`.

Null-homotopies in injective unital inductive limits are detected at a finite
stage. This is the disk argument of Section 4 of the same stw59 artifact: a
disk of unitaries in the limit with prescribed boundary is approximated by a
disk at one stage with exactly that boundary, using a bounded linear collar
extension and the polar decomposition. So there is `j_0 >= i` with
`phi_(i,j)(u_i) ⊕ 1_n in U_0(M_(n+1)(A_j))` for every `j >= j_0`. Pick such
a `j` at which every block is in the stable range.

Write `v_k` for the component of `phi_(i,j)(u_i)` in block `k`. Then
`v_k ⊕ 1_n` is null-homotopic in `U(Gamma End(E_(j,k)^(n+1)))`. By Lemma C
the stabilization maps from `E_(j,k)` up to `(n+1)E_(j,k)` are isomorphisms
on `pi_0`, because `d_(j,k)+1 <= 2 r_(j,k) <= 2 m r_(j,k)` for every
`m >= 1`. Hence each `v_k` is null-homotopic, so `phi_(i,j)(u_i) in U_0(A_j)`
and `u in U_0(A)`. Square.

The obstruction-carrying block can have arbitrarily small tracial weight, so
Proposition D alone says nothing about comparison. What it forbids is a
K1-witness built from homogeneous blocks whose every block is in the stable
range, which is the slow-dimension-growth regime at the level of the unit.

## 6. Proposition E: untwisted point evaluations kill the obstruction

**Proposition E.** Let `X` be a connected finite CW complex of dimension `d`,
`E` a rank-`r` bundle, `B = Gamma(X, End E)`, `Y` compact Hausdorff,
`pi: Y -> X` continuous, and `x_1, ..., x_m in X` with chosen unitary
identifications `E_(x_l) ~= C^r`. Define the unital *-homomorphism

```text
psi : B -> Gamma(Y, End(pi^*E ⊕ theta^(m r))),
psi(a) = pi^*a ⊕ diag(a(x_1), ..., a(x_m)).
```

If `u in U(B)` has `[u] = 0` in `K_1(B)` and `d+1 <= 2 r (m+1)`, then `psi(u)`
is null-homotopic.

*Proof.* `U(r)` is path connected; choose paths `w_l` from `u(x_l)` to `1`.
The path `pi^*u ⊕ diag(w_1(t), ..., w_m(t))` joins `psi(u)` to

```text
pi^*u ⊕ 1_(m r) = pi^*(u ⊕ 1_(m r)),
```

the pullback of the unitary `u ⊕ 1` of `Gamma(X, End(E ⊕ theta^(m r)))`. Its
`K_1` class is the image of `[u]=0` under the corner inclusion, hence zero.
The bundle `E ⊕ theta^(m r)` has rank `r(m+1)` with `d+1 <= 2r(m+1)`, so
Lemma C makes `u ⊕ 1_(m r)` null-homotopic over `X`. Pulling the path back
along `pi` is a unital *-homomorphism of section algebras, so `psi(u)` is
null-homotopic. Square.

**Corollary E1.** Consider a tower of the LIX shape, with
`A_(j+1) = Gamma(X_(j+1), End(pi_j^*E_j ⊕ theta^(m_j r_j)))`, connecting maps
of the form in Proposition E with `m_j >= 1`, and `d_j <= 4 r_j - 1` (the
stw59 towers have `d_j = 2 r_j`). Then every K1-null unitary of `A_j` is
null-homotopic in `A_(j+1)`, so the limit is K1-injective.

The stw59 towers escape Corollary E1 only because their point-evaluation
summands are `E_j(x_j) tensor L_(j+1) = L_(j+1)^(⊕ r_j)`: the tracially
dominant half of every new stage is twisted by a line bundle `L_(j+1)` over a
new factor of dimension `2r_j`. Then `psi(u)` is homotopic to
`pi^*u ⊕ 1` inside `End(pi^*E_j ⊕ L_(j+1)^(⊕ r_j))`, which is not pulled
back from `X_j`. The Euler-degree persistence nodes of the stw59 region
compute that this class survives.

## 7. Where the topology has to go, and why this conflicts with comparison

This section is heuristic and is not recorded as an established claim.

Propositions D and E say that a unit-level K1 obstruction persisting through
a type I tower needs, at every stage, spectrum dimension at least twice the
rank on the carrying block. It also needs the complement that the connecting
maps add on top of the pullback to be topologically nontrivial, not pulled
back from the earlier base. In the stw59 towers that complement has half the
trace at every stage, and its twisting class `c_1(L)^(r_j)` is nonzero. That
is Villadsen's perforation mechanism. For `p = L^(⊕ s)` and a trivial
`theta^t`, the total Chern class of a complement of `p` in `theta^t` would be
`(1+c_1(L))^(-s)`, so `p ≲ theta^t` forces `c_1(L)^(t-s+1) = 0`, a gap of
order the rank. Toms's theorem is the rigorous version for all AH algebras.

Nothing of the kind is proved for approximately subhomogeneous building
blocks, and nothing at all for non-type-I blocks. Those are the only places
Theorem B leaves open.

## 8. What survives

A K1-witness must be a non-AH simple nuclear algebra combining: strict
comparison; stable rank at least two with a unit-level K1 obstruction that
dies at matrix size two or later; an unrealized rank function; no pureness;
and a tracial simplex outside condition (C). No known algebra has all of
these. Concretely the design problem is "a strict-comparison counterexample
to the Rank Problem whose unit carries a persistent characteristic-class
obstruction".

## 9. Graph wiring

Established imports: `z-stable-unital-algebras-are-k1-bijective`,
`simple-ah-strict-comparison-is-z-stable`,
`stable-rank-one-unital-algebras-are-k1-bijective`,
`strict-comparison-rank-surjectivity-forces-sr1`,
`lin-condition-c-boundary-strict-comparison-z-stable`,
`bundle-endomorphism-unitaries-stable-range`.

Established derivations: `simple-ah-strict-comparison-is-k1-injective`,
`stw59-lix-algebras-fail-strict-comparison`, `stw18-k1-witness-constraints`,
`homogeneous-tower-k1-failure-needs-twice-rank-dimension`,
`untwisted-point-evaluations-kill-k1-obstructions`.

Open: `stw18-k1-witness-strict-comparison-not-k1-injective`, feeding the new
negation roots `stw18-strict-comparison-non-z-stable-algebra-exists` and
`stw23-rank-problem-counterexample-exists`. Dead route:
`stw18-k1-witness-via-ah-lix-upgrade`, invalidated by
`simple-ah-strict-comparison-is-k1-injective`.
