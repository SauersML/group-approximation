# Torus degree matrices: the augmentation dichotomy on the support subgroup (2026-09-17)

Author: swarm-0917-w9-w9-gs-break. Notation as in
`research/artifacts/torus-alphabet-degree-2026-09-17.md` Section 0: `X_d = (T^d)^G`,
`tau` a torus automaton (continuous, equivariant, no finite memory), `D = D(tau)` in
`M_d(Z[G])` with `tau^*(xi) = xi D`, `epsilon` the augmentation.

Imported (ESTABLISHED in the graph):
- **(L2)** `torus-automata-over-rf-or-domain-groups-are-surjunctive`, periodic-point lemma
  with `N = G`: for injective `tau` over every group, `epsilon(D) in GL_d(Z)`.
- **(C1)** `torus-automata-with-regular-degree-are-surjective`: if `xi -> xi D` is
  injective on `Q[G]^d` then `tau` is onto.

Definitions.
- `supp D` is the union of the supports of the `d^2` entries; `H(D) = <supp D>`, a
  finitely generated subgroup of `G`.
- A group `H` is **RPP** (residually prime-power) if for every finite `S subset H` there
  are a prime `p` and a normal `N <| H` with `H/N` a finite `p`-group and `S -> H/N`
  injective. The prime may depend on `S`.
- `(A_d)(H)`: every `D in M_d(Z[H])` with `epsilon(D) in GL_d(Z)` has `xi -> xi D`
  injective on `Q[H]^d`.

## 1. Reduction to the support subgroup

**Lemma 1.** Let `H <= G` and `D in M_d(Z[H])`. If `xi -> xi D` is injective on `Q[H]^d`,
it is injective on `Q[G]^d`.

*Proof.* Choose a left transversal `R` of `H` in `G`. Then `Q[G]^d = (+)_(r in R) r Q[H]^d`
as a direct sum of subspaces. Right multiplication by `D` maps `r Q[H]^d` into itself
because the entries of `D` lie in `Q[H]`. Write `xi = sum_r r xi_r` with `xi_r in Q[H]^d`.
Then `xi D = sum_r r (xi_r D)`, and the summands lie in distinct direct summands. So
`xi D = 0` forces `xi_r D = 0` for every `r`, hence every `xi_r = 0`. QED.

So C2 for a given `tau` depends only on the pair `(H(D), D)`. The ambient group enters
only through which `D` can occur as degrees of injective automata.

## 2. Positive half: RPP support forces regularity, for every d

**Lemma 2 (nilpotent augmentation ideal).** For a finite `p`-group `P`, the augmentation
ideal `I` of `F_p[P]` is nilpotent.

*Proof.* Induct on `|P|`; `|P| = 1` is trivial. Otherwise pick a central `z` of order
`p`. The kernel of `F_p[P] -> F_p[P/<z>]` is `(z - 1) F_p[P]`, and `(z - 1)^p = z^p - 1 = 0`
with `z - 1` central, so that kernel `J` satisfies `J^p = 0`. The image of `I` is the
augmentation ideal of `P/<z>`, nilpotent by induction: `I^m subset J` for some `m`. So
`I^(mp) = 0`. QED.

**Corollary 3.** For a finite `p`-group `P` and `E in M_d(F_p[P])` with
`epsilon(E) in GL_d(F_p)`, `E` is invertible in `M_d(F_p[P])`.

*Proof.* `M_d(F_p) subset M_d(F_p[P])` via the unit. `E = epsilon(E) + M` with
`M in M_d(I)`. `M_d(I)` is a two-sided ideal with `M_d(I)^k subset M_d(I^k)`, so it is
nilpotent. `epsilon(E)` is invertible, so `E = epsilon(E) (1 + epsilon(E)^-1 M)` and the
second factor is `1 + nilpotent`, invertible. QED.

**Theorem 4.** If `H` is RPP, then `(A_d)(H)` holds for every `d`.

*Proof.* Let `D in M_d(Z[H])`, `epsilon(D) in GL_d(Z)`, and `0 != v in Q[H]^d` with
`v D = 0`.
- Clearing denominators, take `v in Z[H]^d`. Write `v = p^k w` for the prime `p` chosen
  below, with `w in Z[H]^d` having some coefficient not divisible by `p`. Since `Z[H]^d` is
  torsion-free, `w D = 0`, and `supp w = supp v`.
- By RPP, applied to `S = supp v`, pick `p` and `N` with `P = H/N` a finite `p`-group
  injective on `supp v`. (Choose `p` first, then `k`.)
- Reduce: `pi: Z[H] -> F_p[P]`. Since `supp w -> P` is injective, `pi(w)` has the same
  coefficients as `w` mod `p`, so `pi(w) != 0`.
- `pi(w) pi(D) = pi(w D) = 0`, and `epsilon(pi(D)) = epsilon(D) mod p in GL_d(F_p)`. By
  Corollary 3, `pi(D)` is invertible, so `pi(w) = 0`. Contradiction. QED.

**Corollary 5 (new torus-surjunctive hosts).** Let `G` be a countable group in which every
finitely generated subgroup is RPP. Then for every `d`, every injective torus automaton on
`X_d` over `G` is surjective.

*Proof.* `H(D)` is finitely generated, hence RPP. By (L2) `epsilon(D) in GL_d(Z)`. By
Theorem 4 and Lemma 1, `xi -> xi D` is injective on `Q[G]^d`. By (C1) `tau` is onto. QED.

Examples of such `G`. Items marked * are not residually finite, or are torsion hosts
with `d >= 2`, so they are not covered by Theorem 3 of the parent artifact.
- every locally finite `p`-group (f.g. subgroups are finite `p`-groups), e.g. `Z(p^inf)`*,
  `(+)_N Z(p^inf)`* and the finitary symmetric-type `p`-groups (unions of finite
  `p`-groups);
- every torsion-free abelian group (f.g. subgroups are `Z^r`, residually `p` for all `p`),
  e.g. `Q`*, `Z[1/m]`* and `Q^n`*, at every `d` (the parent covered only `d = 1`);
- every abelian group whose torsion subgroup is a `p`-group, e.g. `Q (+) Z(p^inf)`*;
- every locally free group and every locally torsion-free-nilpotent group (f.g. torsion-free
  nilpotent groups are residually `p` for every `p`; Gruenberg).

All of these are amenable or locally residually finite, hence sofic. So Corollary 5 adds
no host relevant to Gottschalk's conjecture. Its value is diagnostic (Section 4).

## 3. Negative half: the Bezout witness

**Proposition 6.** Let `K` be a finite group whose order is not a prime power. Then
`(A_1)(K)` fails. If `K <= H`, then `(A_1)(H)` fails too.

*Proof.* `|K|` has two distinct prime divisors `p < q`. By Cauchy there are `s, t in K`
of orders `p, q`. Put `P_s = sum_(i<p) s^i`, `P_t = sum_(j<q) t^j`, choose integers
`a p + b q = 1`, and set

    D = a P_s + b P_t in Z[K],   epsilon(D) = a p + b q = 1.

- `P_s = p e_s` with `e_s = P_s / p` idempotent. The left ideal `L_s = {xi : xi e_s = 0}
  = Q[K](1 - e_s)` has dimension `|K| - |K|/p`, since `Q[K] e_s` is spanned by the
  `|K|/p` coset sums `g P_s`. Likewise `dim L_t = |K| - |K|/q`.
- `dim(L_s cap L_t) >= |K| (1 - 1/p - 1/q) > 0`, because `1/p + 1/q <= 1/2 + 1/3 < 1`.
- Any `0 != xi in L_s cap L_t` has `xi D = a xi P_s + b xi P_t = 0`.
- `Q[K] subset Q[H]`, so the same `xi` kills `D` in `Q[H]`. QED.

For `K = Z/6` with `t` of order 2 and `s` of order 3 this is `D = (1+s+s^2) - (1+t) =
s + s^2 - t`, the example of the parent artifact. So the parent's example is one member
of a family that exists in every group with a non-prime-power finite subgroup.

**Computation.** `experiments/torus-prime-power-2026-09-17/check_prime_power_dichotomy.py`
checks the following exactly over `Q`.
- Part A: the Bezout witness has `epsilon = 1` and rank `< |K|` on `Q[K]` for
  `K = Z/6, Z/10, Z/15, S_3, A_4, S_4`. The ranks are `4, 6, 7, 4, 9, 16`. Each is at most
  `|K|/p + |K|/q = |K| - |K|(1 - 1/p - 1/q)`, as the proof predicts.
- Part B: for 200 random `D in M_d(Z[P])` with `d <= 3`, `epsilon(D) in GL_d(Z)`, over
  `P = Z/4, Z/2^2, D_4, Z/9, Z/3^2`, right multiplication is invertible mod `p` and over
  `Q`, as Theorem 4 predicts.

## 4. What this changes: the exact reach of augmentation-only proofs of C2

Call a proof of C2 **augmentation-only** if it uses only `epsilon(D) in GL_d(Z)`, the data
carried by the circle of constants, plus ring theory of `Z[G]`.

**Dichotomy.** For a finitely generated support group `H = H(D)`:
- if `H` is RPP, augmentation-only proofs succeed at every `d` (Theorem 4);
- if `H` contains a finite subgroup of non-prime-power order, every augmentation-only proof
  dies, already at `d = 1`. The invariant is the Bezout witness `a P_s + b P_t`, and the
  failing step is the passage from `epsilon(D) = 1` to injectivity of `xi -> xi D`
  (Proposition 6).
- Between the two, e.g. f.g. groups whose finite subgroups are `p`-groups but which are
  not RPP (Tarski monsters of exponent `p`, torsion-free non-RPP groups at `d >= 2`),
  status is open.

**Consequence 1: C2 localizes to non-RPP support.** Over every group, a
counterexample to C2 must have `H(D)` non-RPP. Via Lemma 1 the ambient group is
irrelevant to the algebra. So a C2 counterexample is an injective torus automaton whose
degree lies in `Z[H]` for a non-RPP f.g. `H`, and which has no finite quotient of `G`
separating the singular part (Lemma 2(2) of the parent kills it otherwise).

**Consequence 2: the smallest open host is amenable and locally finite.** Take
`G = Z(2^inf) x Z(3^inf)`, or `G = Q/Z`.
- `G` is divisible, so it has no nontrivial finite quotients, and Lemma 2(2) of the parent
  gives nothing beyond `epsilon(D)`.
- Its f.g. subgroups are finite cyclic of composite order, so Proposition 6 applies:
  `D = s + s^2 - t` is singular with `epsilon(D) = 1`.
- `G` is locally finite, so finite-alphabet surjunctivity over `G` is elementary, by
  restricting to a finite subgroup that contains the memory set.
- But torus surjunctivity over `G` is **not known** from any tool in the graph. Torus
  automata have no finite memory, so the locally-finite argument does not apply.

So `every-group-is-torus-surjunctive` is open even on countable abelian locally finite
groups, where Gottschalk's conjecture is trivial. This falsifies the heuristic behind
`gottschalk-via-torus-alphabet-degree-transfer`, namely that TS is the easier,
characteristic-zero shadow of GOT, provable where GOT is hard.
- On the hosts that matter for GOT, non-sofic groups, C2 is exactly as hard as on `Q/Z`
  plus whatever non-soficity adds.
- The only known infinite-dimensional replacement for invariance of domain there would be
  a mean-dimension drop on proper subsystems. No such drop theorem for proper subshifts of
  `(T^d)^G` is recorded in the graph for any non-residually-finite `G`, amenable or not
  (recalled from memory, no verbatim citation: over `Z` with alphabet `[0,1]` proper
  subshifts of full mean dimension exist, so such a drop is not automatic).

**Concrete test (need).** Construct, or rule out, an injective continuous equivariant
`tau` on `T^(Q/Z)` (or on `T^(Z(2^inf) x Z(3^inf))`) with `D(tau) = s + s^2 - t`, where `s`
has order 3 and `t` has order 2.
- By C1 and Proposition 6, such a `tau` is automatically not onto, which refutes TS.
- Its restriction to a finite-subgroup coset block cannot be injective: `D` is singular
  over `Q[<s,t>]`, and the block map would be a self-map of the torus
  `T^6` of degree `det = 0`.
- So `tau` must move information between blocks, Hilbert-hotel style, along the
  increasing chain `Z/6 < Z/12 < Z/36 < ...`, with memory growing without bound.
