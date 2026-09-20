---
rg: 2
id: mod-s2-torelli-abelian-census-limit-is-positive
kind: claim
title: The monomial census limit d_inf of Mod(S_2) is positive, so representations with abelian Torelli image keep a separating twist uniformly away from the cube-root scalars
distinct_from:
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the uniform operator-norm gap for all finite-dimensional representations; this is its restriction to representations of M/[K,K], which by (TA1) is the arithmetic statement d_inf > 0 about abelianizations of finite-index subgroups. That claim implies this one; the converse is not known.
  mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit: that proves the reduction to d_inf and computes d at finitely many levels (all values 1/15 or 1/30); this asks for positivity of the limit over all levels.
  deligne-torelli-character-counts-separating-twists: its exact exclusion (ST5) is the statement d(Gamma') > 0 for each single level; this asks for a bound uniform in the level.
---

**OPEN.** Notation as in `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`. The claim is

```text
d_inf = inf_N d(Gamma(N)) > 0 .                                          (TAP)
```

By (TA1) there, (TAP) says the following. There is `delta > 0` such that every finite-dimensional unitary
representation `rho` of `M = Mod(S_2)` with `rho(K)` abelian satisfies
`||rho(t_s) - omega^(+-1) I||_op >= delta`. The sharp constant is `2 sin(pi d_inf)`.

Arithmetic form: there is `eps > 0` such that for every `N` and every character `psi` of
`M_N = pi^(-1)(Gamma(N))`, some separating twist `T` has `||arg psi(T)/(2 pi) - 1/3|| >= eps`.

**Conjecture (sharp form).** `d_inf = 1/30`, attained already at `Gamma(2)`.

## Position in the graph

- **Implied by** `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`, by restriction to
  Torelli-abelian representations. That implication is not filed as a route, so no cycle forms.
- **Necessary for the flagship.** If (TAP) fails, that gap claim fails. Then `1/3 in P_op`, and
  `deligne-triple-cover-exact-mf-radical` is refuted (see the gap claim's "Position in the graph"). So a
  single family of characters of congruence subgroups of `M` with all separating-twist values near `1/3`
  would refute the flagship.
- **What it is not.** (TAP) does not suffice for the gap claim. Representations with nonabelian Torelli
  image are not covered. Quantum and Jones representations are examples.

## Known partial information

- *Each level.* `d(Gamma') > 0` for every single `Gamma'`, by Deligne (ST5): `d = 0` at one level would
  give an exact cube-root scalar.
- *Upper bound.* `d_inf <= d(Gamma(2)) = 1/30` (TA4, TA5).
- *No decay through level three.* All 29 subgroups in the census have `d in {1/15, 1/30}`. These include
  `Gamma(2)`, `Gamma(3)` and 7 intersections of stabilizers at levels 6 and 15.
- *Augmentation constraint.* Push-forward to level one maps `W(Gamma')` into `W(Sp_4 Z) = 5Z` and preserves
  augmentation. So every relation has augmentation divisible by `5`, and `3` never divides the gcd `g(Gamma')`
  of the augmentations (by ST5). In the census `g in {5, 10}`, and the optimal `theta` is constant, equal to
  the nearest point of `(1/g)Z` to `1/3`.

## Why the obvious certificates die (transfer obstruction)

- The level-one relation `5 [t_s] = 0` transfers to `W(Gamma')` as `5 m`, where `m` is the vector of class
  sizes. Its augmentation is `5 [Gamma : Gamma']`.
- `|Sp_4(F_p)| = p^4 (p^2 - 1)(p^4 - 1)` is divisible by `3` for every prime `p`. So `3` divides
  `[Gamma : Gamma(N)]` for every `N > 1`, and the transferred certificate is useless at every principal
  congruence level.
- A proof of (TAP) through (TA3) therefore needs **sparse** relations: `w in W(Gamma(N))` with
  `3 not | aug(w)` and `||w||_1` bounded independently of `N`.
- By Kronecker duality, bounded-`l1` certificates suffice but are not known to be necessary, since the
  number of classes grows with `N`.
- At `Gamma(3)` sparse certificates exist, with `||w||_1 = 5`, even though the transfer dies there.

## Attempts

### 2026-09-18, swarm-0917-w11-w11-deligne-pull (census-computation): sparse certificates at level three are GQ(2,4) point stars

- **What was computed** (`gq24_check.py`). At `Gamma(3)` the 45 classes are the 45 symplectic splittings
  `F_3^4 = P + P^perp`. Transversality (all four plane intersections zero) makes a 12-regular graph with 27
  five-cliques, each splitting in 3 of them. These are the lines and points of `GQ(2,4)`. The 27 point-star
  vectors generate `W(Gamma(3))` over `Z` (rank 21, index 1). Each has `l1 = aug = 5`.
- **Reading.** The level-one relation `5 [t_s] = 0` does not survive the transfer to level three; it only
  survives in the sparse form of a star. A star is five pairwise transverse splittings, i.e. five
  separating twists whose reducing curves have pairwise transverse homology splittings mod 3.
- **Candidate route to (TAP)** (not carried out). Find, for every `N`, a relation among the classes of
  separating twists attached to 5 (or 10) pairwise mod-`N`-transverse splittings, lifting the star
  relation. This would need a geometric relation in `M`, a lantern or chain type relation among
  separating twists, whose image in `H_1(M_N)` is supported on a bounded number of classes. (TA3) would
  then give `d(Gamma(N)) >= 1/15` or `1/30` uniformly.
- **Where it stops.**
  - No such relation in `M` is known to me.
  - The level-two case already differs: `W(Gamma(2))` has rank 1 with `l1 = 10`.
  - `Gamma(9)`, `Gamma(4)` and `Gamma(5)` are out of reach of the enumeration: indices `3^10 * 51840`,
    `2^10 * 720` and `9360000`.
- **Status.** OPEN.

### 2026-09-18, swarm-0917-w12-w12-deligne-follow (census-computation): Gamma(4) computed exactly, d = 1/30, no torsion characters

- **What was computed.** See `mod-s2-gamma4-torelli-census-is-one-thirtieth`, established through
  `mod-s2-gamma4-torelli-census-proof`. Birman-Hilden plus capping replaces the 737280 cosets of
  `Mod(S_2)` by 61440 cosets of `B_5/<Delta^2>`. That makes the exact integral computation feasible.
- **Results.**
  - `H_1(M_4) = Z^54`, torsion-free.
  - There are 160 classes, 16 over each level-two splitting.
  - `W(Gamma(4))` has rank 106 and is saturated, so there are no torsion characters, and `aug(W) = 10Z`.
  - `W` is generated by 60 local relations (augmentation 0) and 1024 transversal 0/1 relations.
  - Each transversal relation has `l1 = aug = 10` and picks one class over each splitting.
  - The 1024 transversal relations form a single `M`-orbit.
  - `d(Gamma(4)) = 1/30`, and `d >= 1/30` for every `Gamma' >= Gamma(4)`.
- **Reading.**
  - The 2-adic tower does not start to decay at its first step.
  - The level-two relation does not survive the transfer: it gives `l1 = 10 * 2^10` and `d >= 1/30720`.
    It survives only as a sparse transversal lift, exactly as the level-three stars do.
  - This settles the "level-two case already differs" point above: level two follows the same
    sparse-lift pattern, with 10 splittings in place of 5.
- **Where it stops.**
  - A uniform bound along `Gamma(2^k)` needs a geometric relation in `M` with 10 separating twists, one
    over each level-two splitting, whose product lies in `[M_(2^k), M_(2^k)]` for all `k`. None is
    identified. The single orbit at `k = 2` suggests one exists.
  - `Gamma(8)` (`2^20 * 60` cosets of `H`) is out of reach of this pipeline.
- **Status.** OPEN.

### 2026-09-19, swarm-0917-w14-w14-deligne-follow (host-geometry): block sums below Gamma(2), and the whole index-two layer above Gamma(4)

- **What was proved.** See `mod-s2-level-eight-index-two-torelli-census`, established through
  `mod-s2-level-eight-index-two-torelli-census-proof`.
  - *(BS).* For every `Gamma' <= Gamma(2)`, pushing a relation forward to `Gamma(2)`, where
    `W = Z (1, ..., 1)`, forces the ten block sums over the level-two splittings to be equal.
  - Hence `aug(W) <= 10 Z`, and `||w||_1 >= 10` for every certificate.
  - `A_+ = 10` if and only if a transversal relation exists, and then `d = 1/30`.
  - Below `Gamma(2)`, (TAP) at the conjectured value `1/30` becomes: a transversal relation exists at
    every level (or a better non-sparse certificate).
- **What was computed.**
  - `H_1(Gamma(4)) = (Z/4)^6 + (Z/8)^4`. So the 1023 index-two subgroups of `Gamma(4)` are exactly
    the hyperplanes of `Gamma(4)/Gamma(8)`. They fall into 15 conjugacy classes.
  - Reidemeister-Schreier over Artin's presentation of `PB_5/<Delta^2>` needs only 1024 cosets per
    subgroup, not 122880. The 122880-coset run did not fit in memory.
  - For all 1023 subgroups: `d = 1/30`, a transversal relation exists, and `aug(W) = 10 Z`.
  - One class of 45 subgroups has `H_1(M'') = Z^54 + Z/2` and 192 classes. This is the first
    2-torsion character of the 2-adic tower, and it does not lower `d`.
- **Reading.** The sparse transversal lift survives the first layer of `Gamma(4)/Gamma(8)`
  everywhere.
- **Where it stops.**
  - `Gamma(8)` itself needs 524288 cosets of `PB_5/<Delta^2>`, which is feasible only with a
    compiled Reidemeister-Schreier.
  - No geometric relation in `M` producing the transversal is identified.
### 2026-09-19, swarm-0917-w15-w15-deligne-pull (census-computation): index-two layer below Gamma(4) computed, d = 1/30, b_1(M_8) = 54

- **What was computed.** See `mod-s2-gamma4-index-two-torelli-census`, established through
  `mod-s2-gamma4-index-two-torelli-census-proof`.
  - The 1023 index-two subgroups `Gamma(8) < G_chi < Gamma(4)` fall into 15 `Sp_4(F_2)`-orbits.
  - For one `chi` per orbit, the [G4] pipeline was run on the 122880 cosets of `H`.
- **Results.**
  - `d(G_chi) = 1/30` for all 1023. In every orbit the certificate is a mass-10 relation with
    `l1 = aug = 10`, so it does not spread to the transfer mass 20.
  - `b_1(M_chi) = 54` in every orbit. `H_1` is `Z^54`, except in orbit 2 (45 subgroups), where it
    is `Z^54 + Z/2` with 192 classes.
  - By the character decomposition of `H_1(M_8; C)` over `Gamma(4)/Gamma(8) = F_2^10`,
    `b_1(M_8) = 54`. The same holds for every `Gamma(8) <= Gamma' <= Gamma(4)`.
- **Reading.**
  - Real characters are frozen from level four to level eight: every real character of `M_8` is
    restricted from `M_4`. So the identity component of `Ann(W(Gamma(8)))` gives exactly `1/30`.
  - Hence `d(Gamma(8)) < 1/30`, the first possible decay of the 2-adic tower, can only come from a
    torsion character of `H_1(M_8; Z)`.
  - In the index-two layer the only torsion is one `Z/2`, and it does not lower `d`.
- **Where it stops.**
  - The torsion of `H_1(M_8; Z)` is not computed. The transfer argument sees only `H_1(-; C)`.
  - It is also open whether `b_1(M_(2^k))` stays 54 for all `k`. For `k = 4`, `Gamma(8)/Gamma(16)` is
    again `sp_4(F_2)`, so the question is again 15 orbit runs. Each run has twice the cosets of
    `M_8`, about 1.26e8, which is out of reach of this coset pipeline.
  - If `b_1` stays 54 along the whole tower, (TAP) on the 2-adic tower becomes a statement about
    torsion characters alone.
- **Status.** OPEN.

### 2026-09-19, swarm-0917-w16-w16-deligne-follow (census-computation): first torsion level Gamma(4,8) computed integrally, the torsion character kills nothing, d = 1/30, A_+ = 10

- **What was computed.** See `mod-s2-igusa-torelli-census-is-one-thirtieth`, established through
  `mod-s2-igusa-torelli-census-proof`.
  - The 512-coset level-four Fox complex is lifted to a free `Z[F_2^4]`-complex for
    `pi^(-1) Gamma(4,8)`, which has 8192 cosets.
  - Elimination is done over the local ring `(Z/2^8)[F_2^4]`, where every odd-augmentation entry is a
    unit.
  - The direct 8192-coset elimination ran out of memory (over 11 GB); the equivariant one needs 11 minutes.
- **Results.**
  - `H_1 = Z^54 + Z/2`, so `k = 1` in (I48).
  - There are 160 classes, one over each level-four class. The order-two torsion character is 1 on
    76 of them.
  - Still, `W(Gamma(4,8)) = W(Gamma(4))`: rank 106, and equal Gram determinant.
  - `d = 1/30` with a mass-10 certificate, and `A_+ = 10`, up from the bound `{10, ..., 160}`.
  - `d = 1/30` on the whole interval `Gamma(4,8) <= Gamma' <= Gamma(4)`.
- **Reading.** The torsion-only failure mode of the 2-adic tower is live, since torsion characters do
  occur and are nontrivial on twists. At its first occurrence it does not fire. On the twist classes the
  new character agrees with a level-four real character, because `W(Gamma(4))` is saturated and `eps`
  pairs evenly with it.
- **Where it stops.**
  - `M_8` has `|A| = 2^10`. The dense stage would need about `54 * 1024` integer columns over
    `Z/2^m`, which is out of reach as written.
  - The same code handles any `Gamma(8) <= Gamma' <= Gamma(4)` with `|Gamma(4)/Gamma'|` up to about
    `2^5`. Such subgroups are not run here.
  - No uniform argument is given.
- **Status.** OPEN.

### 2026-09-19, swarm-0917-w17-w17-deligne-follow (decomposition): short generation of W pins d = 1/30; the 3-Sylow census has no single sharp certificate

- **New lemma.** `mod-s2-short-generated-torelli-relations-pin-one-thirtieth` (ESTABLISHED, short proof).
  Suppose `W(Gamma')` is generated by relations of two kinds:
  - `aug 0` and `l1 <= 30`;
  - `|aug| = 10` and `l1 <= 20`.

  Then `d(Gamma') = 1/30`. The proof has three steps:
  - for such generators, `<w, h>` is forced to equal `3 aug(w)/10` for any lift `h` within `1/30` of `1/3`;
  - so `h - 3/10` is a strictly positive vector orthogonal to `W`;
  - the transfer relation `5 1_X in W` (the (PR) of `mod-s2-induced-torelli-characters-have-positive-relation-floors`)
    forbids such a vector.
- **Decomposition.** If (SG) holds at `Gamma(2N)` for all `N`, then `d_inf = 1/30`, which is the sharp form.
  (SG) splits into two parts:
  - (SG-a): one relation with `aug 10` and `l1 <= 20`;
  - (SG-b): `W_0 = W cap ker(aug)` is generated by vectors with `l1 <= 30`.

  Each level is an independent exact check. This reduces the sharp conjecture to a generation statement
  for the augmentation-zero separating-twist relations. It says nothing about levels where (SG) fails.
- **Computation.** See `mod-s2-three-sylow-torelli-census` (ESTABLISHED), the 3-power direction
  `Gamma(2) -> Gamma(6)` in the `Pbar = PMod(S_{0,6})` model.
  - At `Gamma_V` for `V = U, max_0, max_1, max_2 ~ max_3, Phi` (3-Sylow chain of `Sp_4(F_3)`, down to the
    order-9 Frattini subgroup) the census gives `gcd aug W = 10` and `d = 1/30` exactly. The proof is the
    lemma on an LLL basis, plus an independent box/LP-dual certificate in rationals.
  - `A_+ <= 20` there (MILP value 20).
  - The best single relation has `l1 = 12`, `aug = 10`, so (TA3) gives only `1/36`. This is the first place in
    the census where no single certificate is sharp.
  - So `d = 1/30` holds on all of `Gamma_Phi <= Gamma' <= Gamma(2)`. None of these levels is reached by transfer.
- **2-adic check of (SG).** `level4_sg.py` and `level8_sg.py` recompute `W` in the `Pbar` model.
  - At `Gamma(4)` they reproduce 160 classes and `rank W = 106`, and (SG) holds (`w_1 >= 0` of `l1 = 10`,
    `W_0` generated with `l1 <= 18`). By (W) of `mod-s2-igusa-torelli-census-is-one-thirtieth`, it
    therefore holds at `Gamma(4,8)` too.
  - At all 1023 index-two groups `Gamma(8) < G_chi < Gamma(4)` (15 `Sp_4(F_2)`-orbits), the split form
    (SG0) holds: `w_1 >= 0` of `l1 = 10`, and `W_0` is generated with `l1 <= 22`. The box certificate
    agrees, giving `d = 1/30` at each. At `Gamma_Phi`, (SG0) holds with `||w_1||_1 = 16` and `W_0` `l1 <= 24`.
- **Where it stops.**
  - `Z(U)` needs 8640 cosets, and direct elimination left 17761 dense generators. It was stopped.
  - `Gamma(6)` (25920 cosets) and `Gamma(8)` (524288 cosets) are out of reach of this pipeline.
  - `A_+ = 20` versus 10 at `Gamma_V` is a MILP claim only.
  - No uniform argument for (SG-b) is given. The natural candidate is that `W_0` is generated by relations
    supported on boundedly many cosets (commutation or lantern type), with bounded `l1`.
- **Status.** OPEN.

### 2026-09-20, swarm-0917-w20-w20-deligne-follow (host-geometry): theta balance law; mass-10 certificates are transversals; none below Gamma_U, so the positive-floor route to 1/30 is dead

- **Result.** See `mod-s2-torelli-relations-obey-the-theta-balance-law` (ESTABLISHED through its proof
  node, unreviewed). Let `Gamma' <= Gamma(2)` have finite index. Every relation `b in W(Gamma')` puts the
  same exponent sum `aug(b)/10` over each of the ten level-two splittings (TB1).
  - Proof at `Gamma(4,8)`: wind `b` around the modular unit `theta_m/theta_(m')` on `A_2 - H_1`. Its
    zeros and poles are the Humbert fibres over `m` and `m'`.
  - Proof below: a transfer lemma carries the law to every `Gamma' <= Gamma(2)`.
  - The law is checked exactly on bases of `W(Gamma(4))` and `W(Gamma_U)`, with 0 violations.
- **Consequences for this node.**
  - Below `Gamma(2)`, `A_+ in 10 Z`. A positive relation of mass 10 is exactly a transversal: one twist
    over each splitting.
  - At `Gamma_U`, an exact meet-in-the-middle search finds none of the `5^10` transversals in `W`, even
    rationally. With the census bound, `A_+(Gamma_U) = 20` exactly.
  - Pushforward along inclusions keeps positivity, mass and fibres and does not increase `l1`. So every
    finite-index `Gamma'' <= Gamma_U`, including `Gamma_Phi`, `Gamma(6)` and `Gamma(6N)`, has:
    - `A_+ >= 20`, so (RF) gives at most `1/60`;
    - every `w` with `3 not| aug` of `l1 >= 12`, so (TA3) gives at most `1/36`.
  - This proves the MILP values of the 3-Sylow census and extends them to all deeper levels.
- **Kill.** "Sharp limit from one relation per level", positive or signed, is dead on every cofinal family.
  - The invariant is the ten fibre sums.
  - Every candidate dies at "pushes forward to a transversal relation at `Gamma_U`; there is none".
  - The sharp form `d_inf = 1/30` now rests on joint certificates: (SG) of
    `mod-s2-short-generated-torelli-relations-pin-one-thirtieth`, or (TD).
  - The non-sharp form `d_inf > 0` via positive floors needs `A_+ = 10 s` with `s >= 2` bounded below
    `Gamma_U`, that is, positive relations with every fibre sum equal to `2` (or to another bounded `s` with
    `3 not| s`).
- **Also.** Relations meeting fewer than ten fibres have `aug = 0` (TB4). On compact curves in
  `A_2(Gamma(4,8))`, `deg lambda` is even.
### 2026-09-20, swarm-0917-w21-w21-deligne-last1 (census-computation): first 3-adic layer below Gamma(3), b_1(M_9) = 24 and the level-three relations survive at every index-three step

- **What was computed.** See `mod-s2-three-adic-first-layer-torelli-census`, established through
  `mod-s2-three-adic-first-layer-torelli-census-proof`.
  - The index-three subgroups `Gamma(9) < G_Y < Gamma(3)` are `ker tr(Y .)` for `Y != 0` in
    `sp_4(F_3)`. There are 29524 of them in 16 adjoint classes.
  - Hochschild-Serre plus property (T) of `Sp_4(Z)` gives `b_1(M_Y) = 24 + 2 a_Y`, with `a_Y <= n_Y`.
    Here `n_Y` counts the off-diagonal level-3 splittings, and it is `3, 2, 1` on three classes and 0
    on the other 13.
  - For each class, the level-three Fox complex is lifted to a free `(Z/81)[Z/3]`-complex, which is a
    local ring. It is eliminated by a sparse unit eliminator (`lelim.c`, tested against Python and
    against no elimination).
  - The transfer then pins down the 3-part of `W(G_Y)`.
- **Results.**
  - `c_m = 26` on all 16 classes, so `a_Y = 0`, `b_1(M_Y) = 24`, and by Shapiro `b_1(M_9) = 24`.
  - On the 13 classes with `n_Y = 0`, `W(G_Y) = W(Gamma(3))` exactly: rank 21, `gcd aug = 5`,
    `d = 1/15`, with the mass-5 certificate.
  - On the 3 classes with `n_Y > 0` (45 + 2 n_Y twist classes), the 3-saturation of `W(G_Y)` is the
    pull-back of `W(Gamma(3))`. So `3 not | gcd aug` and `d <= 1/15`.
- **Reading.** The transfer obstruction of this claim (only `3 W(Gamma(3)) <= W(G_Y)` is forced) does
  not fire at the first 3-adic step. The level-three relations survive unchanged, and `W(Gamma(3))/W(G_Y)`
  is 0 rather than `F_3^21`. Down to `Gamma(9)`, decay can come only from torsion characters. For
  `n_Y > 0` it can come only from prime-to-3 torsion of `H_1(M_3; Z[omega]_chi)`.
- **Where it stops.**
  - Exactness away from 3 for `n_Y > 0` is open, because Z-coefficient elimination exhausted memory.
  - `Gamma(9)` itself is the intersection of all the `G_Y`, and only its `b_1` is determined here. Its
    `W` and `d` are not.
  - The next rung is the second layer `G_Y cap G_Y'` over `(Z/3^m)[Z/3 x Z/3]`, which is still local.
  - No uniform argument is given.
- **Status.** OPEN.

### 2026-09-19, swarm-0917-w18c-w18c-deligne-follow (census-computation): first odd-index step Gamma(6), no transversal relation modulo 3, so the mass-10 certificate dies and A_+(Gamma(6)) >= 20

- **What was computed.** See `mod-s2-level-six-torelli-census-has-no-transversal` (OPEN).
  - `M'' = pi^(-1) Gamma(6)` embeds in `K2` as a point stabiliser of `Sp_4(F_3)/{+-1}`, which has
    25920 cosets. After exact unit elimination the Reidemeister–Schreier matrix has 3466 columns.
  - The rank is 3358 modulo each of eight primes, so `dim H_1(M''; F_p) = 108`.
  - There are 900 twist classes, 90 over each level-two splitting, labelled by the ordered mod-3
    splitting. The index is `720 * 51840 / (36 * 576 * 2) = 900`.
  - An exhaustive meet-in-the-middle search (`mitm.cpp`, `2 * 90^5` half-sums) runs over all `90^10`
    one-per-block choices.
- **Results.**
  - No choice sums to 0 in `H_1(M''; F_3)`. Since `W_p = W + p Z^900`, `W(Gamma(6))` has no
    transversal relation.
  - The same exhaustive search modulo 5 and modulo 7 also finds none.
  - Modulo 2 there are exactly 7626240 transversals, and every one checked fails modulo 3.
  - The linear relaxation holds, so `aug(W) = 10 Z` and `d(Gamma(6)) <= 1/30`.
  - Controls:
    - at `Gamma(4)` the same code finds 1024 transversals, all valid at every prime, including the
      known exact one;
    - a planted mod-3 transversal is recovered.
- **Reading.**
  - By (BS3), `A_+(Gamma(6)) >= 20`. Every `w in W` with `3 not| aug(w)` has `||w||_1 >= 12`.
  - The mass-10 positive certificate gives `d = 1/30` at every level computed so far (`Gamma(2)`,
    `Gamma(4)`, its index-two layer, `Gamma(4,8)`). It is absent at the first odd step.
  - So `d_inf = 1/30` cannot be proved uniformly through transversal relations, and a sparse
    certificate here needs support at least 12, where level three needs 5.
  - This does not refute `d_inf > 0`. It removes the one positive certificate that was uniform
    along the 2-adic tower.
- **Where it stops.**
  - `d(Gamma(6))` is not computed. It lies in `[?, 1/30]`, and it is at least `1/60` if a positive
    relation of augmentation 20 exists.
  - Real characters need an integral basis of `W^perp`. The rational reconstruction from two 31-bit
    primes has denominators up to 2.8e7.
  - The next tests:
    - a mod-3 search for `w >= 0` with all block sums 2, which asks whether `A_+ = 20`;
    - characters of order dividing 30030.
- **Status.** OPEN.
