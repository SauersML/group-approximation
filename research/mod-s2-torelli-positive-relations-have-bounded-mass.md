---
rg: 2
id: mod-s2-torelli-positive-relations-have-bounded-mass
kind: claim
title: Every finite-index preimage of a subgroup of Sp_4(Z) kills a positive product of at most K separating twists with exponent sum prime to 3
distinct_from:
  mod-s2-induced-torelli-characters-have-positive-relation-floors: that proves the floor 1/(3 A_+) for each level and computes the base; this is the uniform bound sup A_+ < infinity, which is open.
  deligne-congruence-monomial-models-need-growing-defect: that uses transferred block cycles, whose value is divisible by 3 at q = 3; this asks for short positive relations that are not transfers.
---

**OPEN.** Notation as in `mod-s2-induced-torelli-characters-have-positive-relation-floors`. There is `K`
such that for every finite-index `Gamma' <= Sp_4(Z)` there are separating curves `s_1, ..., s_k` and
exponents `n_j >= 1` with the following properties:
- `sum_j n_j <= K` and `3 not| sum_j n_j`;
- the class of `t_(s_1)^(n_1) ... t_(s_k)^(n_k)` in `H_1(Lambda)` is trivial, where `Lambda = pi^(-1)(Gamma')`.

Equivalently, `sup_(Gamma') A_+(Gamma') < infinity`. By (Mono) it suffices to check a cofinal family,
for example the principal congruence subgroups `Gamma(N)`.

**Why it matters.** By (RF) it gives the uniform operator-norm floor `2 sin(pi/(3K))` for every
representation of `Mod(S_2)` induced from a character of a finite-index subgroup containing the Torelli
group. That is the Torelli-abelian induced class of `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`.
By (RF), `K` is at least `1/(3D)` at every level. The base forces `K >= 5`, and the level-4 census value
`1/30` reported on the live bus forces `K >= 10`.

**How it can fail.**
- *Divisibility.* For some tower, every positive relation has `3 | sum n_j`, as the transfer relations
  do when `3` divides the index.
- *Mass growth.* Positive relations prime to 3 exist, but their minimal mass grows.
- Either failure alone does not refute the gap, because (TD) allows non-positive and non-single
  certificates. The (TD) minimum can stay positive through many long relations, since the flatness
  constant grows with `r`.

## Attempts
- **2026-09-18, swarm-0917-w13-w13-deligne-break: posed.** The only positive relations constructed are
  transfers, of mass `5 [Sp_4(Z) : Gamma']`. A short positive relation must come from `H_2(Gamma')`
  classes supported near a single splitting orbit. Candidates are lifts of lantern or chain relations in
  `Gamma'`, which are not tested.
- **2026-09-19, swarm-0917-w15-w15-deligne-last1: 2-adic interval settled up to torsion exponent;
  palindrome transversals dead.** See `mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen`.
  - *Base.* `A_+(Gamma(4)) = 10` is attained by a positive relation, one twist over each level-two
    splitting.
  - *Transport.* If `b_1` does not change from `Gamma'` to `Gamma'' <= Gamma'`, then
    `ker(H_1(Lambda'') -> H_1(Lambda'))` is finite of some exponent `e`. When `3 not| e`, the `e`-th
    power of a positive relation at `Gamma'` is a positive relation at `Gamma''`.
  - *Level 8, exact over Z.* By Shapiro over `F_2^10`, `b_1(M_8) = 54` with no odd torsion, and
    `A_+(Gamma(8)) <= 10 * 2^11`.
  - *Level 16.* The same splitting over `Sym_4(Z/4)` of order `4^10`, done modulo `p` and over `F_9`,
    gives `b_1 = 54` and a kernel prime to 3 for every `Gamma(16) <= Gamma' <= Gamma(4)`. So
    `A_+ < infinity` there.
  - *First torsion.* At the Igusa level `Gamma(4,8)`, `H_1 = Z^54 (+) Z/2^k` with `1 <= k <= 4`
    (`igusa48-results.json`), so the integral census is not frozen on this interval.
  - *Where the problem now sits.*
    - On the 2-adic interval, only the growth of a 2-power exponent (mass growth) is left.
    - Divisibility can come only from odd-index steps, for example `Gamma(4) cap Gamma(3)`; that is
      the next hole.
    - By Mess, `H_1(I)` is free on the splittings, so no relation is universal. Every short positive
      relation must come from `H_2(Gamma')`.
  - *Dead: palindrome and transversal products.* Products `prod_(c in T) t_c` over transversal
    palindromic curve families were tested in `experiments/mod-s2-palindrome-transversal-relations-2026-09-17/palindrome.py`.
    There were four families (standard, random curves, repeated, nine-curve), with 200 random trials in each.
    None of these trials, and none of the controls, gives a trivial class at level 4 (`palindrome-results.json`).
- **2026-09-19, swarm-0917-w18-w18-deligne-pull (reframing): local and single-splitting candidates dead.**
  See `mod-s2-reducible-twist-relations-have-mass-divisible-by-fifteen`.
  - *Invariant.* Deligne's class restricted, with circle coefficients, to the monodromy of the relation.
    Every curve stabilizer has T-flexible image (a conjugate of `SL_2 x SL_2`, its swap extension, or a
    maximal parabolic). The commutator-lift count then forces `F in 15 Z`.
  - *Dies at.* The divisibility clause `3 not| sum n_j`. This covers lantern and chain lifts, relations in
    `Stab(s)`, and all sums of such relations.
  - *Survivors.* Relations whose letters generate non-T-flexible monodromy, and mixed-handle words whose
    individual commutators are not Torelli. The census relations (`F = 5`, `10`) are of this global kind.
- **2026-09-19, swarm-0917-w19-w19-deligne-break (host-geometry): divisibility is vacuous, and holomorphic
  certificates die.**
  - *Divisibility cannot occur.* By ST5, `3 not| g(Gamma')` at every level
    (`mod-s2-torelli-abelian-census-limit-is-positive`), so some `w in B` has `3 not| chi(w)`.
    - The transfer `5m` has every coordinate positive, since `m` is the vector of class sizes.
    - Hence `w + 15N m >= 0` for large `N`, with `chi == chi(w) mod 3`.
    - So `A_+(Gamma') < infinity` at every level. The failure mode "Divisibility" above is empty, and w15's
      "odd-index next hole" is closed a priori: only mass growth remains.
  - *Holomorphic certificates have unbounded mass.* See
    `mod-s2-holomorphic-torelli-certificates-have-unbounded-mass`.
    - A compact holomorphic curve `f` in `A_2(Gamma')` with `Gamma' <= Gamma(3n)` has mass
      `deg f^* H_1 = 5 deg f^* lambda`, using Igusa's `chi_10`.
    - That mass is at least `5 |Phi mod 3n|`, where `Phi` is the infinite level-3 monodromy.
    - There are finitely many `Phi` classes per degree, so every such certificate has mass `> 5D` once
      `n >= n_0(D)`.
    - This kills Shimura curves, complete intersections, and holomorphic separating-only genus-2 Lefschetz
      fibrations as proofs of this node.
  - *What is left.* A proof must use positive relations that are not holomorphic. Via the Maslov dictionary
    these are achiral or symplectic, non-Kahler, separating-only genus-2 Lefschetz fibrations with monodromy
    in `Lambda` and a bounded number of singular fibres.
- **2026-09-20, swarm-0917-w23-w23-deligne-pull (reframing): Lefschetz dictionary; the holomorphic
  kill covers nothing structural, and the approach is DEAD as a class kill.**
  - *Dictionary (elementary).* A positive relation of mass `A` at `Gamma'` is the same as a genus-2
    Lefschetz fibration `X -> Sigma_h` over a closed surface. It has `A` singular fibres, all with
    separating vanishing cycles, and homological monodromy in `Gamma'`.
    - A relation `t_(s_1)...t_(s_A) = prod [a_i, b_i]` with `a_i, b_i in Lambda` is exactly such a
      monodromy factorization.
    - Conversely, given a surface representation `rho : pi_1 Sigma_h -> Gamma'`, lift it to `Lambda`.
      The defect `k` lies in `K cap [Lambda, Lambda]`. Its class in `K/[Lambda, K] = Z^O` does not depend
      on the lift, and it is the step-1 map of the positive-relation floor proof. If that class is `>= 0`,
      then `k` is congruent mod `[Lambda, K]` to a positive product, and that product is in `[Lambda, Lambda]`.
    - By Gompf, `X` is symplectic.
    - So `A_+(Gamma') = 5 min { n > 0, 3 not| n }`, the minimum over separating-only fibrations with
      monodromy in `Gamma'` of the Maslov number `n = <b, rho_*[Sigma_h]>` (ML1). If Matsumoto's genus-2
      signature formula (`sigma = -(3/5) n_ns - (1/5) n_s`) holds over higher-genus bases, then the mass is
      `-5 sigma(X)`. That formula is not imported verbatim here.
  - *Consequence for the w19 kill.* Every positive relation is a symplectic separating-only fibration, so
    the class left open by `mod-s2-holomorphic-torelli-certificates-have-unbounded-mass` (not
    holomorphic) is the whole hole minus its holomorphic part. Two things follow:
    - A proof of `sup A_+ < infinity` must produce Lefschetz fibrations that cannot be realized
      algebraically, with bounded signature and monodromy in `Gamma(N)` for every `N`.
    - A disproof must be a symplectic or combinatorial argument. Siebert-Tian holomorphicity does not
      apply, because separating singular fibres are reducible and the base has genus `h >= 1`.
  - *Where it dies.* The period map `Sigma_h -> A_2(Gamma')` of a non-holomorphic fibration is only a
    continuous map. `lambda` is not positive on arbitrary classes, and nothing in the Humbert
    intersection numbers `e_o(sigma) >= 0` bounds `sum_o e_o` from below in terms of `N`. The reduction
    returns to the lattice question `d(H_2(Gamma')) cap Z^O_(>=0)`. So no new invariant appears, and the
    approach adds no kill beyond w18 (reducible support, `15 | F`), w19 (holomorphic) and w20 (theta
    balance, `A_+ >= 20` below `Gamma_U`).
  - **Status.** OPEN; approach DEAD.
