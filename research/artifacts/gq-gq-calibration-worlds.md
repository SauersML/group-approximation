# Calibration worlds for GL_n(Q) hosts

Lane `gq-calibrator`, 2026-09-17. Target: `gl-n-q-embeds-in-fp-simple-group` (G) and Problem 2.7 (G').

Every method on the gq boards should pass these tests before anyone invests in it. For each test the
entry gives what fails, the source, which families it hits, and what a method must say to pass.

**Notation.** `H` is one of `GL_n(Q)`, `SL_n(Q)`, `Aff(Q) = Q x| Q^x`, `B_2(Q)`, `U_3(Q)` (`n >= 2`).
`D ~ (Q,+)` is its elementary unipotent (or translation) subgroup. `t = diag(2,1)` acts on `D` by
`u -> u^2`. A **host** is any group proposed to contain `H`: the final simple group, or an intermediate one.

**Status of the facts used.** Items marked *(node)* are Cairn nodes on main. Items marked *(standard)*
are textbook facts, not re-read at the source in this lane. Items marked *(source)* were read at the
source today; the quote is given.

## S. Positive sanity checks

A method should reproduce these, or say why it does not need to.

- **S1, n = 1.** `(Q,+)` and `Q^x` embed in the f.p. simple group `VA` (Belk–Hyde–Matucci; survey
  arXiv:2306.16356v3, Theorem 4.11). A method that cannot give even `(Q,+)` is suspect.
- **S2, finitely generated inputs.** Every f.g. subgroup of `GL_n(Q)` embeds in a f.p. simple group
  (Zaremsky arXiv:2405.09722, Thm 1.2; `rational-linear-groups-satisfy-boone-higman` *(node)*). A method
  that yields something weaker on f.g. inputs is suspect.

## T1. Residual finiteness (root O1, strengthened)

- **Fact A (root O1).** `D` is divisible, and a divisible group has no nontrivial finite quotient. So no
  residually finite group contains `H`.
- **Fact B, a second and independent reason** *(standard: for a field with `|K| > 3`, `SL_2(K)` is perfect
  and `PSL_2(K)` is simple)*. If `K` is infinite, a finite-index normal subgroup `N` of `SL_2(K)` maps onto
  the infinite simple group `PSL_2(K)`, so `N` has index at most 2, and perfection gives `N = SL_2(K)`. So
  `SL_2(K)` has no nontrivial finite quotient and no residually finite overgroup. This covers `SL_2(Q)`,
  which lies in `GL_n(Q)` and `SL_n(Q)` for `n >= 2`.
- **Consequence for the char-p transfer (`gq-countable-fields`).** Fact B holds for **every infinite
  field** `K`. So `GL_n(F_p(t))` has no residually finite overgroup either, although its unipotents are
  torsion. Passing to characteristic `p` removes divisibility (T4) and unipotent distortion (T3), not the
  residual-finiteness wall.
- **Kills, at every stage of a tower:**
  - f.g. linear groups (Mal'cev);
  - `Aut` of a locally finite rooted tree (profinite), hence all self-similar groups;
  - Zaremsky's self-similar affine hosts and the polynomial S-integer hosts of
    `char-zero-linear-groups-satisfy-boone-higman`;
  - any residually finite intermediate group.
- **Pass:** name the non-residually-finite mechanism that carries `D`.

## T2. The Z[1/m] world: what does it use that Q has?

- **Fact.** Each f.g. subgroup of `GL_n(Q)` lies in `GL_n(Z[1/m])` for some `m`, since finitely many
  matrix entries have finitely many denominators. So `GL_n(Q) = U_m GL_n(Z[1/m!])`, and an argument that
  handles each f.g. subgroup separately proves only S2.
- **What Q has that every `Z[1/m]` lacks:**
  - (a) divisibility by every prime (`Z[1/m]` is divisible only by the primes dividing `m`);
  - (b) `D` is not finitely generated;
  - (c) `GL_n(Q)` is not residually finite (T1), while `GL_n(Z[1/m])` is;
  - (d) `Q^x = {±1} x (free abelian of infinite rank)`: infinitely many independent scalings of `D`;
  - (e) `PSL_2(Q)` is simple, while `GL_n(Z[1/m])` has congruence quotients.
- **Pass:** point to the step that uses one of (a)–(e). Otherwise exhibit **one** f.p. host `S`, not
  depending on `m`, with embeddings of `GL_n(Z[1/m!])` that are compatible along the chain. A family of
  hosts `S_m` is only S2 again.

## T3. Distortion (root O4)

- **Transfer upward** *(standard)*. If `a in K <= G` with `K`, `G` f.g., then `|a^N|_G <= C |a^N|_K`.
  So distortion in a f.g. subgroup of `H` forces at least as much distortion in every f.g. host.
- **Required amounts:**
  - `GL_2(Q)`, `Aff(Q)` and `B_2(Q)` contain `BS(1,2) = <u, t | t u t^-1 = u^2>`, with
    `|u^(2^k)| <= 2k + 1`. So the host needs an element with `|a^N| = O(log N)`. That is **exponential**
    distortion, not just some distortion.
  - `SL_2(Q)` and `PSL_2(Q)` contain `BS(1,4)` (`diag(2,1/2)` acts on `D` by `u -> u^4`), so they need the same.
  - `U_3(Q)` contains `H_3(Z)`, whose centre has `|z^(k^2)| <= 4k`, which is quadratic.
  - For `n >= 3`, `SL_3(Z)` also has exponentially distorted unipotents *(standard,
    Lubotzky–Mozes–Raghunathan)*.
- **Hosts killed (no distorted cyclic subgroups):**
  - `VA`, by Burillo–Felipe arXiv:2605.09763v1 Thm 1 and Cor 5 (root O4). With it every subgroup:
    `V`, `T`, `F`, `T-bar`, Brin's `A`;
  - hyperbolic groups;
  - CAT(0) groups (*(standard)*: infinite-order elements are hyperbolic isometries with translation length
    bounded below).
- **Not killed, but unproved:**
  - `mV` for `m >= 2` has distortion elements, but the known one has only `|f^N| = O(log^4 N)`
    (Callard–Salo, Thm E; `brin-thompson-mv-contains-a-distortion-element` *(node)*). Polylog distortion
    does not host `BS(1,2)`.
  - Whether some `nV` contains `BS(1,2)` is **OPEN** (`bs12-embeds-in-brin-thompson-2v` *(node)*). So every
    `nV`-based route for `n = 2`, or for `Aff(Q)`, first needs that node or a replacement.
- **Pass:** exhibit an element of the host that is conjugate to its own square, or cite a subgroup that
  contains `BS(1,2)`.

## T4. Roots of every order

- **Fact.** `D` needs infinite-order elements with roots of every order: `u = b_k^k` for every `k`, with
  compatible `b_k`. In `Aff(Q)` the roots are also forced to satisfy `t b_k t^-1 = b_k^2`, because roots
  in `Q` are unique.
- **Hosts killed:**
  - `V`. Higman: an infinite-order element has only finitely many `k` with a `k`-th root (survey,
    sketch of Theorem 4.4).
  - Hyperbolic groups, whose abelian subgroups are virtually cyclic.
  - CAT(0) groups *(standard: by the Solvable Subgroup Theorem every abelian subgroup is f.g., and `Q`
    is not)*.
  - Any host in which every abelian subgroup is f.g.
- **Known mechanisms that pass:**
  - (i) a central extension of torsion. In `T-bar` the lift of an order-`q` element of `T` is a `q`-th
    root of a central translation (Belk–Hyde–Matucci).
  - (ii) Kojima–Sheng, infinitely divisible elements of `mV`, `m >= 2` (arXiv:2603.18410v3, Prop. 4.1,
    Thm. 4.2, Cor. 4.3). `gq-lit-q-embeddings` owns the extraction of their mechanism.
  - (iii) Higman-type embeddings (Mikaelian).
- **Pass:** name the mechanism, then pass T5 for it.

## T5. Central and covering lifts (`lifts-add-no-unipotent-divisibility` *(node)*, 970b120c7)

- **Fact.** Let `N <= K` be normal in `E`, with `N` `Q`-free, `K/N` central in `E/N`, and `E/K` `Q`-free.
  Then `E` contains none of the groups `H`.
- So mechanism (i) alone gives a central `Q` (as in `T-bar`), never the unipotent `D`. `t` scales `D`, so
  `D` cannot hide in a central layer.
- **Kills:**
  - lifting a `Q`-free circle group to `R` (the `T-bar` pattern), for `n = 2`;
  - `R^n -> T^n` covering lifts with `Q`-free base action (`gq-tbar-lift-n`, `gq-pp-lift`).
- **Pass:** a non-central layer that carries `D`, or a quotient that already contains `Q`. The second is
  circular unless that quotient is simpler.

## T6. Piecewise hosts: identity principle and derivatives

- **(a) Germs** (`germ-extensions-omit-standard-gl-n-q` *(node)*, 4a58a2b5b). Let `L` have the identity
  principle, for example:
  - `PGL_n` on projective space;
  - affine groups over `R`, `Q_p`, or the finite adeles `A_f`.

  Suppose the host agrees locally, off a closed nowhere dense set, with a f.g. group of finitely
  piecewise-`L` maps. Then it meets `L` only in a **f.g.** subgroup of `L`, so it never contains `H` in its
  standard action.
- **(b) Derivatives** (`fg-piecewise-linear-hosts-omit-natural-gl-n-q` *(node)*, e0cfca2b7). If each
  generator has finitely many linear parts or Möbius pieces, all derivatives have entries in one f.g.
  commutative ring `R`, and `R` does not contain `Q`. So `D` and `SL_n(Q)` have trivial derivative at every
  fixed point. `T-bar`'s `Q` is fixed-point-free, so it passes.
- **Kills the natural action** in:
  - finite germ extensions and towers of them;
  - Scott and Röver–Nekrashevych-type affine models;
  - adelic and solenoid V-like models;
  - piecewise-projective `PSL_2(Q)` and `PGL_n(Q)` hosts.
- **(c) Circle groups and their lifts** (`pp-circle-divisible-subgroups-act-freely` and
  `pp-circle-and-lift-hosts-miss-gl-n-q` *(node)*, d65ff92ff). In a f.g. finitely piecewise-`Λ` circle group,
  with `Λ <= PSL_2(R)` satisfying their hypothesis (D), and in its lift to `R`:
  - a divisible abelian `D` acts freely;
  - rotation or translation number is injective on `D`, so `N(D) = C(D)`.

  So no element scales `D`. That excludes `Aff(Q)`, `SL_2(Q)` and `GL_2(Q)` even in nonstandard
  position, because the proof uses no natural action. Calibration check of Step 1 by this lane: correct.
  `Aff_+(Q) <= Homeo_+(S^1)` is not a counterexample, because it has infinitely many pieces.
- **Hits lanes:** `gq-germ-design`, `gq-solenoid`, `gq-adelic`, `gq-deep-adelic-1`, `gq-tbar-lift-n`,
  `gq-pp-*`, `gq-scott-union`, `gq-rn-varying-degree`.
- **Pass:** say which elements carry `D` non-standardly (not as elements of `L`, and fixed-point-free), or
  why the base's piece group is not f.g. In the second case, say where finite presentation comes from.

## T7. Property (T) and FW for n >= 3 (root O2)

- **Fact** *(standard)*. `SL_3(Z) <= GL_n(Q)`, `n >= 3`, is infinite with property (T). So it has FW,
  meaning every action on a CAT(0) cube complex has a fixed point (Niblo–Reeves), and FA.
- **Kills:**
  - every a-T-menable host (`V`, `T`, `F` by Farley), and every host acting properly on a CAT(0) cube
    complex;
  - any host whose vertex stabilizers, on some cube complex, are built from such groups. This is the
    Cornulier argument that kills `VA` (survey Remark 4.12).
- **Not killed:** `mV`, `m >= 2`. Whether some `mV` contains an infinite Kazhdan group is OPEN
  (`some-brin-thompson-group-has-an-infinite-kazhdan-subgroup` *(node)*). `mV` does not act properly on a
  CAT(0) cube complex (Callard–Salo Cor. 1.2), so Farley's argument is gone there.
- **Char-p world.** `SL_3(F_q[t])` also has (T). It is a lattice in `SL_3(F_q((1/t)))` *(standard)*. So
  T7 survives the transfer to characteristic `p`, like T1.
- **Pass, for n >= 3:** name the Kazhdan-compatible part of the host (a vertex stabilizer, or a
  non-cubical piece) that holds `SL_3(Z)`.

## T8. One-manifold hosts (Witte; `gl-n-q-hosts-cannot-act-on-one-manifolds` *(node)*, 5a140f21e)

- **Source.** Witte, *Arithmetic groups of higher Q-rank cannot act on 1-manifolds*, Proc. AMS 122
  (1994) 333–340, as stated by Parwani, arXiv:math/0504189, Theorem 1.2: "If Γ is a subgroup of finite
  index in SL(n,ℤ) with n≥3, then every continuous action of Γ on the circle factors through a finite
  group action."
- **Consequence.** For `n >= 3`, `GL_n(Q)` has no faithful action by homeomorphisms on `S^1` or on `R`,
  since an action on `R` extends to `R ∪ {∞}`. So it is not left-orderable and lies in no left-orderable
  group.
- **Kills, for n >= 3:** every host inside `Homeo(S^1)`, `Homeo(R)` or `Homeo([0,1])`. That includes `T`,
  `T-bar`, `F`, piecewise-projective circle and line groups, their lifts, and every left-orderable host.
- **n = 2.** Line and interval hosts are killed by torsion: `SL_2(Q)` has elements of order 3 and 4,
  and `Homeo(R)` has no torsion beyond order 2. Circle hosts are not killed by T8, since `PGL_2(Q)` acts on
  `RP^1`, but for finitely piecewise projective circle groups T6(c) kills them. Combine with T5 (lifts),
  T6 (pieces) and M3
  (`fg-simple-projective-interval-groups-are-trivial` *(node)*: f.g. simple piecewise-projective
  interval groups are trivial).
- `gq-pp-higher` works on `RP^(n-1)` and is not affected.

## T9. Cube complexes see no divisible element

- **Fact** *(standard; Haglund, "Isometries of CAT(0) cube complexes are semi-simple", arXiv:0705.3386;
  not re-read here)*. On a **finite-dimensional** CAT(0) cube complex, after cubical subdivision, every
  automorphism either fixes a vertex or has a combinatorial axis with positive integer translation length.
- A `k`-th power has `k` times the translation length. So an element with roots of every order acts
  elliptically. Every element of `D` is elliptic in every such action, and hyperplane-based arguments see
  no part of `D`.
- **Consequence.** In a host built on a finite-dimensional cube complex or a tree, `D` must live in the
  elliptic part, meaning vertex stabilizers or the stabilizer of an end. On a tree, a countable group all
  of whose elements are elliptic fixes a vertex or an end *(standard)*.
- So the divisibility has to be produced inside the stabilizers, and the method must say how.
- **Calibration for** `gq-germ-necessary`, `gq-heretic`, and every host that is an amalgam or HNN
  extension.

## T10. Rings (cone map M1, M6, M7, M8)

From `research/artifacts/gq-gq-map-cone.md` §1:
- **M6.** A f.g. commutative ring has finite residue fields (Nullstellensatz), so it contains no `Q`.
  Every coefficient ring that contains `Q` is noncommutative, or not f.g. T6(b) is the dynamical version:
  derivative rings are f.g. and commutative.
- **M1** (`char-zero-algebra-unit-hosts-exclude-unipotents` *(node)*). Unit hosts over characteristic-0
  rings of bounded divisibility contain no unipotents.
- **M7.** `ring-simple-envelope-characteristic-obstruction` *(node)*: a unital ring embeds in a simple
  unital ring iff it has prime characteristic or torsion-free additive group.
- **M8** (`rank-four-elementary-center-obstructs-simplicity` *(node)*). `EL_4(R)` is not simple when
  `2 != 0` in `R`. Use `EL_n/Z`, or rank 3.
- **Pass for a ring lane:**
  - name the noncommutative f.g. (or f.p.) ring `R ⊇ Q` and say where its divisibility comes from;
  - say why its unit or elementary group is f.p.;
  - give the source of simplicity, modulo centre.
- **Char-p warning.** Rings over `F_p` pass M6 trivially, but T1 (Fact B) and T7 still apply.

## T11. Actions and stabilizers (type (A), cone map M2, M5)

- `GL_n(Q)` is not f.g., so any type (A) actor containing it is a strictly bigger f.p. group `Γ`. Only
  the stabilizers **in `Γ`** must be f.g.; those of `GL_n(Q)` need not be. Equivalences:
  `gl-n-q-in-permutational-boone-higman-class` *(node)*, 7ee358237.
- The 2-transitive action on `P^(n-1)(Q)` has point stabilizer the parabolic `P(Q)`, which is not f.g.
  An extension to `Γ` must make the stabilizer f.g. by adding elements, not by shrinking.
- **M2** (`nv-point-germ-groups-embed-in-zn-by-slope` *(node)*). Point germ groups of subgroups of `nV`
  are free abelian of rank `<= n`. This forbids realizing a natural action with nonabelian germs inside
  `nV`, for example on `P^(n-1)(Q_p)`.
- **M5** (`abstract-btb-simple-quotient-fp-gate` *(node)*). A non-faithful action does not remove the need
  for a f.p. faithful image.

## T12. Finite presentation against divisibility

- `D` is not f.g. In a f.p. host `S`, `D` is the increasing union of `<b_k>`, with `b_(k-1) = b_k^k`
  (take `b_k` to be `u/k!`). Finitely many relators must imply all of these root relations, and in
  `Aff(Q)` also `t b_k t^-1 = b_k^2`.
- **Test:**
  - exhibit the finite data (elements and relations) of which every `b_k` is a word, uniformly in `k`,
    for example a recursion `b_(k+1) = w(b_k, s_1, ..., s_r)`;
  - show the root relations follow from the finite relators.
- In `T-bar` the uniformity comes from the finitely many generators of `T`, which produce torsion of every
  order.
- A method with an ad hoc `b_k` for each `k` is a Higman embedding (G' at best, Mikaelian's route), not a
  natural host.

## Matrix: lane family × test (✗ kills the naive form; ! must be addressed; · no bite)

| Family (roster) | T1 | T2 | T3 | T4 | T5 | T6 | T7 (n≥3) | T8 (n≥3) | T9 | T10 | T11 | T12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A: VA / finite germ extensions | · | ! | ✗ VA itself | ! | ! | ✗ natural action | ✗ VA | · | ! | · | · | ! |
| B: type (A), twisted Brin–Thompson, `nV` | · | ! | ! BS(1,2) in `nV` open | · Kojima–Sheng | · | ! | ! Kazhdan in `mV` open | · | · | · | ! M2, M5 | ! |
| C: piecewise projective | · | ! | ! | ! | ✗ lifts | ✗ natural action | · | ✗ 1-manifold | · | · | · | ! |
| D: rings, Leavitt, Steinberg | ! | ! | · | ! | · | · | · | · | · | ✗ M6/M1 naive | · | ! |
| E: unions, Scott/RN, adelic | ✗ self-similar coefficient group | ✗ naive union | ! | ! | · | ✗ natural action | · | · | ! | · | · | ! |
| F: stepping stones | ! | ! | ! | ! | ! | ! | n/a | n/a | ! | ! | ! | ! |
| char-p transfer | ✗ Fact B | ! | · | · | · | ! | ✗ SL_3(F_q[t]) | · | · | · | · | · |

Board-by-board verdicts go to lane owners by SendMessage and are listed in `$GQ/board/gq-calibrator.md`.
They are added to this file only once they stabilize.
