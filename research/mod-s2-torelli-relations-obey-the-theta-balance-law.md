---
rg: 2
id: mod-s2-torelli-relations-obey-the-theta-balance-law
kind: claim
title: Below Gamma(2) every Torelli relation puts the same exponent sum aug/10 over each of the ten level-two splittings (the ratios of even theta constants are modular units whose zeros are the Humbert fibres), so mass-10 positive relations are exactly transversals; none exists at or below the 3-Sylow level Gamma_U, so there A_+ >= 20, every relation with 3 not| aug has l1 >= 12, and no single relation certifies the sharp census limit 1/30
distinct_from:
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that computes W(Gamma(4)) and finds 1024 transversal generators; this proves for every finite-index Gamma' <= Gamma(2), at every depth, that each relation has equal fibre sums, so every mass-10 positive relation is transversal and every relation meeting fewer than ten fibres has augmentation 0.
  mod-s2-torelli-characters-have-a-metaplectic-maslov-line: that proves F(K cap [H,H]) = 5 m Z with m in {1,2}; this is nine further integral linear constraints on all of W (fibre by fibre), and its sum gives aug(W) in 10Z below Gamma(2) directly.
  mod-s2-holomorphic-torelli-certificates-have-unbounded-mass: that bounds the mass of holomorphic curve certificates through chi_10 = 5 lambda; this uses the ten square roots theta_m of chi_10 separately, applies to every relation (not only holomorphic ones), and gives structure rather than a mass bound.
  mod-s2-torelli-positive-relations-have-bounded-mass: that asks for sup A_+ < infinity; this proves A_+(Gamma') in 10Z below Gamma(2) and A_+ >= 20 below Gamma_U, so its constant K is at least 20, and leaves finiteness open.
  mod-s2-three-sylow-torelli-census: that proves A_+ <= 20 at five 3-Sylow levels and reports A_+ = 20 and min l1 = 12 as uncertified MILP values there; this proves A_+ >= 20 and l1 >= 12 exactly at Gamma_U and at every finite-index subgroup of it, including Gamma(6N).
  mod-s2-short-generated-torelli-relations-pin-one-thirtieth: that gives a sufficient condition (SG) for d = 1/30 using signed short generators; this shows that below Gamma_U the positive-relation floor cannot replace it.
  mod-s2-reducible-twist-relations-have-mass-divisible-by-fifteen: that kills relations with T-flexible monodromy through F in 15Z; this kills relations supported over fewer than ten level-two splittings through aug = 0, whatever their monodromy.
artifacts:
  - experiments/mod-s2-theta-balance-2026-09-17/balance.py
  - experiments/mod-s2-theta-balance-2026-09-17/balance-gamma4.json
  - experiments/mod-s2-theta-balance-2026-09-17/balance-U.json
  - experiments/mod-s2-theta-balance-2026-09-17/transversal.py
  - experiments/mod-s2-theta-balance-2026-09-17/transversal-gamma4.json
  - experiments/mod-s2-theta-balance-2026-09-17/transversal-U.json
  - experiments/mod-s2-theta-balance-2026-09-17/theta_check.py
  - experiments/mod-s2-theta-balance-2026-09-17/theta-check.json
---

**ESTABLISHED** through `mod-s2-torelli-relations-obey-the-theta-balance-law-proof`. Unreviewed. The
inputs are Igusa's theta facts and Mess's description of Torelli space (the same trust as the Remark of
`mod-s2-holomorphic-torelli-certificates-have-unbounded-mass`). The conclusion is checked exactly at
`Gamma(4)` (`balance-gamma4.json`) and at `Gamma_U` (`balance-U.json`). (TB3) additionally rests on the
exact finite search `transversal-U.json` and on the census bound of `mod-s2-three-sylow-torelli-census`.

## Setting

Notation as in `mod-s2-induced-torelli-characters-have-positive-relation-floors`.
- `Gamma' <= Sp_4(Z)` has finite index, and `Lambda' = pi^(-1)(Gamma') <= Mod(S_2)`.
- `O = O(Gamma')` is the set of `Gamma'`-orbits of symplectic splittings.
- `B(Gamma') <= Z^O` is the lattice of relations: `b` with `sum_o b_o [t_o] = 0` in `H_1(Lambda'; Z)`.
  In the census nodes this lattice is called `W`.
- `aug(b) = sum_o b_o` is the mass (`chi` or `F` in other nodes).
- A **level-two splitting** is one of the ten splittings `F_2^4 = P (+) P^perp` into nondegenerate planes.
- For `Gamma' <= Gamma(2)`, each orbit `o` lies over a single level-two splitting `m(o)`. For
  `m = 1, ..., 10`, the **fibre sum** is `s_m(b) = sum_(o : m(o) = m) b_o`.
- A **transversal** is a 0/1 vector with exactly one nonzero entry over each level-two splitting.

## Statement

**(TB1) Balance law.** Let `Gamma' <= Gamma(2)` have finite index. Every `b in B(Gamma')` satisfies

    s_1(b) = s_2(b) = ... = s_10(b) = aug(b)/10 ,

exactly over `Z`. In particular `aug(B(Gamma')) <= 10 Z`.

**(TB2) Positive relations.** Let `Gamma' <= Gamma(2)`. Every positive relation `b >= 0` with
`3 not| aug(b)` has the following properties:
- `aug(b) = 10 s`, with `s >= 1` and `3 not| s`;
- `b` puts exponent sum exactly `s` over every one of the ten level-two splittings.

Hence `A_+(Gamma') in 10 Z` and `A_+(Gamma') >= 10`. Moreover, `A_+(Gamma') = 10` holds iff some
transversal lies in `B(Gamma')`.

**(TB3) Class kill: the positive-floor route to the sharp limit is dead.** Let `U` be a 3-Sylow
subgroup of `Sp_4(F_3)` and let `Gamma_U = { A : A = I mod 2, A mod 3 in U }`, as in
`mod-s2-three-sylow-torelli-census`. Then:
- `A_+(Gamma_U) = 20` exactly. The lower bound is the exact search `transversal-U.json`: none of the
  `5^10 = 9,765,625` transversals lies in `W(Gamma_U)`, so by (TB2) `A_+ >= 20`. The upper bound is the
  census bound `A_+ <= 20` of `mod-s2-three-sylow-torelli-census`.
- `A_+(Gamma'') >= 20` for every finite-index `Gamma'' <= Gamma_U`, for example `Gamma(6N)`
  (**pushforward**). The inclusion `Lambda'' -> Lambda_U` sends each separating twist to itself, so
  `Z^(O'') -> Z^(O_U)` maps `B(Gamma'')` into `B(Gamma_U)`. This map keeps `b >= 0`, `aug(b)` and the
  level-two fibre of each class. A positive mass-10 relation below would therefore push forward to a
  transversal in `W(Gamma_U)`.
- In any cofinal family of finite-index subgroups, the members contained in `Gamma_U` form a cofinal
  subfamily. At those members, the floor (RF) `d >= 1/(3 A_+)` of
  `mod-s2-induced-torelli-characters-have-positive-relation-floors` gives at most `1/60`, not `1/30`.
- **Signed single relations fail too.** For every finite-index `Gamma'' <= Gamma_U` and every
  `w in W(Gamma'')` with `3 not| aug(w)`, `||w||_1 >= 12`. So the single-relation certificate (TA3) of
  `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit` gives at most `1/36` there.
  - By (TB1), `aug(w) = 10 s` with `3 not| s`. If `|s| >= 2`, then `||w||_1 >= |aug(w)| >= 20`.
  - If `s = +-1`, push forward to `w' in W(Gamma_U)`. Then `||w'||_1 <= ||w||_1`, and every fibre sum of
    `w'` is `s`. So `||w'||_1 >= 10`, with equality iff each fibre carries one entry `s` and nothing
    else, that is iff `s w'` is a transversal. There is none.
  - Also `||w'||_1 = aug(w') = 0 mod 2`, so `||w'||_1 >= 12`.

  This proves the MILP value 12 of `mod-s2-three-sylow-torelli-census` at `Gamma_U` (its explicit
  relation of `l1 = 12` gives equality). It also extends the bound to `Gamma_Phi`, `Gamma(6)`, and every
  level below them, where no census exists.

So no single relation, positive or signed, certifies the sharp form `d_inf = 1/30` of
`mod-s2-torelli-abelian-census-limit-is-positive` at deep level. The sharp form needs joint control of
several relations: (TD), or the short-generator condition (SG) of
`mod-s2-short-generated-torelli-relations-pin-one-thirtieth`. The constant `K` of
`mod-s2-torelli-positive-relations-have-bounded-mass` is at least 20.

The invariant is the ten fibre sums `s_m`. Every single-relation certificate of value `1/30` dies at the
step "it pushes forward to a transversal relation at `Gamma_U`, and there is none". This covers positive
relations of mass 10 and signed relations of `l1 = 10`.

**(TB4) Class kill: relations over fewer than ten splittings.** Let `b in B(Gamma')` with
`Gamma' <= Gamma(2)`, and suppose some fibre sum `s_m(b)` vanishes. This holds, for example, when `b` is
supported over at most nine level-two splittings. Then `aug(b) = 0`, so `b` is useless for (RF) and for
the mass clause of the bounded-mass node. The following candidate certificates die this way:
- relations living in the stabilizer of a level-two splitting;
- relations obtained by lifting any relation of a proper sub-configuration of splittings;
- local relations of any size.

  The invariant is the theta winding numbers `w_(m,m')(b) = s_m(b) - s_(m')(b)` (nine independent
  ones), the windings of `b` around the modular units `theta_m / theta_(m')`. Every such candidate
  dies at the step "`s_m(b) = 0` for one `m`, hence for all `m`".

**(TB5) Where the balance law sits in `H_1`.** Take `Gamma' <= Gamma(4,8)`, so that `A_2(Gamma')` is a
manifold, and let `X = A_2(Gamma')`. The nine real characters of `Lambda' = pi_1(X - H_1)` defined by
`d arg(theta_m / theta_(m'))` are exactly the annihilator of the balance lattice
`Bal = { b : s_1(b) = ... = s_10(b) }` of corank 9. So (TB1) is the statement `B <= Bal`. At `Gamma(4)`,
where only the squares `(theta_m/theta_(m'))^2` are invariant, the computation gives the following:
- rank `W = 106`, while rank `Bal = 160 - 9 = 151`;
- so 45 of the `b_1 = 54` characters are *not* theta windings;
- the other 9 are.

## Computation

`balance.py gamma4` recomputes `W(Gamma(4))` in the `Pbar = PMod(S_(0,6))` model of
`mod-s2-three-sylow-torelli-census`, with twist vectors indexed by (coset, level-two twist). It checks
(TB1) on a `Z`-basis of `W`. By (W) of `mod-s2-igusa-torelli-census-is-one-thirtieth`,
`W(Gamma(4,8)) = W(Gamma(4))`. The results (`balance-gamma4.json`) are:
- 512 cosets and 160 classes, with 16 over each level-two splitting;
- every class lies over one splitting;
- `W` has rank 106, `gcd aug = 10`, `H_1 = Z^54`, and `d = 1/30`;
- **0 violations** of (TB1) among the 106 basis rows.

`balance.py U` does the same at `Gamma_U`. This level lies in `Gamma(2)` but not in `Gamma(4,8)`, so it
tests the transfer step of the proof. The results (`balance-U.json`) are:
- 320 cosets in the `Pbar` model and 50 classes, with 5 over each level-two splitting;
- `W` has rank 34, `gcd aug = 10`, `H_1 = Z^16 + (Z/3)^5`, and `d = 1/30`;
- **0 violations** of (TB1) among the 34 basis rows.

`transversal.py` decides exactly whether some transversal lies in `W`. It reads an additive invariant
`Z^O -> Z^O / W` off a Smith decomposition of the basis of `W` (sympy, exact), then runs meet in the
middle over fibres 1-5 and 6-10. The results are:
- at `Gamma(4)`, 1024 transversals lie in `W`, which matches (G4) (`transversal-gamma4.json`);
- at `Gamma_U`, **0** of the `9,765,625` transversals lie in `W` (`transversal-U.json`).

A separate rational check was run from a scratch script, using the 16 integral kernel vectors of `W`.
It finds that no transversal lies even in `W (x) Q`. So the obstruction at `Gamma_U` is not torsion. It
is seen by real characters of `H_1(Lambda_U)`, which has rank `50 - 34 = 16`. The 9 balance characters
of (TB5) vanish on every transversal, so it is seen by the other 7 real characters.

`theta_check.py` checks numerically (`theta-check.json`) the two theta inputs of the proof:
- the ten ratios `theta_m/theta_(m_1)` are invariant, to `1e-15`, under four generators of `Gamma(4,8)`;
- they are not invariant under an element of `Gamma(4) - Gamma(4,8)`, which gives a sign;
- on the diagonal exactly `theta_[11;11]` vanishes, and it has a simple zero in `z`.

## What this changes

- **The level-four transversal generators are forced.** The 1024 transversal relations of
  `mod-s2-gamma4-torelli-census-is-one-thirtieth` (G4), and the transversal certificates surviving into
  the index-two layers (`mod-s2-gamma4-index-two-torelli-census`), are not a numerical accident. By
  (TB2), any certificate of mass 10 at any level below `Gamma(2)` must be transversal.
- **The sharp census limit cannot come from positive floors** (TB3). Before this node, one way to prove
  `d_inf = 1/30` was to find, at every deep level, ten separating twists over the ten splittings with
  trivial product in `H_1`. That route is false already at `Gamma_U`, and so at every level below it.
  The sharp form now rests on signed certificates, (TD) or (SG).
- **The bounded-mass problem below `Gamma_U` starts at mass 20.** `sup A_+ < infinity` asks for positive
  relations whose exponent sum `s` is the same over every splitting, with `3 not| s` and `s` bounded.
  Below `Gamma_U` one needs `s >= 2`, and the first open case is `s = 2`.
- **Local and partial candidates are dead** (TB4). This includes everything supported in the stabilizer
  of a level-two splitting. Combined with `mod-s2-reducible-twist-relations-have-mass-divisible-by-fifteen`,
  a useful relation must meet all ten level-two fibres *and* have non-T-flexible monodromy.
- **The holomorphic picture refines.** Let `C` be a compact curve in `A_2(Gamma')` with
  `Gamma' <= Gamma(4,8)` and `C` not inside `H_1`. The meromorphic function `theta_m/theta_(m')` has degree
  0 on `C`, so `C . D_m = C . D_(m')`, where `D_m` is the Humbert fibre over `m`.
  - With (H1) of the holomorphic node, `C . D_m = deg(lambda|C)/2` for each `m`. So `deg(lambda|C)` is
    even at these levels.
  - A mass-10 holomorphic certificate would have `deg lambda = 2` and meet each fibre once. By (H3), none
    exists at deep level.

## What is left

- **(Open, mass 20.)** Is `A_+ = 20` along a cofinal family? This asks for relations with fibre sums
  all equal to 2, meaning two twists over each splitting. By pushforward, `A_+` can only grow down a
  chain. So the question is whether it stays at 20 below `Gamma_U`, for example at the maximal subgroups
  `max0, max1, max2` of `mod-s2-three-sylow-torelli-census`. The transversal search does not apply
  there; a search over fibre sums 2 does.
- **(Open, 2-adic.)** Does `W(Gamma(2^k))` contain a transversal for every `k`? The answer is yes at
  `k = 2` (1024 of them) and at the index-two layers. At level 8 the only known positive relations have
  mass `<= 10 * 2^11` (`mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen`). The 2-adic tower
  is not cofinal, so even a yes would not give the sharp limit.
- **(Open, structural.)** Identify the 45 non-theta characters at level 4 as windings of other modular
  units, for example level-four theta constants `theta_m(2 tau)` or Klein-type forms. Each such unit
  would give further linear constraints on `B`, and hence on which transversals can be relations.
