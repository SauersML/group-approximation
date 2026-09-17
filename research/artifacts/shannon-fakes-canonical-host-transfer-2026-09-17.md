# Minimal-window Shannon fakes transfer to freer hosts, and every known fake forces torsion in its incidence pattern

swarm-0917-w4-pull-gs-4 (transplanter, reframing), 2026-09-17.

Scripts: `experiments/shannon-canonical-hosts-2026-09-17/` (`host_tietze.py`, `fake_hosts_scan.py`,
`random_fake_hosts.py`, `recheck_forced_torsion.py`, `base_rate.py`, `free_host_lp.py`, `onerel_hosts_z6.py`, and
the output files `scan_*.txt`, `rs_*.txt`, `recheck_all.txt`, `base_rate.txt`, `free_host_lp.txt`,
`onerel_hosts_z6.txt`).

## 0. Why this matters

`torsion-free-windows-have-minimal-shannon-certificates` (OPEN) asks for the minimal-window Shannon LP to have
value `>= 1` on every configuration in every torsion-free group. The census behind it works one host at a time.
It found exact fakes on torsion hosts and none on torsion-free hosts. The torsion fakes were treated as irrelevant
to the torsion-free question, because the same windows "read in `Z`" certify. But reading a window in `Z` changes
its incidence pattern, so that comparison says nothing about whether a fake can be moved into a torsion-free group.

This note does four things.

1. It proves a transfer lemma. Fakes move **up** along homomorphisms that are injective on the window: a freer
   host has a smaller LP value. The smallest value for an incidence pattern is attained on its canonical host.
2. That gives an exact refutation criterion. A fake anywhere, in any group, whose canonical host is torsion-free
   refutes the claim.
3. It runs the criterion on 151 fakes (Section 3): every one found in exhaustive scans of `Z/3`, `Z/4`, `Z/5`,
   `Z/6`, `(Z/2)^2` and `S_3`, part of a `Z/2 x Z/4` scan, the `D_inf` and `Z/7` fakes, and random windows in `S_4`,
   the Heisenberg group mod 3, `Z/3 x Z/3` and `Z/13`. It kills the lifting route (Section 4). In every case the incidence pattern alone forces an element
   `u` with `u^k = 1`, where `u` is a window point, a ratio of two readers or a ratio of two offsets. So `u` is
   nontrivial in **every** group that realizes the pattern, and no known fake's pattern occurs in any torsion-free
   group.
4. It proposes a strengthening. `fake-incidence-patterns-force-torsion` (OPEN) implies the torsion-free claim, is
   equivalent to a statement about canonical hosts alone, and can be tested and refuted inside finite groups.
   Section 3.4 tests it on all 1274 patterns of the exhaustive enumerations, with no counterexample. 551 patterns
   force torsion. The other 723 have free canonical hosts, and the LP on the free host is `>= 1`. By Corollary 2,
   those patterns then have no fake in **any** group.

## 1. Setup

A **configuration** in a group `G` is a pair of finite sets `E, F ⊆ G` (the code `psi` does not enter the LP). Put
`X = FE ∪ {1}`. The ground set is `V_G = {x_g : g in X} ∪ {y_f : f in F}`.

`LP_G(E,F)` is the minimum of `Phi(h) = h(y_{f_0}) + h(x_1 ∪ y_F) - h(y_F)` over polymatroids `h` on `V_G` that
satisfy the following:

- (I) `h(x_S) = |S|` for `S ⊆ X`;
- (D) `h(x_{fE} ∪ {y_f}) = h(x_{fE})` for `f in F`;
- (T) `h(S) = h(tS)` whenever `t in G` and both `S` and `tS` lie in `V_G`. Here `t` acts by `x_g -> x_{tg}` and
  `y_f -> y_{tf}`.

This is Section 2 of `research/artifacts/shannon-window-certificates-2026-09-17.md`. There, (T) is imposed for every
`t = p q^-1` with `p, q` sites. Every `t` that carries a nonempty subset of `V_G` into `V_G` has this form, so the
two definitions agree. By (T), `h(y_f) = h(y_{f'})` for all `f, f' in F`, so the choice of `f_0` does not matter.

The **incidence pattern** of `(E,F)` consists of:

- the index sets `E` and `F`;
- which pairs `(f,e)` and `(f',e')` satisfy `fe = f'e'`;
- which pairs satisfy `fe = 1`.

A **realization** of a pattern is a group `K` with injections `E -> K` and `F -> K` whose products have exactly
these coincidences and exactly these products equal to `1`.

The **canonical host** `H_P` of a pattern `P` has:

- one letter for each element of `E` and each element of `F`;
- a relator `f e (f' e')^-1` for each coincidence;
- a relator `f e` for each product equal to `1`.

Every realization `K` receives the homomorphism `H_P -> K` that is the identity on letters.

## 2. The transfer lemma

**Lemma 1 (transfer).** Let `pi : H -> G` be a homomorphism, and let `E_H, F_H ⊆ H` be finite. Suppose `pi` is
injective on `X_H = F_H E_H ∪ {1}` and on `F_H`, and that `pi(1) = 1`. Put `E = pi(E_H)` and `F = pi(F_H)`. Then

    LP_H(E_H, F_H) <= LP_G(E, F).

*Proof.*

1. **The ground sets match.** `pi` is injective on `E_H`: if `pi(e) = pi(e')` with `e != e'`, then for any `f` in
   `F_H` the distinct points `fe` and `fe'` would have the same image. So `pi` maps `X_H` bijectively onto
   `FE ∪ {1} = X_G`, and `F_H` bijectively onto `F`. The map `Pi(x_g) = x_{pi g}`, `Pi(y_f) = y_{pi f}` is
   therefore a bijection `V_H -> V_G`.
2. **Pull back.** Let `h` be feasible for `LP_G(E,F)`, and put `h_H(S) = h(Pi S)`. Relabelling by a bijection
   preserves the polymatroid axioms.
   - (I): `Pi` sends distinct `x`'s to distinct `x`'s.
   - (D): `Pi` sends the window `x_{f E_H}` of `y_f` to `x_{pi(f) E}`, which is the window of `y_{pi f}`.
   - (T): suppose `S` and `tS` both lie in `V_H`. Then `Pi(tS) = pi(t) Pi(S)` because `pi` is a homomorphism, and
     both sides lie in `V_G`. So `h_H(tS) = h(pi(t) Pi S) = h(Pi S) = h_H(S)`.
3. **The objective matches.** `Pi` maps `x_1`, `y_{F_H}` and `y_{f_0}` to `x_1`, `y_F` and `y_{pi f_0}`. So
   `Phi(h_H) = Phi(h)`.

Every feasible point for `G` therefore gives a feasible point for `H` with the same objective. `[]`

The proof is exact: a rational fake on `G` pulls back to a rational fake on `H` with the same value.

**Corollary 2 (the minimum is at the canonical host).** Let `(E,F)` be a configuration in `G` with incidence pattern
`P`. Let `E_P` and `F_P` be the letter sets in `H_P`. Then `LP_{H_P}(E_P, F_P) <= LP_K` for every realization `K` of
`P`. In particular `LP_{H_P} <= LP_G(E,F)`.

*Proof.* The letter map `H_P -> K` is a homomorphism. It is injective on letters and on `F_P E_P ∪ {1}`, because
distinct points of `P` have distinct images in the realization `K`. Apply Lemma 1. `[]`

**Corollary 3 (refutation criterion).** Suppose `LP_G(E,F) < 1` for a configuration in some group `G`, and the
canonical host of its incidence pattern is torsion-free. Then
`torsion-free-windows-have-minimal-shannon-certificates` is false.

*Proof.* `H_P` is a countable torsion-free group, and `LP_{H_P}(E_P, F_P) <= LP_G(E,F) < 1` by Corollary 2. `[]`

Corollary 3 turns every finite group into a test bed for the torsion-free claim. It also kills the "read in `Z`"
comparison: a torsion fake is relevant exactly when its *pattern* can be realized without torsion.

## 3. The census: every known fake forces torsion in its pattern

### 3.1 The certificate

Tietze moves do not change the group. Suppose that after eliminating letters, `H_P` has a relator `u^k` with
`k >= 2`, where `u` has one of these forms, up to rotation and inversion:

- (point) `u = f e` with `fe != 1` in the pattern;
- (reader ratio) `u = f f'^-1` or `f^-1 f'` with `f != f'`;
- (offset ratio) `u = e e'^-1` or `e^-1 e'` with `e != e'`.

**Lemma 4 (realization independence).** If such a certificate exists, no torsion-free group realizes `P`.

*Proof.* Let `K` realize `P`, and let `rho : H_P -> K` be the letter map. Then `rho(u)^k = 1`. In the point case
`rho(f) rho(e) != 1`, because realizations keep exactly the products equal to `1`. In the reader-ratio case
`rho(f) != rho(f')`, because realizations are injective on `F`. In the offset-ratio case `rho(e) != rho(e')`,
because `F` is nonempty and `rho(f)rho(e) != rho(f)rho(e')` for any `f`. So `rho(u)` is a nontrivial element of
finite order in `K`. `[]`

This is exact. Each certificate is a finite chain of Tietze moves on a presentation with at most `|E| + |F|` letters
and at most `|E||F|` relators, so each one can be checked by hand.

### 3.2 Worked example: the `Z/3` fake

Take `G = Z/3`, `E = {0,1,2}`, `F = {0,1}`. Here `LP = 5/6`, and the fake is exact
(`shannon-window-certificates-2026-09-17.md`, Section 3). The products `f + e` are `0,1,2` for `f = 0` and `1,2,0`
for `f = 1`. The relators of `H_P` are:

- `f0 e0` and `f1 e2`, from the products equal to `0`;
- `f0 e1 (f1 e0)^-1` and `f0 e2 (f1 e1)^-1`;
- the redundant relator `f0 e0 (f1 e2)^-1`.

The Tietze moves go as follows.

1. Eliminate `f0 = e0^-1` and `f1 = e2^-1`. The two remaining relators become `e0^-1 e1 e0^-1 e2` and
   `e0^-1 e2 e1^-1 e2`.
2. The first relator gives `e1 = e0 e2^-1 e0`.
3. Substituting into the second gives `e0^-1 e2 e0^-1 e2 e0^-1 e2 = (e0^-1 e2)^3`.

So `H_P = <e0, e2 | (e0^-1 e2)^3> = Z * Z/3`, and the certificate is the offset ratio `u = e0^-1 e2` of order `3`.
The script writes the same relator as `(e0^-1 f1^-1)^3` with `f1 = e2^-1`.

In every group where this pattern occurs, `e0^-1 e2` is a nontrivial element of order dividing 3. So the pattern
occurs in no torsion-free group.

### 3.3 The fakes

`fake_hosts_scan.py` and `random_fake_hosts.py` found the fakes. `recheck_forced_torsion.py` rebuilt each canonical
host, and the output is in `recheck_all.txt`. The Tietze elimination order is randomized on retries, and one `Z/3 x
Z/3` fake needed a retry.

| group | enumeration | fakes | certificates (kind, order) |
|---|---|---|---|
| `Z/3` | exhaustive, `\|E\| <= 3`, `\|F\| <= 3`, `n <= 10` | 3 | point 3 |
| `Z/4` | exhaustive, `\|E\| <= 4`, `\|F\| <= 3`, `n <= 10` | 20 | point 4: 11, reader 4: 8, offset 4: 1 |
| `Z/5` | exhaustive, `\|E\| <= 4`, `\|F\| <= 3`, `n <= 10` | 52 | point 5: 36, reader 5: 13, offset 5: 3 |
| `Z/6` | exhaustive, `\|E\| <= 3`, `\|F\| <= 3`, `n <= 10` | 12 | point 3: 12 |
| `(Z/2)^2` | exhaustive, `\|E\| <= 4`, `\|F\| <= 3`, `n <= 10` | 16 | point 2: 14, reader 2: 2 |
| `S_3` | exhaustive, `\|E\| <= 3`, `\|F\| <= 3`, `n <= 10` | 12 | point 3: 12 |
| `Z/2 x Z/4` | exhaustive enumeration, **stopped early** | 12 | point 4: 7, reader 4: 5 |
| `D_inf` | the known 7/8 fake | 1 | point 2 |
| `Z/7` | the known 5/6 fake | 1 | reader 7: `(f6 f5^-1)^7` |
| `S_4` | 60 random windows | 1 | point 3 |
| Heisenberg mod 3 | 60 random windows | 3 | point 3 |
| `Z/3 x Z/3` | 60 random windows | 18 | point 3: 17, offset 3: 1 |
| `Z/13` | 40 random windows | 0 | none |

**Total: 151 fakes, and all 151 have a two-letter certificate.**

The order `k` is always a divisor of the exponent of the host group. It can be smaller than the exponent: all 12
`Z/6` fakes are certified at order 3. It does not have to match the order of the element in `G`.

### 3.4 Base rate: the dichotomy is not vacuous

"Every fake forces torsion" would say little if almost every pattern in a small finite group forced torsion anyway.
`base_rate.py` classifies **every** configuration of the exhaustive enumerations, fake or not. `free_host_lp.py`
then solves the LP directly on the canonical host whenever that host is free. The outputs are `base_rate.txt`,
`free_host_lp.txt` and `onerel_hosts_z6.txt`.

| group | configurations | pattern forces torsion | free host | fakes | fakes in the forced class | min LP on free hosts |
|---|---|---|---|---|---|---|
| `Z/3` | 12 | 6 | 6 | 3 | 3 | 1 |
| `Z/4` | 67 | 33 | 34 | 20 | 20 | 1 |
| `Z/5` | 258 | 70 | 188 | 52 | 52 | 1 |
| `Z/6` | 435 | 129 | 303 + 3 | 12 | 12 | 1 |
| `(Z/2)^2` | 67 | 55 | 12 | 16 | 16 | 1 |
| `S_3` | 435 | 258 | 177 | 12 | 12 | 1 |
| **total** | **1274** | **551** | **723** | **115** | **115** | **1** |

The "+ 3" for `Z/6` counts three patterns that Tietze elimination reduces to a single relator which is not a proper
power, such as `e0^-1 e2 e0^-1 e2 e0^-1 f3^-1 e0^-1 e2 e0^-1 f3^-1`. The Nielsen moves `x = e0^-1 e2`,
`y = e0^-1 f3^-1` turn this into `<e0> * <x, y | x^2 y x y>`. With `z = xy`, the second factor is `<z>`. So the host
is free of rank 2. `onerel_hosts_z6.py` writes down the explicit isomorphism, checks the pattern, and solves the LP
there; the value is 1.

Two things follow.

1. **The fakes concentrate on the forced class.** In `Z/5`, 52 of the 70 torsion-forcing patterns are fakes, and
   none of the 188 free-host patterns is. If fakes were spread across patterns without regard to torsion, all 52
   would land in the forced class with probability about `(70/258)^52 < 10^-29`.
2. **`fake-incidence-patterns-force-torsion` holds on the whole enumeration (numerically).** Every one of the 1274
   patterns falls into exactly one of two cases:
   - it forces torsion (Lemma 4);
   - its canonical host is free and `LP_{H_P} >= 1`. By Corollary 2 the LP is then at least 1 in **every** group
     realizing the pattern, finite or infinite, with or without torsion.

   This does more than confirm the torsion-free claim on these windows. It decides these patterns in every group
   at once, including every torsion-free group in which the pattern occurs. The free-host LP values come from
   `highs-ipm` with tolerance `1e-6`; they are not rational certificates. Several of them are exactly tight at 1.

## 4. Class kill: lifting fakes into torsion-free groups

**The class.** Refute `torsion-free-windows-have-minimal-shannon-certificates` by taking a known fake in a torsion
group and moving it to a torsion-free group. Every such move must go through a homomorphism or a correspondence
that keeps the LP from rising. Members of the class include:

- lifting along a surjection `Gamma -> G` from a torsion-free group, e.g. a free group or a surface group;
- passing to a torsion-free finite-index subgroup of an extension or a crystallographic-type cover;
- moving into a torsion-free quotient such as `P/Tor_inf(P)`;
- embedding into the universal finitely presented torsion-free group of
  `higher-whitehead-universal-finitely-presented-torsion-free-group`.

**The invariant.** Take any configuration `(E', F')` in a torsion-free group `Gamma` with `LP_Gamma(E',F') < 1`,
produced from a fake `(E,F)` in `G`. Let `P'` be its incidence pattern. By Corollary 2,
`LP_{H_{P'}} <= LP_Gamma(E',F') < 1`, and `P'` is realized in the torsion-free group `Gamma`. The invariant is the
pattern, together with whether it carries a two-letter torsion certificate (Lemma 4).

**Where every member dies.** A member that transports the fake with its value intact keeps the incidence pattern
(otherwise Lemma 1 does not apply, and the value is recomputed from scratch). So `P' = P`, and `P` must be realized
in `Gamma`. For all 151 known fakes, Lemma 4 gives an element `u`:

- a window point `fe != 1`, a ratio of two readers, or a ratio of two offsets;
- with `u^k = 1` in every realization.

A torsion-free `Gamma` cannot contain it. **Every member of the class dies at the realization step, at the named
two-letter relator `u^k`.**

Any member that changes the pattern is not a transfer at all. It is a new LP computation on a new pattern. By
Corollary 2 and Section 3.4, every pattern in the exhaustive enumerations without forced torsion has host LP `>= 1`.
So such a member dies there too, at least within those windows.

The obstruction is stronger than "this fake lives on a torsion group", which was already known. It says that
**no torsion-free group contains even the coincidence pattern of any known fake**. Future searches for a refutation
must look for fakes whose patterns carry no two-letter torsion certificate. Finite groups can find such fakes,
because Corollary 3 only needs the canonical host to be torsion-free, not the group in which the fake was found.

## 5. The proposed strengthening

**`fake-incidence-patterns-force-torsion` (OPEN).** If `LP_G(E,F) < 1` for a configuration in some group `G`, then
the incidence pattern of `(E,F)` is realized in no torsion-free group.

**Proposition 5.**

(a) The strengthening implies `torsion-free-windows-have-minimal-shannon-certificates`.

(b) The strengthening is equivalent to the following statement: `LP_{H_P}(E_P, F_P) >= 1` for every pattern `P`
that is realized in some torsion-free group.

(c) The strengthening would be refuted by a single fake, in any group including a finite one, whose pattern has a
torsion-free realization.

*Proof.*

(a) A fake in a torsion-free group `G` realizes its own pattern in `G`.

(b) Suppose the strengthening holds, and `P` has a torsion-free realization `K`. If `LP_{H_P} < 1`, then `H_P` itself
carries a fake with pattern `P`. The strengthening then says `P` has no torsion-free realization, which contradicts
`K`. Conversely, suppose a fake `(E,F)` has pattern `P` and `P` has a torsion-free realization. Corollary 2 gives
`LP_{H_P} <= LP_G(E,F) < 1`, which contradicts the right-hand side.

(c) This restates (b), using Corollary 2. `[]`

**Why it is worth stating separately.** The torsion-free claim only speaks about torsion-free groups, where nobody
has found a fake, so nothing can falsify it in a small computation. The strengthening can be refuted inside finite
groups, where exhaustive exact search is cheap. Section 3.4 is the first systematic test, and the strengthening
survives it on 1274 patterns.

It also splits the torsion-free claim into two independent prerequisites.

- **(P1) pattern side.** A combinatorial statement about when a finite system of relators `f e = f' e'` and `f e = 1`
  forces torsion. It is decidable pattern by pattern in the cases above. In general it asks whether the
  two-letter certificates are complete for fakes.
- **(P2) entropy side.** `LP_{H_P} >= 1` whenever `H_P` carries no forced torsion.

(P2) is where the entropy content lies. The strengthening can fail at (P1), if some fake pattern forces torsion
without any two-letter certificate. That would not refute the torsion-free claim; it would only weaken the proposed
certificate. It can also fail at (P2), which would refute the claim itself when the host is torsion-free.

## 6. Limits

- The LP is Shannon-only on the minimal window. Nothing here concerns non-Shannon inequalities or larger windows.
- The enumerations are small: `|E| <= 4`, `|F| <= 3`, `n <= 10`, groups of order at most 8 for the exhaustive
  scans, and random windows in `S_4`, Heisenberg mod 3 and `Z/3 x Z/3`. The `Z/2 x Z/4` scan was stopped early. A
  `Z/7` scan with `|E|, |F| <= 3` produced no fake before it was stopped, and no result from it is claimed.
- Lemma 1, Corollaries 2 and 3, Lemma 4 and Proposition 5 are exact. Each certificate is an explicit Tietze
  derivation, which the script prints and which can be checked by hand. The free-host LP values in Section 3.4 are
  floating point.
- Tietze search is heuristic. When it finds no certificate, the pattern may still force torsion. This never happened
  for a fake. In the base-rate scans no pattern was left undecided: each one either received a certificate (with
  up to 50 shuffled retries) or reduced to a free host, counting the three `Z/6` one-relator hosts shown to be free
  by hand.
- The script labels the `Z/3` certificate `(e0^-1 f1^-1)^3` as a point certificate, since `f1 e0 != 1`. Section 3.2
  reads the same relator as an offset ratio, using `f1 = e2^-1`. Both readings satisfy Lemma 4.
