---
rg: 2
id: free-subgroup-rounding-is-universal-at-bounded-exponent
kind: claim
title: For groups of exponent m, SDP value 1-eps of a symmetric Galois game gives a subgroup acting freely on G/K with mu-mass 1 - C(m) eps log k
refuted_by:
  - free-subgroup-rounding-fails-for-non-normal-fibres
distinct_from:
  galois-games-round-through-free-subgroups: that proves free-subgroup rounding and the kernel version with a dimension-weighted cost; this asks whether the cost can always be made dimension-free at bounded exponent.
---

**REFUTED as stated (2026-09-13), for arbitrary `K`.**
`free-subgroup-rounding-fails-for-non-normal-fibres` gives `G = F_2 wr F_2^n`
(exponent `4`), `K = <e_0>` (`k = 2`) and coordinate noise `mu_delta`. Then
`SDP >= 1 - delta` and `val >= 1 - delta`, but every subgroup acting freely on
`G/K` has `mu(G \ H) >= (N - 1) delta` when `delta = N^-2`. The failure is in
freeness, not in the value: a permutable subgroup still rounds.

**The sharper form for normal `K` is true.**
`normal-fibre-galois-games-round-linearly-over-m-groups`: if `K` is normal and
the irreducibles carrying the certificate are monomial (every nilpotent group,
in particular every `p`-group), some `L` with `L cap K = {e}` has
`mu(G \ L) <= 3 eps log_q k/(1 - cos(2 pi/m))`. That is the abelian constant,
with no dimension factor. Large irreducibles of `p`-groups are no obstruction.
`normal-fibre-galois-games-round-linearly-over-all-groups` removes the monomial
hypothesis using `primitive-projective-representations-have-a-trace-gap`. The
constant becomes `3/min(1 - cos(2 pi/m), 1 - gamma(G))`, where
`gamma(G) = 2^(-1/2)` for solvable `G`, and in general `gamma(G) < 1` is
uniform in `m` by CFSG. For arbitrary `K`, free rounding costs exactly the extra
factor `[G : N_G(K)]` (`free-rounding-pays-the-number-of-fibre-conjugates`).
The value-only question for non-normal `K` is open:
`galois-games-round-linearly-for-every-fibre-at-bounded-exponent`.
Artifacts: `research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md` and
`research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md`.

The original statement and attempts are kept below as history.

**Original (OPEN until 2026-09-13).** Is there `C(m)` such that for every finite group `G` of exponent `m`,
every `K <= G`, and every symmetric conjugation-invariant `mu`,
`SDP Gal(G,K,mu) >= 1 - eps` implies a subgroup `H` acting freely on `G/K`
with `mu(G \ H) <= C(m) eps log k`?

A yes would mean symmetric quotient gap constructions over bounded-exponent
groups never beat the linear loss `Theta(eps log k)`. That loss is attained by
Khot--Vishnoi (`elementary-abelian-galois-games-round-with-linear-loss`), and
the constructions would then separate SDP from integral value only in the
regime `eps log k -> infinity`. A no would be an explicit group whose
large-dimensional representations carry SDP certificates that no free subgroup
matches: a genuinely non-abelian symmetric gap phenomenon.

**Sharper form for normal `K`.** By part 5 of
`galois-games-round-through-free-subgroups`, for normal `K` it suffices to find
`L` with `L cap K = {e}` and `mu(L) >= 1 - C(m) eps log k`. This is a stability
statement about positive-definite functions: does an admissible `phi` with
`sum mu phi >= 1 - eps` force a subgroup-indicator certificate `1_L` of nearly
the same value?

## Attempts

* **Irreducible-kernel rounding**
  (`galois-games-round-through-free-subgroups`, part 3). This proves the bound
  with `C` replaced by `3 d_max/(1 - cos(2 pi/m))`. It dies on large
  irreducibles: a representation can have `lambda = 1 - O(eps)` while
  `rho(s) != I` for `mu`-almost every `s`.
* **Abelian groups.** Yes, with `C(m) = 3/(1 - cos(2 pi/m))`: all `d = 1`.
* **Exhaustive small-group replay** (`scripts/check_galois_unique_games.py`;
  artifact part 2, Section 6). On `S_3`, `S_4`, `D_8`, `Z_2^3` and `Z_6`,
  for every `K` and random class-function `mu`, it found no case with
  `max { mu(L) : L cap K = {e} } > val`, and no failure of the free-action or
  permutable-rounding bounds. This is weak evidence, since the groups are tiny.
* **Extraspecial 2-groups, `K` the centre.** Admissibility puts weight `1/2`
  on the `2^n`-dimensional irreducible, whose `lambda` is `mu(e) - mu(z)`. So
  `SDP >= 1 - eps` forces `mu(e) >= 1 - 2 eps`, and `H = {e}` works. No
  counterexample there.
* **Point stabilizers (unbounded exponent, `S_N`).** For transposition noise
  and semiregular `K`, `H = Stab(1)` is free on `G/K` with
  `mu(G \ H) = O(eps)`, although kernel rounding is vacuous. This suggests that
  the right subgroups are stabilizers of structure fixed by the certificate
  vector, not kernels. The missing piece is a stability lemma: a unit vector
  with orthonormal `K`-translates that is almost invariant under `mu` should
  yield a subgroup of large `mu`-mass meeting no conjugate of `K`. No such lemma
  is known here.
* **Inducing kernels (2026-09-13, lane `ex-ugc-rounding-pgroups`).** The
  stability lemma exists for monomial representations. If
  `rho = Ind_H theta`, then against conjugation-invariant `mu` the normalized
  character equals `sum_(h in H) mu(h) theta(h)`, the value of the single
  vector `e_H`, whose eigenvalue-one stabilizer is `ker theta`. For normal `K`
  this gives the dimension-free bound over M-groups. For non-normal `K` the
  conjugates of `ker theta` need not avoid the conjugates of `K`, and the
  wreath-product counterexample shows the loss grows with `[G : N_G(K)]`.
