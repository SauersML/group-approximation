---
rg: 2
id: shannon-window-fakes-on-klein-and-infinite-dihedral-hosts
kind: claim
title: Shannon inequalities on a configuration's own window fail to prove Rokhlin window domination in every group with two distinct involutions of even or infinite product, or an element of order 7
distinct_from:
  minimal-window-shannon-derivations-miss-rokhlin-domination: that gives exact fakes on cyclic orbits of order 3, 4 and 5; this gives exact fakes on the order-2 hosts (Z/2)^2 and D_inf and at order 7, which extends the class kill to every group whose torsion has 2-power order, except groups with exactly one involution.
  torsion-free-windows-have-minimal-shannon-certificates: that conjectures certification in torsion-free groups; this does not touch torsion-free groups, and it shows that the D_inf fake disappears in the index-2 subgroup Z.
  rokhlin-window-transport-is-dominated: that is the domination inequality itself; this kills one proof method, on configurations where the inequality is true.
artifacts:
  - research/artifacts/shannon-window-fakes-on-involution-hosts-2026-09-17.md
  - experiments/promislow-shannon-windows-2026-09-17/verify_generic.py
  - experiments/promislow-shannon-windows-2026-09-17/verify_all.sh
  - experiments/promislow-shannon-windows-2026-09-17/verify_log.txt
  - experiments/promislow-shannon-windows-2026-09-17/torsion2_scan.py
---
**OPEN.** A route is drafted (`minimal-window-shannon-fakes-on-involution-hosts-exact-check`) but the referee panel refuted the node as stated; see Attempts.

**Setup.** This uses the minimal-window Shannon method of
`minimal-window-shannon-derivations-miss-rokhlin-domination` and its LP, Section 2 of
`research/artifacts/shannon-window-certificates-2026-09-17.md`:
- the premises are polymatroid (P), independent unit `x` (I), `y_g = psi(x_(gE))` (D), and translation invariance inside the window (T);
- the ground set is `{x_g : g in FE ∪ {1}} ∪ {y_f : f in F}`;
- the objective is `Phi = h(y_f0) + h(x_1 y_F) - h(y_F)`.

**Claim.** An exact rational polymatroid satisfies (P), (I), (D) and (T) and has `Phi < 1` on each configuration in the table:

| host | `E` | `F` | ground set | exact `Phi` |
|---|---|---|---|---|
| `(Z/2)^2 = <a,b>` | `{1, a, b, ab}` | `{1, ab, b}` | 7 | `7/9` |
| `(Z/2)^2` | `{1, a, ab}` | `{ab, a, b}` | 7 | `11/12` |
| `D_inf = <r0, r1>`, with `r0: x -> -x`, `r1: x -> 1-x`, `t = r1 r0: x -> x+1` | `{1, r0, r1, t}` | `{r1, t^-1, 1, t}` | 12 | `7/8` |
| `Z/7 = <t>` | `{1, t, t^2, t^4}` | `{1, t^3, t^5, t^6}` | 11 | `5/6` |

So the minimal-window method fails in every group containing `(Z/2)^2`, `D_inf` or an element of order 7.

**Corollary.** Combined with the order 3, 4 and 5 fakes, the method fails in every group `G` containing
- an element whose order is divisible by 3, 4, 5 or 7; or
- two distinct involutions whose product has even or infinite order.

In particular, suppose every element of finite order in `G` has 2-power order. Then the method fails unless `G` is torsion-free or has exactly one involution.
Proof. Let `s != s'` be involutions, and let `n` be the order of `ss'`. Then `<s, s'>` is dihedral of order `2n`:
- if `n = infinity`, it is `D_inf`;
- if `n = 2`, then `s` and `s'` commute and it is `(Z/2)^2`;
- if `n` is even and `n >= 4`, it contains `r^(n/2)` with `r = ss'`. That is a central involution distinct from `s`, so it contains `(Z/2)^2`.

So whenever `n` is even or infinite, two distinct involutions give a fake. If all torsion has 2-power order, `n` cannot be odd and greater than 1, so two distinct involutions always give a fake.

**The inequality is true there.** For `(Z/2)^2` and `Z/7`, `<F F^-1>` is finite. For `D_inf`, it is amenable. So `lambda(F) = 1` and
`Phi >= log q` by `bernoulli-window-codeword-folner-ratio-bound`. The failure is a failure of the method, not a deficit.

**Why the table covers every group containing the host.** Every site of the window lies in the host subgroup `H`. So does every translation `p q^-1` between sites, and any translation carrying a nonempty subset of the window into the window is of that form. So (I), (D) and (T) are literally the same constraints in `G` as in `H`.

**What dies.** The class is the one of `minimal-window-shannon-derivations-miss-rokhlin-domination`: per-configuration derivations that use only Shannon-type inequalities on the variables of the minimal window, the premises (I), (D) and (T), and no extra codewords. Every member dies at the final nonnegative combination of elemental inequalities, because the polymatroids above satisfy every premise and violate the conclusion.
Among groups with torsion, the method can survive only in groups where:
- every element of finite order has order `m` or `2m`, with every prime factor of `m` at least 11; and
- any two distinct involutions have a product of odd order.

Examples are `Z × Z/2`, `Z/11` and `D_11`. The scans of the artifact found no fake there: 338 exhaustive and 80 random configurations in `Z × Z/2`, and 21 of 56 classes of the `Z/11` shape scan.

**Commensurability.** `D_inf` contains `Z` with index 2. The tested `Z` windows (27 exhaustive, 9 dense, `n <= 14`) all certify, while `D_inf` has the `7/8` fake. This is evidence only: that `Z` certifies every window is part of the open `torsion-free-windows-have-minimal-shannon-certificates`. What does follow is that a proof using only virtual torsion-freeness cannot work, since `D_inf` is virtually `Z` and has a fake. Non-invariance under finite-index overgroups does hold by a separate easy example: the trivial group certifies (`Phi = h(x_1 y_1) >= h(x_1) = 1`), and it has index 3 in `Z/3`, which has a `5/6` fake.

## Attempts

1. **Exact rational fakes on `(Z/2)^2`, `D_inf` and `Z/7` (swarm-0917-w3-gs-pull-1, 2026-09-17).** See `research/artifacts/shannon-window-fakes-on-involution-hosts-2026-09-17.md` and route `minimal-window-shannon-fakes-on-involution-hosts-exact-check`. All three referees reran `verify_all.sh` (exit 0, ALL EXACT: 7/9, 11/12, 7/8, 5/6, 1264/1469) and accepted the table, the reduction to the host subgroup, the dihedral case split and the corollary. Lenses 2 and 3 refuted the node as stated (lens 1 survived with the same defects noted), so it is recorded as an attempt, not established. Referee reasons:
   - the Commensurability paragraph asserted that certifiability is not invariant under finite-index overgroups on the grounds that `Z` certifies; only finitely many `Z` windows were tested and full `Z` certification is the open `torsion-free-windows-have-minimal-shannon-certificates` (now downgraded above to evidence, with the trivial-group-in-`Z/3` repair);
   - the sentence "when all torsion has 2-power order there is no `Z/4`" was false (reworded above; the conclusion still follows from the even `n >= 4` case);
   - the random `Z × Z/2` count was 59 but `rs_zz2.txt` has 80 (corrected above).
   *Pending re-referee.*
