---
rg: 2
id: exact-kernel-rank-does-not-exclude-flip-violators
kind: claim
title: (SF_P) is false for every kernel-rank threshold r -- swapping n pairs of lines in each J-copy keeps the 3LIN instance regular and perfectly satisfiable and kills its exact homogeneous kernel, but Phi(v) = v stays an approximate kernel map of rank k - c dirty on a 26kn 4^(-n) mass of tuples, and Theorem O runs on the clean tuples, so the flip orientation is a violator inside P_0
distinct_from:
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that is (SF_P), stated with the exact kernel rank; this refutes it for every r in the CIRC range and names the corrected robust-rank prerequisite.
  star-list-structure-is-circular-on-decodable-yes-inputs: that proves Theorem O for exact kernel maps and refutes star lists on classes containing J-instances; this extends Theorem O to approximate kernel maps and applies it to inputs of exact kernel rank 0, which every class P_r contains.
  dkkms-list-seed-needs-lists-exponential-in-l: that builds the defect-line labelling from an exact generic kernel; this shows the exact kernel is not needed, only one that is exact on almost all tuples.
  selector-witness-hypotheses-collapse-to-selector-free-form: that reduces every per-selector witness route to (SF_P); this refutes the reduced statement as written, so the reduction must target the robust form.
artifacts:
  - experiments/ugc-kernel-swap-2026-09-17/check_swapped_j_kernel.py
---

**ESTABLISHED.** Route: `exact-kernel-rank-does-not-exclude-flip-violators-proof`.

## Setting

The notation is that of `star-list-structure-is-circular-on-decodable-yes-inputs`
(Theorem O, Proposition S, Corollary CIRC) and of
`good-dkkms-orientations-admit-short-star-lists-on-hard-inputs` ((SF_P), with
the classes `P_r` defined there by the rank of exact kernel maps).

**Approximate kernel maps.** A linear `Phi : F_2^X -> F_2^n` is a
`delta_K`-approximate kernel map if the `G_multi` mass of tuples `U` that
contain an equation `e` with `Phi(x_e) != 0` (**kernel-dirty** tuples) is at
most `delta_K`. An exact kernel map is the case `delta_K = 0`.

**Swapped J-copies.** In a J-copy `F_2^n \ 0` (one equation
`x_u + x_v + x_(u+v) = 0` per line), a **swap** takes two disjoint lines
`{a, b, a+b}` and `{c, d, c+d}` and replaces their equations by
`x_a + x_b + x_(c+d) = 0` and `x_c + x_d + x_(a+b) = 0`. A **J'-copy** is a
J-copy with `n` swaps on `2n` pairwise disjoint lines, with
`a_i + b_i + c_i + d_i = e_i` (the `i`-th unit vector). A **J'-instance** is
a disjoint union of `N >= k` J'-copies.

## Statement

**Lemma J'.** For `n >= 7`, J'-copies exist and are found greedily. A
J'-instance has these properties:
* it is regular, with every variable in exactly `2^(n-1) - 1` equations;
* all right-hand sides are `0`, so `x = 0` satisfies every equation;
* its homogeneous system has trivial kernel, so every exact kernel map has
  rank `0`, and the instance lies in `P_0`, hence in `P_r` for every `r >= 0`;
* `Phi(v) := v` on each copy kills every equation except the `2n` swapped
  ones per copy, and it is a `delta_K`-approximate kernel map with
  `delta_K <= 2k rho`, where `rho = 2n / ((2^n - 1)(2^n - 2)/6) < 13 n 4^(-n)`.

**Theorem O'.** Theorem O holds for every `delta_K`-approximate kernel map, with
`delta_K` added to the loss of both items. Item 1 becomes
`val >= v(l) - 2^(l-k) - beta_bad - delta_dirty - delta_K`. Item 2 becomes
`val <= 1/2 + D^C_L + E + delta_K`.

**Corollary R (refutation of (SF_P)).** Take the CIRC range:
* `l >= 8`;
* `2^(2-l) <= gamma' < gamma <= 0.105`;
* `L` in the Corollary DK^C budget;
* every sufficiently large `k`, with `n = k - c` as in CIRC.

Then for every `r >= 0`, (P2) fails on `P_r`. Every J'-instance with
`N >= k` copies is in `P_r`, and there are infinitely many. On each of them
the flip orientation `o*` built from `Phi(v) = v` and `x = 0` has lift value
`>= 0.605 > 1/2 + gamma`. Every lift labelling of value `>= 1/2 + gamma` has
`D^C_L > gamma - gamma'` against every list of at most `L` references. So
(SF_P) is false as stated, whatever the threshold `r(k, l, gamma')`.

The J'-copy test is a constant-size check per component, so Proposition S also
splices `o*` into every selector on J'-instances. The per-selector form over
`P_r` dies the same way.

## What this kills (impact types 3 and 4)

**Class killed.** Every closure of the constant-bias cell of H1 through a
selector-free or per-selector star-list statement restricted to a promise
class defined by exact kernel rank, or by any other invariant that changes
when `O(n)` equations per J-copy are edited. This includes (SF_P) for every
`r`, the "local-kernel version of the flip orientation" falsifier being
unnecessary.

**Invariant.** The flip mechanism uses `Phi(x_e) = 0` only for the equations of
the tuple at hand:
* LS Lemma 3(a), class invariance at the member's own `H_U`;
* the growth set `W_U ⊇ L' + H_U`;
* LS Lemma 7, through `H' ⊆ H_U`.

So the operative invariant is the **robust kernel rank**: the largest `n` such
that some `Phi` of rank `n` is exact on all but a `delta_K << gamma'` mass of
tuples. Exact kernel rank is not stable under editing a vanishing fraction of
the equations.

**Where every member dies.** Membership in `P_r` is decided by the exact
kernel. The edit that sends a J-instance to a J'-instance moves exact rank from
`N n` to `0`. It changes the game on a `2k rho` mass of tuples only, and item 2
of Theorem O is a per-star bound, so it survives there.

## What survives (the corrected prerequisite)

**(SF_P^rob).** For `delta := gamma'/(4k)`, let `P^delta_r` be the YES
inputs on which every `delta`-approximate kernel map, generic in the sense of
Theorem O, has rank `<= r`. Two parts:
* **(P1^rob)** `(P^delta_r, NO)` is NP-hard;
* **(P2^rob)** (P2) holds on `P^delta_r`.

Theorem O' refutes (P2^rob) only for `r >= k - c`. The w16 local-flip attempt
on the (SF_P) node shows that the flip mechanism gives nothing below
`k - O(log(1/gamma'))`. (P1^rob) is a real hardness question: the inputs must
have no large linear family of near-solutions. Local edits, as here, can make
exact rank `0`, but they cannot remove a robust kernel. Robust kernel-freeness
is plausible for expanding Håstad-format images, but it is unproved.

## Belief change

The (SF_P) node recorded that (P2) "is refuted only at high kernel rank" and
put its open region at "kernel rank `< k - 2l - O(log(1/gamma'))`". That region
contains the J'-instances, of exact rank `0`, on which (P2) is false. The
graph's "low kernel rank" had to mean robust rank all along.

## Attempts

* **2026-09-19, swarm-0917-w17-w17-ugc-pull (minimal-counterexample).** Built
  the J'-instances, verified exact kernel `0`, regularity and the dirty set by
  GF(2) elimination for `n = 6..9`, and transferred Theorem O to
  kernel-clean tuples. Not attempted: (P1^rob), and the range
  `gamma' < 2^(2-l)`, where the `1/(2^l - 1)` cross-star term of item 2
  exceeds `gamma'`.
