# Ternary anti-central route: bilinear lift screens, unit absorption, and why the obstruction must be linear

Lane `gk3-ternary-bilinear`, 2026-09-14. Continues `research/artifacts/gk3-ternary-fullness-2026-09-14.md`.
Target: decide `ternary-anti-invariant-swap-corner-is-full` (equivalently, by
`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`, the failure of
`anti-central-lifted-trace-is-relatively-positive`) from either side. Nothing here decides it.

## 0. Setting

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S_- = eps_- F_3[G] = F_3[G]/(1 + [z])`, `pi : S_- -> R` the
  evaluation, `K_- = ker pi`.
- Condition (V3*) (kernel normal forms artifact, 3.3): some lift `alpha` of `s0` is left invertible in `S_-`.
  Any failure of direct finiteness of `S_-` transfers to (I3*), and (V3*) implies (I3*) (Theorem 4 there), so
  (V3*) is a sufficient witness shape for a strict linear automaton over `G` on `F_3^G`.
- `alpha0 = 2[A] + 2[A D] + 2[A'] + [A' D]` is the explicit support-four lift of `s0`, with `A = (0,10,11) -> (00,01,1)`,
  `A' = (00,01,1) -> (00,1,01)`, `D = diag(1,-1)`.
- `P = U_2`, the level-two unitriangular 3-group (order 729); `span{[p] - 1}` is nilpotent.
- `mix2` is the generating set `{A, A', W, D, sigma_00, sigma_01}` of `pscreen.py`.

## 1. Obstruction side

**1.1 What a state needs.** By `anti-central-state-obstruction-equals-stable-finiteness` a state on
`(K_0(S_-), [eps_-])` exists iff `[eps_-]` is not `<= 0`. Every known way to produce one is a Sylvester matrix
rank function `N` on `S_-` with `N(eps_-) = 1`, or equivalently a unital map into a ring with such a function.

**1.2 Permutation-type rank functions cannot work (conditional remark, not a node).** Let `G` act on a set `X`
on which `z` acts freely, and let `V_-` be the functions `f : X -> F_3` with `f(zx) = -f(x)` and finite support.
`S_-` acts on `V_-`. If the action has Følner sets `F_n` (`z`-invariant, `|gF_n Δ F_n| = o(|F_n|)` for every `g`),
then

    N(x) = lim_omega rank(P_n x P_n) / (k |F_n| / 2)       (x in M_k(S_-), P_n = restriction to F_n)

is a Sylvester matrix rank function with `N(eps_-) = 1`: products differ from compressed products by boundary
terms of rank `o(|F_n|)`, and block-diagonal and triangular laws hold exactly on the compressions. So an amenable
action with `z` free kills the corner route.

Such actions do not exist when `G` has a Kazhdan pair. By `kazhdan-groups-mean-free-amenable-iff-residually-finite`
invariant means then live on finite orbits. A finite orbit on which `z` acts freely is a finite quotient of `G`
moving `z`, hence a nonzero finite-dimensional representation of `S_-`, and there is none (kernel normal forms
artifact §5). A Kazhdan pair for `G` is not pinned on main here, so this remark is conditional. Its point is
that the obstruction side is genuinely linear: states must come from rank models of `G` over `F_3` moving `z`
(`ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`), not from Følner or permutation data.

**1.3 Where the obstruction side stops.** No new positivity input was found. The lifted trace `s_3` obeys every
state law (lifted-trace artifact Proposition 1.1), finite-support lifts are positive (Remark 3.1), and nothing
gives order to infinite-support `Z_3` lifts. This lane lands no obstruction node.

## 2. Witness side: unit absorption and bilinear screens

**Lemma 2.1 (unit absorption).** Let `K <= G` be finite, `u` a unit of `eps_- F_3[K]` with `pi(u) = 1`, `C <= G`
finite, and `beta in span(C)` with `beta alpha = u`. Then `(u^-1 beta) alpha = eps_-` and `u^-1 beta` lies in
`span(K . C)`. *Proof.* `u^-1 in eps_- F_3[K]`. QED

So a left-inverse screen over `span(K . C)` with no correction covers every correction by units of
`eps_- F_3[K]` over `1`. These include semisimple units such as `eps_- + q`, `q` the Klein idempotent of
`ternary-anti-central-kernel-has-klein-idempotents` (`(eps_- + q)^2 = eps_- + 3q = eps_-`), which the unitriangular
corrections of the linear screens never reach.

**2.2 The bilinear problem.** Let `k_1, ..., k_d` be a basis of `ker pi ∩ span(B)`, `B` a lift ball. Every lift of
`s0` in `alpha0 + span(B)` is `alpha(lambda) = alpha0 + sum lambda_i k_i`, `lambda in F_3^d`. The screen asks for
`lambda`, `beta in span(C)` and `n in span{[p] - 1 : p in P}` with

    beta alpha(lambda) = eps_- + n.                                       (*)

`(*)` is bilinear. A solution gives a left inverse `(eps_- + n)^(-1) beta`, and `alpha beta' != eps_-` because
`pi(alpha) = s0` has no right inverse. Every slice is image-feasible: `pi(alpha(lambda)) = s0` for all `lambda`, and
the evaluated system is solvable for the balls below.

**2.3 Tool.** `experiments/gottschalk-ternary-corner/bscreen.py` (fd69c4432, `--mult` added in 2e72451f2):
- *exhaust* enumerates every `lambda` in a shard, solves each slice exactly over `F_3`, and re-verifies each UNSAT
  functional from a fresh unit registry;
- *relax* linearizes `nu_(c,i) = beta_c lambda_i`; UNSAT would exclude every `lambda` at once;
- `--mult {klein, e2, gl2}` replaces `C` by `K . C` for the Klein group `<h1, h2>` (order 4), the level-two sign
  diagonals (order 16) or `GL_2(F_3)` at level one (order 48), per Lemma 2.1.

**Controls, all PASS (MSI job 792088, and re-run at the start of every job).**
- K1 planted: `alpha0 = [g] + k` with direction `-k`, `C = B_1`. Exhaust finds exactly `lambda = 1` SAT (the other
  two slices UNSAT, verified); the relaxation is SAT.
- K2 forced UNSAT: `alpha0 = e_-` with three kernel directions. `pi(alpha) = 2(1 + w)` is an idempotent `!= 1`, which
  has no left inverse in `R`. All 27 slices UNSAT with verified functionals; the relaxation is UNSAT with a verified
  functional (992 columns, rank 941).

## 3. Results

Raw data: `experiments/gottschalk-ternary-corner/runs-bilinear/summary.json` (per-shard counts, sizes, seconds and
controls; md5 `d1769a05ee8944414b217c55d5550f1b` on MSI and locally).

### 3.1 Exhaust, `beta in span(C_3)` (job array 792373, tasks 0–15)

| lift ball `B` | `d` | `|C_3|` | `|P|` | slices | SAT | UNSAT, functional verified | unverified | CPU seconds |
|---|---|---|---|---|---|---|---|---|
| mix2, radius 2 (38) | 9 | 147 | 729 | 19683 | 0 | 19683 | 0 | 8272 |

- The 16 shards cover `[0, 19683)` contiguously, and every shard re-ran and passed K1 and K2.
- Each slice is image-feasible, so no UNSAT is vacuous.
- This is `s0-lift-affine-box-has-no-small-left-inverse`. It contains the single-lift slices of `gk3-ternary-fullness`
  whose lift lies in the box, among them the explicit lift and all nine kernel directions at once.

### 3.2 Linearized relaxations (job array 792374)

| lift ball | `d` | `C` | columns | rows | rank | result |
|---|---|---|---|---|---|---|
| mix2, radius 2 | 9 | mix2 radius 4 (516) | 5888 | 4884 | 2777 | SAT: inconclusive |
| mix2, radius 3 | 65 | mix2 radius 3 (147) | 10430 | 5495 | 3835 | SAT: inconclusive |
| mix, radius 1 | 30 | mix radius 1 (75) | 3053 | 4498 | 2771 | UNSAT, functional verified, **vacuous** |

- **Vacuous row.** The last UNSAT is vacuous because the evaluated system is infeasible there: `pi(span C)` with the
  unitriangular corrections carries no left inverse of `s0` even in `R`. It proves nothing.
- **What the SAT rows mean.** Once `nu_(c,i)` is free, the products `[c] k_i` span far too much. The relaxation does not
  separate at useful sizes, and exhaustion is what certifies.

### 3.3 Still running when this section was written

- Exhaust with `beta in span(C_4)` (`|C_4| = 516`, job 792373 tasks 16–31).
- Exhaust with `beta in span(H . C_3)` (`|H . C_3| = 344`, job 792749 tasks 0–15). 4 of 16 shards were done: 4924
  slices, all UNSAT with verified functionals.
- Relaxations with `--mult klein` (radius 4), `e2` (radius 4) and `gl2` (radius 3) (job 792749 tasks 16–18).

Their totals will be appended here when complete. Until then the claim node covers only 3.1.

## 4. Verdict and exact gap

**Not decided.** Nothing here proves or refutes `ternary-anti-invariant-swap-corner-is-full`, and no conjecture is
decided.

**Landed.**
- `bscreen.py`: bilinear exhaust and relaxation modes, finite-subgroup unit absorption, controls K1/K2.
- Lemma 2.1 (unit absorption).
- The conditional remark 1.2: Følner-type permutation rank functions would give the state, and are excluded when `G`
  has a Kazhdan pair.
- The census claim `s0-lift-affine-box-has-no-small-left-inverse`, ESTABLISHED, computer-assisted and unreviewed.

**Exact gap.**
1. **Witness side.**
   - Search cost grows as `3^d` in the affine directions, and the linearization is too loose, so bounded search will
     not reach the deep supports a witness needs.
   - A witness needs a design: a unital two-pair Cohn family `gamma_i beta_j = delta_ij e_-` in the corner
     `e_- S_- e_-` (part 3 of `ternary-leavitt-swap-problem-splits-at-central-involution`), built from structured
     non-core units rather than balls; or a (V3*) lift whose product `beta0 alpha0` of lifts over `(s0, t0)` is a unit.
   - The natural pair of support-four lifts gives `beta0 alpha0` with support nine and `pi = 1`. Its support generated
     at least 7296 group elements before the closure check stopped, still growing. So invertibility cannot be read off
     inside a small finite subgroup algebra. Invertibility of `beta0 alpha0` itself was not tested.
2. **Obstruction side.**
   - A state on `(K_0(S_-), [eps_-])` must come from genuinely linear data: a rank model of `G` over `F_3` moving `z`,
     or positivity of infinite-support `Z_3` lifts.
   - Permutation-type Følner rank functions do not exist if `G` has a Kazhdan pair (remark 1.2). Pinning a Kazhdan pair
     for `L_(F_3)(1,2)^x` on main would make that remark unconditional.
