# SAT search for strict one-sided inverse pairs in F_2[L^x] (2026-09-12)

Lane `kdf-sat`. Target: `leavitt-unit-group-algebra-not-directly-finite`, that is
`alpha beta = 1 != beta alpha` in `F_2[G]`, `G = L_(F_2)(1,2)^x`. By
`leavitt-stable-finiteness-equals-direct-finiteness` the scalar case is the whole
question, so no matrix sizes are searched.

Encoder: `experiments/nonsofic-certificates/kaplansky-df/sat/dfsat.py` (57e16adfd).
Runs: MSI, `/projects/standard/hsiehph/sauer354/kdf-sat/runs/`, single-threaded
CryptoMiniSat 5.14.3 through `pycryptosat`, on acn112 at `nice 10`.

## Encoding

Fix finite supports `A, B` of group elements and write
`alpha = sum x_a [a]`, `beta = sum y_b [b]`, `z_ab = x_a AND y_b`. Then

    alpha beta = 1   <=>  XOR_{ab = g} z_ab = [g = 1]        for every g in AB,
    beta alpha != 1  <=>  OR_g w_g,   w_g = XOR_{ba = g} z_ab + [g = 1].

The XORs are native XOR clauses. Singleton cells with right-hand side 0 become
unit clauses. The same AND variables serve both products, because
`x_a y_b = y_b x_a`; only the grouping of pairs by product differs. UNSAT means
that no strict pair has `supp alpha` in `A` and `supp beta` in `B`. A SAT model is
recomputed in `F_2[G]`, and only a certificate that passes `certcheck.py` in dual
mode counts.

Products come from the shared normal form `leavitt.py`. The MSI copy is the
archive at `nonsofic-certificates/current`, VERSION 2e9a9873e.

## Controls

| control | expected | result |
|---|---|---|
| `leavitt-control`, all basis monomials `S[a]T[b]` with `|a|, |b| <= 1`, strict | SAT (the defect of `R`) | SAT, `alpha = T[0]`, `beta = S[0]` |
| family `v`, radius 1 by 1, strictness clause dropped | SAT (a trivial unit) | SAT, `alpha beta = beta alpha = 1` on recheck |
| family `v`, radius 1 by 1, strict | UNSAT | UNSAT |

The first control is the only place where the strictness clause can be tested
positively, since no strict pair is known in any group algebra. It runs the
identical encoder on the Leavitt algebra's monomial basis, where products are
sums.

## What prunes the search space before any solve

- `subgroup-supported-one-sided-inverse-rigidity`, applied to each factor
  separately: `<supp alpha>` and `<supp beta>` must each have a non-directly-finite
  `F_2` group algebra. So each must be non-`F_2`-linear-sofic
  (`linear-sofic-group-algebra-is-stably-finite`), and in particular nonsofic,
  not residually finite and not amenable.
- Level-preserving units of bounded depth, meaning all monomials `S[a]T[b]` with
  `|a| = |b|`, generate finite groups. This is step 1 of
  `non-nesting-transporter-finite-block-proof`, pointed out by lane
  `kdf-leavitt-certificate`. Every live support therefore contains
  length-changing units. The standard units `@u @v @w @g` generate `S_3` and are
  dead, as are the rank-three lifts
  (`leavitt-rank-three-lift-has-no-one-sided-inverse`).
- `sofic-support-cannot-install-half-corner-comparison` (db1604762) is the
  sharper form for the comparison stage, where `Z` is a split embedding between
  inequivalent idempotents of a chart `K`. It is what
  `kdf-leavitt-certificate` prunes with. `dfsat` searches complete pairs with no
  chart and no comparison stage, so the operative prune here is the per-factor
  rigidity above. A future comparison-stage encoding must use this lemma instead.
- `dykema-heister-juschenko-bounded-rank-direct-finiteness`: support pairs
  `(3, n <= 11)` and `(5, 5)` are dead over `F_2` for every group, and
  augmentation forces both supports to be odd.

The two families searched are built to avoid all three:

- `v`: balls in the Cannon–Floyd–Parry generators of Thompson's `V`,
  `A = (0,10,11)->(00,01,1)`, `B = (0,10,110,111)->(0,100,101,11)`,
  `C = (0,10,11)->(11,0,10)`, `P = (0,10,11)->(10,0,11)`. `A` and `B` change
  lengths. The soficity of `V` is open.
- `eld`: balls in the OpenAI nine-leaf triple, `E_ij(r) = 1 + S[alpha_i] r T[alpha_j]`
  on `alpha = (000,001,01)` with `r in {1, s0, s1, t0, t1}`, together with the
  compressors `u, v` of `openai-nine-leaf-leavitt-configuration`. Here
  `<Gamma, u, v> = EL_D(R)` is nonsofic, and `Gamma = EL_3(R) =~ R^x` is too.

## Results

`(ra, rb)` gives the ball radii of `A` and `B`. The sizes are `|B_1(V)| = 8`,
`|B_2(V)| = 44`, `|B_3(V)| = 211`, `|B_1(eld)| = 35` and `|B_2(eld)| = 933`.

| family | (ra, rb) | mode | AND vars | status | solve time |
|---|---|---|---|---|---|
| v | (1,1) | strict clause | 64 | UNSAT | 0.0 s |
| v | (2,2) | strict clause | 1,936 | UNSAT | 2.7 s |
| v | (2,3) | strict clause | 9,284 | UNSAT | 147 s |
| eld | (1,1) | strict clause | 1,225 | UNSAT | 0.08 s |
| eld | (1,2) | strict clause | 32,655 | UNSAT | 238 s |
| eld | (2,1) | strict clause | 32,655 | UNSAT | 256 s |

**Target mode so far is only linear.** Gaussian elimination (`span_contains`,
c698d076a) shows that `s0` is not in the `F_2`-span of `pi(B_4(V))` and not in
the span of `pi(B_2(eld))`, and likewise for `t0`. Every target-mode UNSAT
recorded on these families is that linear fact, not a bilinear one:

| family | supports | target | status |
|---|---|---|---|
| v | `B` up to radius 4 | `pi(beta) = s0` | target outside the span |
| v | `A` up to radius 4 | `pi(alpha) = t0` | target outside the span |
| eld | `B` up to radius 2 | `pi(beta) = s0` | target outside the span |
| eld | `A` up to radius 2 | `pi(alpha) = t0` | target outside the span |

So the sharp lift problem needs supports whose evaluations reach `s0`. The atlas
family below does: the predecessor's seven-term lift of `s0` lives in a
radius-three atlas ball.

**Atlas family: the target is in the span, so these are genuine bilinear UNSATs.**
The generators are the two `GL(4,2)` charts on `D_1 = (01,1,000,001)` and
`D_2 = (00,1,010,011)`, two generators per chart as in `four_generator_atlas()`,
and they generate all of `R^x`. The per-factor rigidity therefore kills nothing
here. Sizes: `|B_1| = 9`, `|B_2| = 53`, `|B_3| = 293`.

| (ra, rb) | target | span check | AND vars | status | solve time |
|---|---|---|---|---|---|
| (1,3) | `pi(beta) = s0` | in span | 2,637 | UNSAT | 0.006 s |
| (3,1) | `pi(alpha) = t0` | in span | 2,637 | UNSAT | 0.014 s |
| (2,3) | `pi(beta) = s0` | in span | 15,529 | UNSAT | 2.1 s |
| (3,2) | `pi(alpha) = t0` | in span | 15,529 | UNSAT | 2.9 s |

In words: no `beta` supported in the radius-3 atlas ball evaluates to `s0` and
has a left inverse supported in the radius-2 ball, and dually for `t0`.

Also UNSAT: atlas (1,5) in target mode, meaning `supp a` in `B_5` and `supp b` in
`B_1`, with 78,669 AND variables, in 1.6 s.

**Larger span checks (exact).**
- `s0` is outside the span of `pi(B_5(V))` (1,231 evaluation rows) and of `pi(B_6(V))` (2,649 rows).
- `s0` is outside the span of `pi(B_3(eld))` (1,319 rows).

For `V` this holds at every radius, by the invariant below. For `eld` the generators
generate `EL_D(R) = R^x`, whose evaluations span `R`, so the failure there is a radius
effect and must end at some radius.

**The invariant behind the V failures:**
`s0-lifts-cannot-be-supported-in-the-all-ones-stabilizer`. `R` acts on functions of
binary sequences by `(S[a]T[b] f)(a eta) = f(b eta)`. Units that fix the constant
function `1` form a subgroup `H_1` containing `V`. For `supp beta` inside `H_1`,
`pi(beta) 1 = eps(beta) 1`, while `s_0 1` is the indicator of `[0]`. So no lift of `s_0`
is supported in `V` at any radius. The encoder turns this into a clause: in target
mode `supp beta` must leave `H_1`, and dually `supp alpha` must leave `H^1` for `t_0`.

**At the 600 s limit, without prune clauses.** Target mode on atlas (3,3) and (2,4) is
UNKNOWN (85,849 and 84,959 AND variables). The strict clause on `v` (3,3) is also
UNKNOWN (44,521 variables).

**Running.**
- sbatch `kdf-sat-b8`: controls, then `v` (3,3) strict and atlas (3,3) target, 2,400 s each. It uses the prune clauses of 7e8a94ac9: both supports odd, and neither support inside the degree-zero units or inside a finite chart group.
- sbatch `kdf-sat-b7`, unpruned: atlas (3,4), (4,3), (2,5) and (5,2) in target mode.

## Trust surface

- An UNSAT verdict is CryptoMiniSat's, with no proof log. It records where
  nothing was found and certifies no theorem, so it is used only in `## Attempts`.
- A SAT verdict is worthless until `certcheck.py` passes in dual mode.
