---
rg: 2
id: dkkms-list-seed-needs-lists-exponential-in-l
kind: claim
title: (List-Seed) with a list size depending only on gamma is false on DKKMS 2-to-1 games -- on regular 3LIN inputs with a generic homogeneous kernel of rank 2l, a mixture split by the defect line Phi(L') meet K has value 0.610 and satisfied B-labels at mass 0.289 that no list of fewer than 2^(l-6) per-tuple references covers
distinct_from:
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies the decoding hypotheses for honest encodings; this builds non-honest labellings of the same instances whose satisfied B-labels spread over 2^l different good assignments.
  dkkms-near-perfect-labellings-are-outer-honest: that is a 99 percent single-reference theorem; this shows that at value 0.61 even list-reference statements need lists of size exponential in l.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this refutes one proposed prerequisite (List-Seed with an l-free list) of its constant-bias kill and names the corrected one.
artifacts:
  - experiments/ugc-list-seed-2026-09-17/check_defect_split_mixture.py
---

**ESTABLISHED** (Theorem LS). Route: `dkkms-list-seed-needs-lists-exponential-in-l-proof`.

## What is refuted

Need `a06a9ee8` (bounty 5, on
`parity-leaking-branch-selectors-reach-near-perfect-completeness`) asks to
prove or refute

> **(List-Seed)** every labelling of the folded DKKMS 2-to-1 game of value
> `>= 1/2 + gamma` has satisfied B-labels covered, outside mass `gamma/2`, by
> `O_gamma(1)` honest encodings of good outer labellings,

and then to rerun Theorem C of the constant-bias node (on the w12 integration
branch: `constant-bias-selectors-need-seed-dishonest-witnesses`) with a list of
references. It was posted because single-reference (Seed) is refuted by the
two-branch rank-split mixture of `dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures`
(Theorem M, value `0.711`, also on that branch). The two-branch mixture is 2-list
honest, so it does not touch List-Seed.

This node refutes List-Seed whenever the list size may not grow with `l`. It
survives only as **(List-Seed_l)**, with list size `t(gamma, l) >= 2^(l-6)`.

## Setting

The notation is that of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
(DKKMS, ECCC TR16-198, Section 4.2, quoted verbatim there):
* tuples `U`, spaces `X_U` (dimension `3k`), `H_U`;
* smoothed tuples `V`, with `X_V <= X_U` and `H′ := H_U ∩ X_V`;
* `Q := X_V / H′`, of dimension `d′ >= k`;
* A-vertices `(U,L)` with `L ∩ H_U = 0`, and B-vertices `(V,L′)`;
* folding classes `C` with representatives `R_C`.

A **reference** is a per-tuple functional family `λ = (λ_V)`, which covers every
outer labelling. A list `Λ = {λ^1, ..., λ^t}` covers a satisfied edge
`((U,L),(V,L′))` if `h_(V,L′) = λ^j_V|_(L′)` for some `j`. Put
`D(h, Λ) := Pr_edge[edge satisfied and not covered by Λ]`.

**Inputs.** A regular 3LIN instance has a **generic kernel of rank `n`** if
there is a linear `Φ : F_2^X -> F_2^n` with two properties:
* `Φ(x_e) = 0` for every equation vector;
* `Φ` is surjective on `X_V` for all but a `δ_sur` fraction of smoothed tuples.

The J-instances of the Theorem M node supply one for every `n`, with
`δ_sur <= 2^n 2^(-k) + O(k^2/N)`, and every assignment satisfying all equations
(for example `x = 0`) is good.

## Statement

Write `F_2^n = F_2^l x F_2^s` with `n = l + s`, `Φ = (φ, ζ)`, and
`K := 0 x F_2^s`. For a subspace `S` put `c(S) := Φ(S) ∩ K`. Fix an
assignment `x`. For nonzero `d ∈ F_2^s` let `y_d := x + <d, ζ(·)>`; each `y_d`
satisfies exactly the equations that `x` satisfies.

**The labelling `h`.** On `S = R_C` (A-side) or `S = L′` (B-side):

```text
h_S = y_d|_S   if c(S) = <(0,d)> is one-dimensional,
h_S = x|_S     otherwise.
```

**Theorem LS.** Let the instance have a generic kernel of rank `l + s`, with
`l >= 3` and `s >= 2`, and suppose `x` satisfies every equation (J-instances).
Let `N` be the nullity of `φ` on `L′`. Then:

1. **Well defined, honest unfolding.** `c(R_C) = c(L)` for every member
   `(U,L)` of `C`. The unfolding of `h_C` at `(U,L)` is `a|_L`, where `a` is
   the branch assignment of `C`. The folded value equals the multi-edge value.
2. **Value.** On every surjective `V`,
   `val_V(h) >= 1 - E[2^(-1-N) | V]`.
3. **Every list is thin on the defect branches.** For every surjective `V`
   and every functional `λ_V`, the satisfied mass on B-vertices with
   one-dimensional `c(L′)` that `λ_V` covers is at most `2^(-s) + 2^(3-l)`.
   The satisfied mass on such B-vertices is at least
   `(3/4) Pr[N = 1 | V] - 3 * 2^(-s-1)`.
4. **Numbers** (`k -> infinity` at fixed `l, s`; exact rationals in the artifact):

   | l | P(N=0) | P(N=1) | val >= | gamma | defect mass >= |
   |---|---|---|---|---|---|
   | 8 | 0.5798 | 0.3835 | 0.6097 | 0.1097 | 0.2818 |
   | 12 | 0.5777 | 0.3850 | 0.6103 | 0.1103 | 0.2884 |
   | oo | 0.5776 | 0.3851 | 0.6103 | 0.1103 | 0.2888 |

**Corollary LS (the refutation).** Take `s = l` and `l >= 8`. The instance
then needs `2l << k`. For every `gamma <= 0.109` and every large `k`, the
labelling `h` has value `>= 1/2 + gamma`. Every list of
`t < 2^(l-6)` references leaves uncovered satisfied mass
`D(h, Λ) > gamma/2`. As `l -> infinity`, the threshold is
`t_min ~ 0.026 * 2^l`. So no list size `O_gamma(1)` independent of `l` works,
on perfectly satisfiable regular inputs. The padded hard-family transfer of the
Theorem M node (its Remark P, conditional on DKKMS Lemma 5.4 at padded
soundness) applies unchanged.

## What this kills (impact types 3 and 4)

**Class killed.** Every closure of the constant-bias cell of H1 or H2 through a
list-reference seed statement whose list size is independent of `l`. This
includes the literal List-Seed of need `a06a9ee8` and every rerun of Theorem C
that loses only a factor `poly(1/gamma)` for the list.

**Invariant.** The branch is the *defect line* `c(L′) = Φ(L′) ∩ K`. It is a
function of `L′` only (not of `V`), it is inherited by `L ⊃ L′` except when
`φ(w) ∈ φ(L′)`, which has probability `2^(-1-N)`, and it takes
`2^s - 1` values, each of mass `< 2^(-s-1)`.

**Where it dies.** A reference `λ_V` is one functional per tuple. By item 3 it
covers the branch of at most one defect line, up to `2^(3-l)`. A list of `t`
references therefore covers at most `t (2^(-s) + 2^(3-l))` of the defect mass
`0.288`.

**What survives (the corrected prerequisite).**
* **(List-Seed_l)** List-Seed with list size `t(gamma, l)`. Every labelling in
  this node is covered by the `2^s` references `{x} ∪ {y_d}`, so
  `t(gamma, l) = 2^(Theta(l))` is not refuted.
* **List-decoding rerun.** Theorem C must then be rerun with a loss of
  `1/t = 2^(-Theta(l))`. This is affordable against DKKMS outer soundness
  `exp(-k/exp(ql))` at large `k`, but it has to be proved. A random-guess
  reference loses exactly this factor.
* **Heavy reference.** In this family the single reference `x` has honest
  satisfied mass `P(N=0)/2 = 0.289 < 1/2`. So any rerun that needs one
  reference above `1/2` fails here as well, as it does for Theorem M.

## Belief change

The graph recorded, after Theorem M, that "a value above 1/2 forces a branch of
mass above 0.25, which is what a list decoder needs". That limit-model
observation was about 2- and 3-branch rank-threshold labellings. It is false
for defect-line splits. At value `0.61`, the non-`x` satisfied mass `0.288`
is spread over `2^s - 1` branches of mass below `2^(-s-1)` each. The `x`
branch alone carries `0.289`, which is heavy but below one half.

## Attempts

* **Defect-line split (2026-09-18, swarm-0917-w13-w13-ugc-last1).** Proved
  Theorem LS and Corollary LS. The artifact checks the nullity law exactly
  (Part A) and the growth and defect-mass bounds by exact enumeration of the
  image model for `(l,s) = (3,1), (3,2), (4,1), (3,3)` (Part B).
* **Open.** Prove (List-Seed_l) with `t = 2^(O(l))`, or push the lower bound on
  `t` past `1/eps_k`. The latter would need kernels of rank `>> k`, which
  surjectivity on `X_V` (`d′ ~ 2k`) forbids in this construction.
