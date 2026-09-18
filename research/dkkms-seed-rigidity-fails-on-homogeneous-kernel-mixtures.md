---
rg: 2
id: dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures
kind: claim
title: (Seed) is false on DKKMS 2-to-1 games -- on regular 3LIN inputs with a homogeneous kernel of rank l+1 generic on tuples, a two-assignment mixture split by the rank of the inner subspace has value 0.711 and satisfied seed labels disagreeing on mass 0.289 > gamma with the honest encoding of every outer labelling
distinct_from:
  dkkms-near-perfect-labellings-are-outer-honest: that is a 99 percent theorem (value 1 - eta forces agreement with a per-tuple patchwork of one outer labelling); this is a 71 percent counterexample showing that no such single-reference statement survives at value 1/2 + gamma, because the two branches are split by the inner subspace L', not by the tuple V.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies the decoding hypotheses for honest encodings; this exhibits non-honest labellings of the same instances, each of whose two branches is the honest encoding of a good assignment.
artifacts:
  - experiments/ugc-seed-mixture-2026-09-17/check_seed_mixture.py
---

**ESTABLISHED** (Theorem M; the transfer to hard input families, Remark P,
is conditional and marked). Route:
`dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures-proof`.

## What is refuted

The need posted as `16613d6f` by the constant-bias node
(`constant-bias-selectors-need-seed-dishonest-witnesses`, Theorem C, survivor
(C4)) asks to prove or refute:

> **(Seed)** every labelling of the folded DKKMS 2-to-1 game with value
> `>= 1/2 + gamma` has satisfied seed (B-)labels agreeing, outside mass
> `gamma/2`, with the honest encoding of some outer labelling of value
> `>= 1 - eps`.

A proof would have killed the constant-bias cell of H1 and all of H2 under
`NP not in RP`. The need names the refuting object as "a seed-dishonest 50
percent labelling, the only surviving witness type". This node constructs it.

## Setting

The notation is that of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`:
* tuples `U`, spaces `X_U`, `H_U` and `h_U`;
* smoothed tuples `V`, with `X_V <= X_U` and `H' := H_U ∩ X_V` spanned by the
  kept `x_e`;
* A-vertices `(U,L)` with `L ∩ H_U = 0`, and B-vertices `(V,L′)`;
* folding classes `C` with representative `R_C`, and the multi-edge game
  `G_multi`;
* the outer game `Φ_k`, and the honest encoding `hon(λ)_(V,L′) = λ_V|_(L′)` of
  an outer labelling `λ`.

For a labelling `h` and any family `λ = (λ_V)` of linear functionals
`λ_V : X_V -> F_2` (this includes every outer labelling, good or not), put:

```text
D(h, λ) := Pr_edge [ edge satisfied by h  and  h_(V,L′) != λ_V|_(L′) ].
```

This is the seed-dishonest satisfied mass. The escape clause of Theorem C is
`D > gamma - gamma' - r - kappa` for every defect-`r` honest reference. So
`D > gamma` escapes Theorem C for every admissible `gamma', r, kappa >= 0`.

## The inputs

A regular 3LIN instance `(X, Eq)` has a **generic kernel of rank `m+1`** if
there is a linear map `Φ = (φ, z) : F_2^X -> F_2^m x F_2` with two properties:
* it vanishes on every equation vector `x_e`, so each coordinate is a
  homogeneous solution;
* it is surjective on `X_V` for all but a `δ_sur` fraction of smoothed tuples
  `V`.

**The J-instances.** Label the variables by `u in F_2^(m+1) \ {0}`, in `N`
disjoint copies. The equations are `x_u + x_(u′) + x_(u+u′) = 0` for all lines
`{u, u′, u+u′}` of each copy. Put `Φ(e_u) := u`.

The instance is regular, with every variable in `2^m - 1` equations, and `Φ`
vanishes on every `x_e`. Every assignment `x` that satisfies all equations is
good, for example `x = 0`. A smoothed tuple with `t` kept or dropped blocks
fails surjectivity with probability at most `2^(m+1) 2^(-t) + O(k^2/N)`, and
`t = k`.

## Statement

**Theorem M (mixture).** Let `(X, Eq)` have a generic kernel `(φ, z)` of rank
`l+1`, so `m = l`. Let `x` be an assignment and put `y := x + z`; this also
satisfies every equation that `x` satisfies. Define:

```text
h_C      = x|_(R_C)  if φ is injective on R_C,   else  y|_(R_C)
h_(V,L′) = x|_(L′)   if φ is injective on L′,    else  y|_(L′)
```

1. **Well defined on classes.** `h` is constant on each folding class, and its
   unfolding at every clean `(U,L)` in `C` is `x|_L` or `y|_L`, according to
   whether `φ` is injective on `L`. When `x` satisfies every equation, as on
   the J-instances, every tuple is clean. Then all multi-edges inside one
   folded constraint have the same outcome, and the multi-edge value equals
   the folded value.
2. **Value.** Put
   `b := Π_(i=0)^(l-2) (1-2^(i-l))/(1-2^(i-d′))`, with `d′ := dim X_V/H′`, and
   `c := (2^(3k-1) - 2^(l-1+k))/(2^(3k) - 2^(l-1+k))`. On every clean, surjective
   `V`:
   `1 - bc <= val_V(h) <= 1 - bc + 2^(1-l)`.
3. **Seed dishonesty.** For every functional family `λ` and every clean,
   surjective `V`, the conditional dishonest mass satisfies
   `D_V(h, λ) >= min(b(1-c), 1-b) - 2^(1-l)`.
4. **Numbers.** As `k -> infinity` with `l` fixed, the unclean or non-surjective
   mass is `O(kε_3 + δ_sur)`. Here `c -> 1/2` and `b -> b_l := Π_(j=2)^l (1-2^(-j))`,
   which tends to `P_1 := Π_(j>=2)(1-2^(-j)) = 0.577576` as `l` grows. So:
   ```text
   val(h)  -> 1 - P_1/2 = 0.711212,      gamma := val - 1/2 -> 0.211212,
   D(h, λ) >= P_1/2 - o(1) = 0.288788    for EVERY λ,
   D - gamma -> P_1 - 1/2 = 0.077576,    D - gamma/2 -> 0.183.
   ```
   The certified finite-`l` margins, with all `2^(1-l)` losses charged, are:
   * `D - gamma > 0` for `l >= 7` (for example `+0.035` at `l = 7` and `+0.072`
     at `l = 10`);
   * `D - gamma/2 > 0` for `l >= 5`.

   The table is in the artifact.

**Corollary M (the refutation).** For every `l >= 5`, every large `k`, and
every `gamma in (0, γ_0(l)]`, (Seed) is false on the J-instances. These are
perfectly satisfiable regular 3LIN instances. Here
`γ_0(l) := 1/2 - b_l/2 - 2^(-l)`, which is `0.171` at `l = 5` and tends to
`0.2112`. The folded value of `h` is at least `1/2 + γ_0(l)`. For `l >= 7`, the same
labellings satisfy even the strong escape `D > gamma` of Theorem C, against
every reference and not only good ones.

**Remark P (hard families; conditional).** Pad any regular
`Gap3Lin(1-ε_3, s*)` input `I` as `I ⊔ J` with J-weight `ω`, where degrees are
matched by repetition. Take `φ` and `z` supported on `J`.

A tuple then carries `t ~ Bin(k, ω)` J-blocks. Surjectivity fails with
probability at most `2^(l+1) E 2^(-t) + O(k^2/N) <= 2^(l+1) e^(-ωk/2) + o(1)`.
Every clean surjective tuple then behaves as in Theorem M, where `x` is the
good assignment of `I ⊔ J`. So YES instances of the padded family carry the
mixture with `G_multi` value `0.711 - kε_3 - o(1)`. This is the game on
which the decoding Corollary runs, by item 2 of the decoding-hypotheses node.

NO instances have value `<= s′ := (1-ω)s* + ω < 1`. The Corollary of the
decoding-hypotheses node, and Theorem C, need Lemma 5.4 of DKKMS (outer
soundness `exp(-k/exp(ql))`) at soundness `s′`. As quoted, it is stated for
`s*`. **Conditional on Lemma 5.4 at `s′`**, the constant-bias escape is
realised on a family on which the whole DKKMS pipeline is NP-hard.

## What this kills

**Class killed.** Every approach to the constant-bias cell of H1, or to H2,
that closes the escape clause of Theorem C through a *single-reference* seed
rigidity statement is killed on inputs with a generic homogeneous kernel of
rank `>= l+1`. This covers statements of the form "satisfied B-labels agree with
`hon(λ)` for one outer labelling `λ`, outside mass `f(gamma) >= gamma/2`",
including per-tuple patchworks in the style of Theorem R.

**Invariant.** The branch of `h` at `(V,L′)` is `rank φ|_(L′) = l-1`. This is
a function of the inner subspace `L′`, not of `V`. Conditioned on any `V`,
both branches carry constant satisfied mass: `b/2` and `1-b`.

**Where it dies.** A reference is a per-`V` functional `λ_V`. Any functional
other than `x|_(X_V)` agrees with `x|_(L′)` on at most a `2^(1-l)` fraction of
the `L′`, and likewise for `y`. Since `z|_(X_V) != 0`, a reference is honest on
at most one branch per `V`.

So single-reference seed rigidity at 50 percent requires the source 3LIN
instance to have no generic near-kernel of rank `>= l+1`. That is a property
of the input, not of the DKKMS construction, and Theorem 4.1 of DKKMS does not
provide it.

**What survives.** A *list* version:

> **(List-Seed)** every labelling of value `>= 1/2 + gamma` has satisfied
> B-labels covered, outside mass `gamma/2`, by `O_gamma(1)` honest encodings
> of good outer labellings.

The mixture is 2-list honest, since `x` and `y` are both good. The
rank-threshold search in the artifact (Part C) finds the following in the
limit model:
* with every branch mass `<= 0.25`, the best value is `0.134`;
* with branch mass `<= 0.3`, it is `0.615`.

So in this family a value above `1/2` forces a branch of mass above `0.25`,
which is what a list decoder needs. Whether Theorem C can be run with a list
of references, and whether selectors can exploit such mixtures, is open.

## Checks

`experiments/ugc-seed-mixture-2026-09-17/check_seed_mixture.py` runs in a few
seconds and exits 0. It has four parts:
* **Part A:** the exact `b` and `c`, the limits, and the finite-`l` margin
  table.
* **Part B:** exact brute force of single clean tuples against every reference
  functional on `X_V`, with `(k,l,m) = (2,2,2), (2,3,3), (3,2,2)` and smoothed
  `V`. It reproduces `R_x = b(1-c)`, `R_xy = bc` and `R_y = 1-b` as exact
  fractions.
* **Part C:** rank-threshold labellings with 2 or 3 branches for
  `m = l-2 .. l+3`. The largest value with `D > gamma` is `0.7112`. The largest
  with `D > gamma/2` is `0.8075`, at `m = l-2`; this is a limit-model
  computation, not part of Theorem M.
* **Part D:** the J-instance at `m = 3`. It is regular, `Φ` vanishes on every
  equation vector, and Monte Carlo of surjectivity at `k = 8` gives
  frequency `0.0005`, below the bound `0.0625`.

## Attempts

* 2026-09-17 (swarm-0917-w12-w12-ugc-follow): constructed the mixture and
  proved Theorem M and Corollary M. The hard-family transfer (Remark P) is left
  conditional on DKKMS Lemma 5.4 at padded soundness `s′`. (Seed) with
  constant `gamma > 0.3075` is not refuted here. The limit model gives no
  rank-threshold labelling with `D > gamma/2` above value `0.8075`.
* 2026-09-18 (swarm-0917-w13-w13-ugc-follow): the mixture `h` of Theorem M
  escapes (Seed) and Corollary C', but not Theorem C itself. Against the
  y-branch, the ev-form mass of Theorem C's hypothesis Str is exactly
  `D_V(h, lambda_y) = b(1-c)/2`, which tends to `0.1444`. That is below
  `gamma - gamma'` at lift values above about `0.645`. The seed-form bound of
  item 3 above does not bound the ev form from below. With the reference read
  off the B-branch, the star-list mass with `L = 2` is `<= 2^(1-l)`, so
  Theorem CL also applies at every larger `gamma`. See
  `list-star-coherent-selector-witnesses-put-np-in-rp` (Remark M1).
