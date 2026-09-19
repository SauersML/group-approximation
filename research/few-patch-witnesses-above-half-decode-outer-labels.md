---
rg: 2
id: few-patch-witnesses-above-half-decode-outer-labels
kind: claim
title: On DKKMS 2-to-1 instances a polynomial-time selector whose YES lift has value 1/2 + gamma through a witness using at most P global linear patches per outer vertex, with P^2 2^(1-l) well below gamma, puts NP in RP; so an intermediate-window witness needs about 2^(l/2) patches per outer vertex
distinct_from:
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes only from honest or zeta-near-honest witnesses (one patch); this allows P patches per outer vertex that may disagree everywhere with every good outer labelling, and replaces closeness by seed-class uniqueness outside pair kernels.
  high-advantage-selector-witnesses-decode-good-outer-labellings: that needs lift value near 1 and a locally honest patchwork of small dirt; this works at every lift value above 1/2 and prices the patchwork by its number of patches, not its dirt.
  view-local-selectors-beat-one-half-through-non-honest-witnesses: that is the open H2 existence question for view-local selectors; this constrains the H2 witness itself, for every selector, to use many patches or kernel-aligned patch families.
  dkkms-certified-parameters-lie-in-the-selector-kill-regime: that closes near-1 completeness; this is about the surviving window (1/2, 1 - 10^(-5)).
artifacts:
  - experiments/ugc-intermediate-window-2026-09-17/check_patchwork_acceptance.py
---

**OPEN.** Lemmas A–C below are proved here in full (they are elementary).
The assembly into the Theorem needs the DKKMS-specific consistency step (Q2)
checked against the paper's folding and projection conventions, which has not
been done. So the node stays OPEN.

## Setting

`G = G_folded(I)` at a DKKMS-certified point, with A-vertices `(U, L)`,
`dim L = l`, and B-vertices `(V, L')`, `L' < L` of codimension one. Each
constraint is written in the linear normal form of
`orientation-lifts-sandwich-2to1-game-values`: for seed `w = (V, L')` with
label `beta`, the selector bit is `g_e(beta)`, and the edge to `a = (U, L)`,
`L = L' + x_e`, is lift-satisfied by a labelling `W` iff
`W_a|L' = beta` and `W_a(x_e) = g_e(beta)` (known offsets absorbed).

A lift labelling `W` is **P-patched** if for every outer vertex `U` there is a
set `F_U` of at most `P` linear forms on `F_2^U` with `W_(U,L) = f|_L` for some
`f in F_U`, for every `L`. Honest labellings are 1-patched. Every labelling is
`2^(3k)`-patched, so `P` is the invariant.

## Lemmas

**Lemma A (seed identity).** Fix `(w, U)`. Let `S` be the set of
lift-satisfied edges from `w` into the cloud of `U`, and for `e in S` let
`phi(e) = W_(a_e)(x_e)`. For every linear form `f` on `F_2^U`,

```text
E_e [ (-1)^(g_e(beta) + f(x_e)) ]  >=  2 Pr[e in S, phi(e) = f(x_e)] - 1,
```

and a completion of `g` on the complement of `S` attains equality. *Proof.* On
`S` the bit equals `phi`; off `S` each term is at least `-1`. Equality: set
`g_e(beta) = f(x_e) + 1` off `S`.

So Theorem-1 decoding at `(w, U)` needs one form agreeing with `phi` on more
than half of the whole seed star. Lift value `1/2 + gamma` alone does not give
this. The obstruction is precise:
- the invariant is `max_f Pr[S and phi = f]`;
- it dies at the Parseval step of
  `efficient-branch-selectors-list-decode-honest-outer-labels`;
- Lemma A's equality case is realised by an arbitrary function `g`, which is
  all that Theorem 1's proof uses.

**Lemma B (pointwise explanation is vacuous).** Every `h : F_2^m -> F_2` agrees
pointwise with one of the `m + 1` forms `0, e_1, ..., e_m`: take `0` where
`h(x) = 0`, and otherwise `e_i` for any `i` with `x_i = 1`. For bent `h`, every
Walsh correlation is `2^(-m/2)`, as the artifact checks at `m = 6, 8`. So a
decoder cannot use the fact that each satisfied edge is explained by some good
form. It must use where each patch lives.

**Lemma C (seed-class uniqueness).** If `W` is P-patched and the seed `L'` lies
in no pair kernel `ker(f - f')` with `f != f'` in `F_U`, then all of `S` at
`(w, U)` uses a single form `f_(w,U)`, since satisfaction forces
`f|_(L') = beta`. Then `phi = f_(w,U)` on `S`, and by Lemma A the correlation is
at least `2 s_(w,U) - 1`. A fixed nonzero form contains a uniform
`(l-1)`-space with probability at most `2^(1-l)`, up to the direction-law
defect `tau`.

Caveat: the seed lives in the embedded `F_2^V`, so what matters is the
restriction `(f - f')|_V`. This restriction vanishes identically for a random
`V < U` with probability at most the smoothness defect `zeta_sm` of the outer
cover. So the kernel seeds have mass at most
`C(P,2) (2^(1-l) + zeta_sm) + tau`. Every later use of `2^(1-l)` should be read
with `zeta_sm` added.

## Theorem (conditional on Q2)

Let `gamma > 0`, and let `P` satisfy `P^2 2^(1-l) <= gamma/4`. Suppose a
polynomial-time selector has, on every YES instance, a P-patched lift witness
of value `>= 1/2 + gamma`. Assume (Q2) below. Then NP is in RP.

*Sketch.*
- Pairs `(w, U)` with `s_(w,U) >= 1/2 + gamma/2` carry mass `>= gamma/2`.
  Removing kernel seeds leaves mass `>= gamma/4`, where Lemma C gives
  correlation `>= gamma` with `f_(w,U)`.
- Guess `beta` (probability `2^(-l)`). Parseval then returns `f_(w,U)` from a
  list of `gamma^(-2)`.
- **(Q2) patch consistency.** At a B-vertex `(V, L')` outside the kernels of
  the `V`-restrictions of `F_U` and `F_(U')`, satisfied edges into `U` and `U'`
  use forms whose restrictions to `F_2^V` agree on `L'`, so they are equal.
  The pair is then outer-consistent, after the folding offsets, exactly as for
  honest labels in `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`.
  The kernel mass is at most `P^2 2^(1-l)`.
- Decoding `U` and `U'` from independent random seeds picks the patch pair
  realised at a common B-vertex with probability `>= 1/P^2` times the rates
  above. This gives an outer labelling of value
  `>= c0' = gamma^4 2^(-2l) / (64 P^2 K^2) - 2 eps`.
- The certified outer soundness `s` is below `c0'/2`, because `k` is chosen
  after `l` and `P <= 2^(l/2)`. The RP amplification is that of Theorem 1.

(Q2) is the step that remains unchecked. It needs the DKKMS projection
`U -> V` to act on labels by restriction to embedded coordinates, with folding
applied uniformly across `F_U`.

## Consequence (impact type 3, conditional on Q2)

In the intermediate window `(1/2, 1 - 10^(-5))`, the only witnesses Theorem-1
decoding cannot reach are:
- (i) witnesses with `P > sqrt(gamma/8) 2^((l-1)/2)` patches per outer vertex;
- (ii) patch families that are kernel-aligned, where a positive fraction of
  seeds lie in `ker(f - f')` for patches of one outer vertex. For example
  `lambda + D` with `dim D >= l`, where every seed mixes patches.

Type (ii) is exactly the branch-matching freedom: at a kernel seed the witness
can pick, edge by edge, the patch that agrees with the selector bit. By Lemma B,
type (i) cannot be ruled out by counting alone.

## Attempts

* **Small-parameter acceptance check (2026-09-18).** The artifact measures the
  G-value of honest, two-patch, zoom-in, zoom-out and two-form zoom-in
  patchworks at `(m, l) = (5, 2), (6, 3)`. All exceed `1/2`
  (`0.60`–`0.87`). This is **uninformative**:
  - `l = 2` has the trivial floor `2^(1-l) = 1/2`;
  - at `m = 6` a zoom-in set has mass `1/9`.

  The heuristic large-`m` value of a random-rank zoom-in patchwork is about
  `(2^(l-1) - 1)/(2^l - 1) + 2^(-l)`, which is roughly `1/2`. It is not proved
  here.
