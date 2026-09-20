---
rg: 2
id: thompson-f-size-profile-spectral-relaxation-has-value-one
kind: claim
title: The size-profile relaxation of the Rayleigh quotient of Thompson's F on pointed forests has value exactly 1 - a multi-count cut-blind tower law Q on (tree sizes, pointer) has TV(Q, rho Q) + TV(Q, mu Q) <= 3/W, so no argument that reads a near-eigenvector only through its pushed-forward size law and the two data-processing inequalities can prove ||P|| < 1
distinct_from:
  thompson-f-tower-size-laws-have-zero-defect: that is a cut-blind tower lemma for one fixed number w+1 of intervals, with a uniform height window, used for the shadow defect of flows on the positive monoid; this is a spectral statement on pointed forests, and it needs one law that is cut-blind for every number of intervals up to H+1 at once (the merge changes the count), which is proved here with a pinned top level instead of a height window.
  thompson-f-tree-size-observations-have-zero-defect: that kills transport rules on Guba sets reading sizes and depths, via Theorem A of the flow gate; this kills Rayleigh-quotient arguments on the pointed-forest model, a different certificate shape (one law Q and two total variations, no minimax, no finite set S).
  thompson-f-flow-certificate-observation-gate: that is the minimax gate for flows; this is the analogous gate for the spectral route, restricted to the data-processing inequality, and it does not use Sion's theorem.
  thompson-f-near-eigenvectors-need-log-scale-pointer-spread: that proves a necessary condition on the size law of a near-eigenvector; this shows every such necessary condition, and any finite list of them, is jointly satisfiable, so the family can never close to a contradiction.
  thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes: same relation; the tower law here meets its conclusion, with a tree of tower height about 2W within distance W of the pointer.
  thompson-f-near-eigenvectors-have-fibonacci-tree-profiles: same relation as the two above.
  thompson-f-near-eigenvectors-are-log-flat-near-the-pointer: same relation as the three above.
  thompson-f-markov-size-chain-scale-limit-affinity-at-most-0-978: that caps one class of actual test vectors (size-measurable Markov chains with recursive shapes) at 0.978; this says the cap cannot come from the size law alone, since the relaxation of every size law is 1, so the loss there is paid in lifting a size law to vectors on forests.
  thompson-f-is-amenable: that is the open root; this decides nothing about it and kills one witness class of its negation.
  thompson-f-is-not-amenable: that is the open negation; this kills the size-profile spectral route to it.
---

**ESTABLISHED** through `thompson-f-size-profile-spectral-relaxation-proof` (direct, self-contained proof;
agent-verified, not independently refereed; no priority claimed).

## Setting

This is the model of `thompson-f-one-sided-forest-windows-are-norm-lossless`, items 1, 3 and 4, in the
conventions of `thompson-f-near-eigenvectors-doubly-exponential-proof`.
- `R` is the set of one-sided pointed forests `v = (T_0, T_1, ...; i)`.
- `ρ` moves the pointer right. `μ` replaces `T_i, T_(i+1)` by the tree `(T_i, T_(i+1))`. Both are
  injective maps `R -> R`.
- For unit `f >= 0` on `R`, `⟨f, K f⟩ = 2 Σ_v f(v) f(ρv) + 2 Σ_v f(v) f(μv)` and `⟨f, P f⟩ = ⟨f, K f⟩/4`.
  `F` is amenable iff `sup_f ⟨f, P f⟩ = 1`.
- `m = f²`. For probability laws `p, q`, `BC(p, q) = Σ √(p q)` and `TV(p, q) = (1/2) Σ |p − q|`.

**The size observation.** `Ψ(v) = ((|T_j|)_(j >= 0), i)`, the sequence of leaf counts and the pointer. Its
image `X` is the set of pairs `(n, i)` with `n` a sequence of positive integers, all but finitely many
equal to `1`, and `i >= 0`. Every such pair is realized. The moves descend to `X`:
- `ρ̃(n, i) = (n, i + 1)`;
- `μ̃(n, i)` replaces `n_i, n_(i+1)` by `n_i + n_(i+1)` and shifts the rest left.

So `Ψ ∘ ρ = ρ̃ ∘ Ψ` and `Ψ ∘ μ = μ̃ ∘ Ψ`.

**Data processing.** Let `Q = Ψ_* m`. For `g ∈ {ρ, μ}`, `Σ_v f(v) f(gv) = BC(m, g_* m)`, because `g` is
injective. Pushing forward does not decrease `BC`. Hence

`⟨f, P f⟩ <= V(Q) := (BC(Q, ρ̃_* Q) + BC(Q, μ̃_* Q)) / 2`,   and `1 − V(Q) <= (TV(Q, ρ̃_*Q) + TV(Q, μ̃_*Q))/2`.

Every size-profile theorem on this model uses `f` only through this: it bounds
`t_ρ = TV(Q, ρ̃_* Q)` and `t_μ = TV(Q, μ̃_* Q)` by `O(√η)` and then reads events of `Q`. This holds for
the log-scale spread, log-flat, Fibonacci and doubly-exponential nodes.

## Theorem

**Theorem (the relaxation is trivial).** For every integer `W >= 1` there is a finitely supported law `Q_W`
on `X` with

`TV(Q_W, ρ̃_* Q_W) = 1/W`   and   `TV(Q_W, μ̃_* Q_W) <= 2/W`.

Hence `sup_Q V(Q) = 1` and `inf_Q (t_ρ + t_μ) = 0`. The same holds for every word `g` in `ρ, μ`: by the
triangle inequality and contraction of `TV` under pushforward, `TV(Q_W, g̃_* Q_W) <= 2|g|/W`.

**The law** (full construction and proof in the route).
1. **Multi-count cut-blind tower (Lemma T).** For all `N, H >= 1` and `ε > 0` there is a law of positive
   integers `(a_1, ..., a_N)` such that, for every `k <= min(H, N − 1)` and every two cuts of `1..N` into
   `k + 1` consecutive nonempty intervals, the laws of the interval-sum vectors are within
   `ε (k + 1)(k + 2)` in total variation.
   - Levels `t = 1..H+1` of left-dominant atoms `a^(t)_v = 2^(L^(t)_v) + u^(t)_v`, with `u` uniform on
     `{0, ..., 2^(L) − 1}`.
   - `L^(t)_v = Λ_t − Σ_(u < v) g^(t)_u`. The first log-level `L^(t)_1 = Λ_t` is **pinned**.
   - The gaps are `g^(t) = G + a^(t+1)`, and the top level has constant gaps `G`.
   - `ε = 2^(2−G) + G N 2^(−R)`, where `R` is a floor for every log-level, secured by choosing the `Λ_t`
     top-down.
2. **Mixture over the count.** Take `N = 2W + 1`, `H = 2W` and `ε (2W+1)(2W+2) <= 1/W`.
   - Draw `w` uniform on `{W, ..., 2W}` and the pointer `i` uniform on `{0, ..., W − 1}`, independently.
   - The forest has sizes `n_j = a_(j+1)` for `j < w` and `n_w = a_(w+1) + ... + a_N`. That is the
     standard cut into `w + 1` intervals. All later trees are leaves.

**Why it works.**
- `ρ̃` shifts the uniform pointer: `t_ρ = 1/W`.
- `μ̃` at `i <= W − 1 < w` merges two of the first `w + 1` intervals. The result is a cut into `w`
  intervals, so by Lemma T its law is `1/W`-close to the standard cut into `w` intervals, which is `Q_W`
  conditioned on `w − 1`. The count `w − 1` is uniform on `{W − 1, ..., 2W − 1}`, and it differs from the
  count law of `Q_W` by `1/(W + 1)`.
- The pinned top level is what makes one law blind for **all** counts at once. The recursion strips one
  coordinate per level. It reaches a single interval, whose log-level is the constant `Λ_t`, after `k`
  levels, whatever `k` is.

## Class killed

**Class.** A *size-profile spectral argument* is a proof of `||P|| <= c` that uses a unit `f >= 0` only
through `Q = Ψ_*(f²)` and through the inequalities `BC(Q, g̃_*Q) >= BC(f², g_* f²)` for words `g` in
`ρ, μ`, or their total variation and Hellinger forms.
- Every such argument proves at best `||P|| <= sup_Q V(Q) = 1`, so it proves nothing.
- Equivalently, any finite list of conclusions of the form "`t_ρ + t_μ <= τ` implies `Q(E_k) <= φ_k(τ)`",
  with `φ_k(τ) -> 0`, is jointly satisfiable for every `τ > 0`. Such conclusions are pointer spread,
  log-flatness, Fibonacci runs, doubly exponential runs, or any tower-height extension of them. They
  describe near-eigenvectors and never contradict each other.

**Invariant.** The law `Q_W`: a cluster of `w + 1` tree sizes, cut from one multi-count cut-blind tower,
with a uniform number of clusters and a uniform pointer.

**Where every member dies.** At the merge step. The merge sends the size law of a cut into `w + 1`
intervals to that of a cut into `w` intervals, and Lemma T makes this indistinguishable from `Q_W` with
one cluster fewer. Any test event `E` has `Q_W(E) − Q_W(μ̃^(−1)E) <= 2/W`, so any inequality derived from
`t_μ` alone is satisfied.

**Calibration against the existing profile theorems.** `Q_W` has, within distance `W` of the pointer,
trees of tower height about `2W`. The spread, Fibonacci and doubly exponential theorems all ask for less
at the deficit `t_ρ + t_μ ≈ 3/W`, so they are met, as they must be.

## Scope

- **Not a statement about test vectors.** `V(Q)` is an upper bound for every `f` with `Ψ_*(f²) = Q`, but
  it need not be attained. The best vector over a fixed size law, `c*(Q) = sup{⟨f, P f⟩ : Ψ_*(f²) = Q}`,
  has `sup_Q c*(Q) = ||P||`, and whether that is `1` is the root question. The theorem kills only
  arguments that pass through the data-processing inequality. For example, it does not touch bounds that
  use the number of tree shapes of a given size, such as the Catalan count in the fibre of `Ψ`.
- **Survivors.** Arguments reading unbounded-depth shape data of individual trees survive: Moore
  derivatives, the root-local Moore tower of `thompson-f-near-eigenvectors-carry-a-root-local-moore-tower`,
  and the Ackermann hierarchy of `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`. Arguments on
  the full group, which use pointer-left and split as well as `ρ`, `μ`, also survive. The theorem covers
  the inverse moves only through the symmetric `BC` and `TV`, not through observations that split trees.
- **Direction.** The theorem is consistent with both answers. If `F` is amenable, the size law of a
  Følner vector is another such `Q`. The content is that such `Q` exist *unconditionally*, so a positive
  infimum of `t_ρ + t_μ`, which would have proved non-amenability, does not exist.

## What is left

1. **Shape lifting (the whole problem, reduced).** Condition `m` on the size observation. The chain rule
   for Hellinger affinity gives
   `BC(m, μ_* m) = Σ_x √(Q(x) μ̃_*Q(x)) · BC(m(· | x), (μ_* m)(· | x))`, where `x = (n, i)`.
   The size factor is now free by the theorem. So `F` is amenable iff the size-conditional shape laws
   can be chosen almost equivariant under merge and pointer-right, averaged along some near-invariant
   `Q`. The theorem says every obstruction lives in the second factor. The first falsifiable step is
   the Catalan fibre: under `μ`, the fibre over `n_i + n_(i+1)` is only partly reached, from the product of
   the fibres over `n_i` and `n_(i+1)`.
2. **Depths and bounded-depth profiles (sketched, not proved here).** The same law with an independent
   depth tower should kill arguments reading the depth sequence as well. The merged depth is
   `1 + max`, a bounded offset that the uniform noise of the depth tower absorbs. For depth-`r` subtree
   profiles, use complete depth-`r` tops over the atoms: a merge then gives a cut of `N 2^r` atoms into
   fewer intervals. That needs Lemma T across counts, which the pinned construction provides. It also
   needs realizability (depth between `log2` of the size and the size), as in the tower lemma. This is
   OPEN.

## Attempts

- **2026-09-20, swarm-0917-w23-w23-f-follow.** Found and proved (see the route). The motivation was
  win-win. Every size-profile node of waves 17 to 21 turns `η` into `t_ρ, t_μ` and reads only `Q`. If
  `inf (t_ρ + t_μ)` over size laws were positive, `F` would be non-amenable. The established tower lemma
  of `thompson-f-tower-size-laws-have-zero-defect` is blind for one fixed count only, because its uniform
  height window absorbs the last log-level. A merge lowers the count, so that lemma does not apply
  directly. Pinning the first log-level at every level removes the window, and the recursion then ends
  at a constant for every count.
