---
rg: 2
id: mapping-torus-radical-is-pseudo-orbit-recurrence
kind: claim
title: The MF radical of a finitely presented automorphic mapping torus is exactly the set of kernel elements at which no substitution pseudo-orbit of quasi-solutions of the finite kernel relators recurs, in any dimension
distinct_from:
  mf-kazhdan-quotientless-mapping-torus-exact-radical: its Attempt 1 periodizes exact orbits rho o psi^j of one almost-representation and dies because rho must be accurate on balls of radius lambda^J; this proves an if-and-only-if in which each step is re-projected onto quasi-solutions of the finite relator set R_0, so ball accuracy is never needed and the pigeonhole closing is the whole content of MF approximation of G.
  kazhdan-regular-block-periodizations-of-mapping-tori-are-finite: that shows regular finite-quotient block models below a wrap constant are genuine; this characterises all MF approximations of G by arbitrary (not block-regular) pseudo-orbits, with the cyclic shift as the only wrap.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that builds a tracial model with a Folner wrap of weight 1/N; this is the operator-norm criterion, where the wrap is closed by compactness of U(d)^S instead of by small trace.
  mapping-torus-mf-radical-descends-through-kernel-radical: that reduces to the kernel quotient Q = K/Rad_MF(K); this is a criterion stated only through the finite presentation of G, valid for every kernel.
artifacts:
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/kazhdan-regular-block-periodizations-of-mapping-tori-are-finite.md
---

**ESTABLISHED (unreviewed).** Proof: `mapping-torus-radical-is-pseudo-orbit-recurrence-proof`.
Elementary: compactness of `U(d)`, a cyclic block shift, and the corona definition of `Rad_MF`.

## Setting

Let `G = K ⋊_ψ Z` be finitely presented. As recorded in
`kazhdan-regular-block-periodizations-of-mapping-tori-are-finite` (from
`fp-mapping-torus-iff-finite-automorphic-presentation`), `G` has a presentation

```text
G = < S, t | R_0 ,  t s t^-1 = w_s  (s in S) >,   S generates K,  R_0 ⊂ F_S finite,  w_s ∈ F_S.
```

Fix a word `g ∈ F_S` (an element of `K`). For `d ≥ 1` put `X_d = U(d)^S`, with the metric
`‖b − b'‖ = max_s ‖b(s) − b'(s)‖` (operator norm). A word `v ∈ F_S` evaluates to `v(b) ∈ U(d)`.

- **Substitution map.** `W_d : X_d -> X_d`, `W_d(b)(s) = w_s(b)`. It is continuous (polynomial
  in the entries).
- **Quasi-solutions.** `Q_ε = { b : ‖r(b) − 1‖ ≤ ε for all r ∈ R_0 }`, closed.
- **Nontrivial at g.** `N_δ(g) = { b : ‖g(b) − 1‖ ≥ δ }`, closed.
- An **(ε, δ)-chain** in dimension `d` is `b_0, ..., b_L ∈ Q_ε ∩ N_δ(g)` with
  `‖b_(j+1) − W_d(b_j)‖ ≤ ε` for `j < L`. It is **infinite** if it is indexed by `j ∈ N`.
- `N(d, ε)` is the least number of closed `ε`-balls covering `X_d`. It is finite, and at most
  `(C/ε)^(|S| d^2)`.

## Statement

For `g ∈ K`, the following are equivalent.

1. `g ∉ Rad_MF(G)`.
2. There is `δ > 0` such that for every `ε > 0` there are `d` and an infinite `(ε, δ)`-chain in
   dimension `d`.
3. There is `δ > 0` such that for every `ε > 0` there are `d` and an `(ε, δ)`-chain in dimension
   `d` of length `L + 1 > N(d, ε)`.
4. There is `δ > 0` such that for every `ε > 0` there are `d` and a nonempty closed
   `Y ⊆ Q_ε ∩ N_δ(g) ⊆ X_d` with `W_d(Y) ⊆ Y_ε` (the closed `ε`-neighbourhood).

**Corollary (witness form).** `Rad_MF(G) = K` exactly when, for every `g ∈ K \ {1}` and every
`δ > 0`, there is `ε > 0` such that in every dimension `d`:
- every `(ε, δ)`-chain has length at most `N(d, ε) ≤ (C/ε)^(|S| d^2)`;
- equivalently, no nonempty closed subset of `Q_ε ∩ N_δ(g)` is `ε`-almost invariant under `W_d`.

So the flagship `torsion-free-sofic-exact-mf-radical-over-z` and `(XMF)` of
`mf-kazhdan-quotientless-mapping-torus-exact-radical` are statements about one explicit polynomial
map `W_d` per dimension, on compact semialgebraic sets cut out by the finite set `R_0`. No
conjugating unitary appears: the cyclic shift is the only wrap.

## What this changes

- **The Attempt 1 death was an artifact of exact orbits.** Periodizing `rho o psi^j` of a single
  almost-representation needs `rho` accurate on balls of radius `lambda^J`, with `J` the pigeonhole
  time. A chain instead re-projects onto `Q_ε` at every step, and only the finite set `R_0` is
  ever tested. So Attempt 1 does not show that periodization cannot prove MF of a mapping torus.
  By 1 ⇔ 3 it is the universal method: every MF approximation of `G` nontrivial on `K` is a
  closed chain after one pigeonhole.
- **Exact form of the witness obligation.** A witness must make `W_d` *uniformly transient* on
  the `δ`-nontrivial quasi-solutions: one `ε = ε(g, δ)` for all dimensions `d`, with every
  `(ε, δ)`-chain shorter than the covering number of `U(d)^S`. The bound is dimension-dependent,
  but the scale `ε` is not.
- **Arithmetic shape.** For fixed `(g, δ, ε, d)` and an explicit `M ≥ N(d, ε)` (Step 3 of the
  proof works with any such `M`), "an `(ε, δ)`-chain of length `M + 1` exists" is a first-order
  statement over the reals, hence decidable by Tarski. So, for a
  concrete finite presentation, `Rad_MF(G) = K` reads as `∀ g ∀ δ ∃ ε ∀ d` applied to a decidable
  predicate. Every finite computation can refute the witness property only at one `(ε, d)`, and
  can confirm it only at one `(g, δ, ε)` and finitely many `d`.
- **Tracial contrast.** In the Hilbert--Schmidt analogue the wrap step in Step 3 of the proof
  costs weight `1/m`, and no pigeonhole is needed. That is why
  `kazhdan-mapping-tori-have-proper-stably-finite-radical` closes and this criterion does not
  automatically.

## Not claimed

- No example either way. The criterion does not decide the flagship, and it does not decide
  `(XMF)`.
- It does not give an intrinsic (`ψ`-free) condition on `K`. `W_d` depends on the words `w_s`.
