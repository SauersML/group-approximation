---
rg: 2
id: past-conditioned-domination-holds-on-locally-amenable-orders
kind: claim
title: Past-conditioned domination D holds for every code on every amenable left-ordered group, and on every left-ordered group whose finite ordered patterns map order-preservingly into amenable left-ordered groups, including every central-series order and the Magnus order on free groups
distinct_from:
  every-group-has-positive-rokhlin-entropy-action: the root records D (Attempts entry "Past-conditioned domination", swarm-0917-w5-pull-gs-4) as OPEN, proved only for linear codes, and leaves nonlinear codes on F_2 open; this proves D for all codes on F_2 in the Magnus order and on every amenable left-ordered group.
  rokhlin-window-transport-is-dominated: that is the random-order transport normal form with constant 1, for every group; this is the deterministic-order past-conditioned inequality D, proved only on amenable-realizable ordered patterns.
  torsion-free-windows-have-minimal-shannon-certificates: that asks for Shannon certificates on a configuration's own window; this proof is not a window certificate, since it uses the Kieffer-Pinsker formula of the whole amenable host.
  gated-diagonal-linear-deficits-force-kaplansky-failure: that controls linear gated codes through direct finiteness; this covers every code but only amenable-realizable ordered patterns.
artifacts:
  - experiments/past-conditioned-domination-2026-09-17/hxy-1409.0275-excerpts.txt
  - experiments/past-conditioned-domination-2026-09-17/check_d_magnus_nilpotent.py
  - experiments/past-conditioned-domination-2026-09-17/check_d_magnus_nilpotent.log
---

**ESTABLISHED.**

**Setting.** `(G, <)` is a left-ordered group, meaning `<` is invariant under left multiplication, with past
cone `Φ = {g : g < 1}`. A configuration is `(k, E, F, psi)`, with `x` iid uniform on `(A^k)^G`, `|A| = q`,
and `y_g = psi(x(ge))_(e in E)`. The inequality from the root's Attempts entry is

    D:  I(x_1 ; y_F | x_{<1}) <= H(y_1).

By the reduction recorded there, D for every finite `F` gives `Phi >= log q` for the configuration.

**Claim.**

1. **Amenable hosts.** Let `G` be amenable and left-ordered. For every code, `I(x_1 ; y_G | x_{<1}) = h(y) <= H(y_1)`,
   where `h(y)` is the Kolmogorov-Sinai entropy of the factor process `y`. Hence D holds for every finite `F`.
2. **Transfer.** Take a configuration on `(G, <)` with sites `S = FE ∪ {1}`. Suppose a homomorphism
   `φ: <E ∪ F> -> G'` into an amenable left-ordered group `(G', <')` is injective on `S`, and satisfies
   `φ(s) <' 1` iff `s < 1` for every `s in S`. Then D holds for that configuration. The D-quantity depends
   only on the ordered incidence pattern `(S, (f, e) -> fe, 1, S ∩ Φ)`.
3. **Central-series orders.** Let `G = G_1 ⊇ G_2 ⊇ ...` be a central series (`[G, G_c] ⊆ G_(c+1)`) with
   torsion-free factors and `∩ G_c = 1`. Fix orders on the factors. Put `g > 1` when the image of `g` in
   `G_d/G_(d+1)` is positive, where `d` is the last index with `g in G_d`. This is a bi-order. D holds for
   every code on `(G, <)`, because every finite pattern embeds into the nilpotent quotient `G/G_(c+1)` with
   the same rule.
4. **Free groups.** The Magnus order on `F_n` (the sign of the leading (degree, lex) coefficient of
   `μ(w) - 1` in `Z<<X_1..X_n>>`) is a central-series order, for the Magnus filtration
   `D_c = {w : μ(w) - 1` has no terms of degree `< c}`. So D holds for every code, linear or not, on `F_2`
   in the Magnus order. This closes the case the root's Attempts entry left open.

**Consequences for the D route.**
- D can fail only at an ordered finite pattern of a left-ordered group that has no order-preserving
  realization in any amenable left-ordered group.
- Every host where the route has been tested (`Z`, and `F_2` in the Magnus order) is of this realizable
  kind. There D is a theorem, so no census there can refute it. Such hosts are LEA and hence
  sofic, so the route adds nothing new on them.
- A proof of D for all left-ordered groups must work on ordered patterns beyond local amenability. A
  counterexample must be sought among left-orders that are not locally amenable-realizable.
- The equality in part 1 identifies the D gap on amenable hosts exactly: `H(y_1) - I(x_1; y_G | x_{<1}) = H(y_1) - h(y)`.

The proof is in `past-conditioned-domination-locally-amenable-proof`. It imports Theorem 3.1
of Huang-Xu-Yi, arXiv:1409.0275; verbatim excerpts are in the artifact.

**Check.** `check_d_magnus_nilpotent.py`, output in `check_d_magnus_nilpotent.log`:
- **Scope.** Exact evaluation (`q = 2`, `k = 1`) on `F_2` in the Magnus order, over 42 configurations.
  - Six windows: `E = {1,a,b}`, `{1,a,ab}`, `{1,a,ba}`, `{1,a,Ab}`, `{1,ab,ba}`, `{1,a,aba}`.
  - `F` = the three readers plus random elements of the 2-ball, with `|S| <= 16`.
- **Codes.** All 254 nonconstant Boolean `psi`, plus 60 random 2- or 3-block partitions per configuration,
  13188 cases in total.
- **Results.**
  - Violations: 0. The maximum of `I - H(y_1)` is exactly `0`, attained on reader sunflowers, where D is
    the chain rule over the window order.
  - For every configuration, the truncated Magnus map separates `S` at degree `c <= 2` and keeps every
    site's sign, as used in the transfer.

## Attempts
