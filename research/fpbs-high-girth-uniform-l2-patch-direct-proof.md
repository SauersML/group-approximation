---
rg: 2
id: fpbs-high-girth-uniform-l2-patch-direct-proof
kind: route
title: Nachmias-Peres path counting plus the Benjamini-Nachmias-Peres girth bound give the uniform high-girth l2 gap with no appeal to the Baire dichotomy
target: fpbs-high-girth-uniform-l2-patch
requires: []
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
  - research/artifacts/fpbs-high-girth-uniform-l2-patch-proof-attempt-2026-09-17.md
---

Complete written proof of the target, self-contained apart from two imported
theorems quoted verbatim. Written 2026-09-19 by `swarm-0917-w18-w18-bs-last1`
(reframing). It reproduces Proposition 3.0 and Theorem 3.1 of
`research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`, which the referee lenses
2 and 3 checked line by line. It also proves every auxiliary fact that those
statements took from other notes.

## 0. Why the former route's prerequisite is not needed

The former route required `fpbs-l2-gap-baire-dichotomy`. That claim was refuted
over one sentence: that a gap failure "is never isolated in the marked-group
topology". The quantitative statement of the target, `||T_{p_c+delta}|| <= M`,
uses none of the following:

* the Baire dichotomy (Theorem 2.1 of the artifact);
* the transfinite kernel (Theorem 2.2);
* compactness of `X_{k,eta}`;
* any statement about isolated points.

The two sentences of the target that mention `X_{k,eta}` and the kernel use
only the *definitions* of `X_{k,eta}` and of the derivative `D`, which are
restated in Step 7. So the target stands on the imports and Steps 1–7 below.

## 1. Imports (verbatim)

**(BNP)** Benjamini, Nachmias and Peres, *Is the critical percolation
probability local?*, arXiv:0901.4616, Theorem 1 (`localpc`). This is quoted
from the e-print source `localpc.tex`, fetched 2026-09-17 and recorded in
Section 3 of the artifact.

> There exists an absolute constant $C>0$ such that if $G$ is a non-amenable
> regular graph with degree $d$ and girth $g$ such that the bottom of spectrum
> of $I-P$ is $\lambda_1>0$, then
> $$ p_c(G) \leq {1 \over d-1} + {C \log\big( 1 + {1 \over \lambda_1^2} \big) \over dg} \, .$$

The arXiv abstract, re-read 2026-09-19, agrees in substance: "the critical
probability for percolation on a d-regular non-amenable graph of large girth is
close to the critical probability for percolation on an infinite d-regular
tree".

**(NP)** Nachmias and Peres, *Non-amenable Cayley graphs of high girth have
$p_c<p_u$ and mean-field exponents*, arXiv:1207.1480, quoted from the e-print
source recorded in the same artifact:

> \begin{lemma} \label{nbwvssrw} For any graph $G$, vertices $x,y$ and
> $n \geq 0$ we have
> $$ \pnbw^n(x,y) \leq \sum_{j \geq n} \psrw^j(x,y) \, .$$

> since $d(d-1)^{n-1} \pnbw^n(x,y)$ is an upper bound on the number of simple
> paths of length precisely $n$ between $x$ and $y$.

Here `p_nbw^n` is the n-step law of non-backtracking walk and `p_srw^j` the
j-step law of simple random walk, on a `d`-regular graph.

*Sanity check of (NP), not used as a proof.* Lift simple random walk to the
universal cover, the `d`-regular tree. The lift is transient, and its limiting
ray starts with a uniform non-backtracking path. The lift visits the `n`-th
vertex of that ray at some time `j >= n`. Project back to `G`: the event
"`NBW_n = y`" is contained in "`X_j = y` for some `j >= n`", and a union bound
gives the lemma.

## 2. Elementary operator facts (proved here)

Let `G` be a vertex-transitive `d`-regular graph, `P` its transition operator
on `l2(V)`, and `rho = limsup_n p_n(o,o)^(1/n)`. Let `tau_q(x,y)` be the
Bernoulli(`q`) two-point function, and `T_q` the operator on `l2(V)` with that
kernel.

**(E1) Domination.** If `0 <= K <= B` entrywise and `B` is bounded on `l2`,
then `||K|| <= ||B||`. *Proof.* For every `f` and `g`,
`|<f,Kg>| <= <|f|,K|g|> <= <|f|,B|g|> <= ||B|| ||f|| ||g||`.

**(E2) Monotonicity.** `q -> tau_q(x,y)` is nondecreasing (standard
coupling), so `q -> ||T_q||` is nondecreasing, by (E1).

**(E3) `||P|| = rho`.** *Proof.*
- `p_{2n}(o,o) <= ||P||^{2n}`, so `rho <= ||P||`.
- For finitely supported `f`,
  `||P^n f||^2 = sum_{x,y} f(x) f(y) p_{2n}(x,y)`.
- By Cauchy–Schwarz and transitivity,
  `p_{2n}(x,y) = <P^n delta_x, P^n delta_y> <= p_{2n}(o,o)`.
- So `||P^n f||^2 <= ||f||_1^2 p_{2n}(o,o)`, and hence
  `limsup ||P^n f||^(1/n) <= rho`.
- By the spectral theorem for the self-adjoint `P`, the spectral measure of
  every finitely supported `f` lives on `[-rho, rho]`. These `f` are dense, so
  `||P|| <= rho`.

Consequently `||P^j|| <= rho^j` and
`||sum_{j>=n} P^j|| <= rho^n/(1-rho)` when `rho < 1`.

**(E4) Bottom of the spectrum.** `sup spec(P) <= ||P|| = rho`. So the bottom of
the spectrum of `I - P` is `lambda_1 >= 1 - rho`.

## 3. Proposition (walk-counting l2 bound, no girth hypothesis)

Let `G` be as in Section 2, with `d >= 3` and `rho < 1`. If `q >= 0` and
`r := q(d-1)rho < 1`, then

```text
||T_q|| <= 1 + (d/(d-1)) r / ((1-r)(1-rho)).
```

*Proof.*

1. For `x != y`, the event `{x <-> y}` is contained in the union, over simple
   paths from `x` to `y`, of the event that the path is open. A path of length
   `n` is open with probability `q^n`.
2. By (NP, path count), there are at most `d(d-1)^(n-1) p_nbw^n(x,y)` simple
   paths of length `n`. By (NP, Lemma `nbwvssrw`), entrywise
   `tau_q <= I + sum_{n>=1} q^n d(d-1)^(n-1) sum_{j>=n} P^j =: B`.
   This also holds on the diagonal, where `tau_q(x,x) = 1`.
3. By (E3),
   `||B|| <= 1 + sum_{n>=1} q^n d(d-1)^(n-1) rho^n/(1-rho)`, which equals
   `1 + (d/(d-1)) sum_{n>=1} r^n/(1-rho)`, which equals
   `1 + (d/(d-1)) r/((1-r)(1-rho))`.
4. The bound on `||T_q||` follows from (E1). QED.

In particular `p_{2->2}(G) >= 1/((d-1) rho)`.

## 4. The theorem

Constants as in the target:
`L(eta) = max(3, ceil(4C log(1+eta^-2)/eta))`, `M(eta) = 1 + 3/eta^2` and
`delta(k,eta) = eta/(4(2k-1))`, where `C` is the constant of (BNP). Let
`(Gamma; s_1,...,s_k)`, with `k >= 2`, have no nontrivial freely reduced word
of length `< L(eta)` trivial in `Gamma`, and suppose its simple Cayley graph `G`
has `rho <= 1 - eta`.

**Step 1 (degree and girth).** `L >= 3`, so the words `s_i`, `s_i^2` and
`s_i s_j^(+-1)` (`i != j`) are nontrivial. Hence the `2k` elements `s_i^(+-1)`
are distinct and nontrivial, and `G` is `d`-regular with `d = 2k >= 4`. It is
vertex-transitive.

A shortest cycle has no backtracking, so reading its edge labels gives a
nontrivial freely reduced word of length equal to the girth that is trivial in
`Gamma`. So the girth is `g >= L(eta)`.

**Step 2 (choice of `q`).** Put `q := (1 + 1/rho)/(2(d-1))`. We have
`rho > 0`, since `p_2(o,o) = 1/d > 0`. Then:

- `r = q(d-1)rho = (1+rho)/2 < 1`, and `1 - r = (1-rho)/2 >= eta/2`.
- Since `r <= 1`, `d/(d-1) <= 4/3 <= 3/2` and `1 - rho >= eta`, the
  Proposition gives
  `||T_q|| <= 1 + (3/2) * 1/((eta/2) * eta) = 1 + 3/eta^2 = M(eta)`.
- `q < 1`. The `d`-regular tree covers `G`, and projecting closed walks gives
  `p_n^G(o,o) >= p_n^T(o,o)`. So `rho >= rho(T_d) = 2 sqrt(d-1)/d` (Kesten).
  Hence
  `1/rho <= d/(2 sqrt(d-1)) < d - 2` for `d >= 4`, and
  `q < (d-1)/(2(d-1)) = 1/2`.

**Step 3 (margin).** `1/rho >= 1/(1-eta) >= 1 + eta`, so
`q - 1/(d-1) = (1/rho - 1)/(2(d-1)) >= eta/(2(d-1))`.

**Step 4 (BNP).** `rho < 1`, so `G` is nonamenable. This is Kesten's
criterion; on regular graphs, `rho < 1` is equivalent to a positive Cheeger
constant. By (E4), `lambda_1 >= 1 - rho >= eta > 0`. So (BNP) applies, and,
since `g >= L(eta) >= 4C log(1+eta^-2)/eta`,

```text
p_c(G) <= 1/(d-1) + C log(1 + eta^-2)/(d g) <= 1/(d-1) + eta/(4d) <= 1/(d-1) + eta/(4(d-1)).
```

**Step 5 (conclusion).** By Steps 3 and 4, with `delta = eta/(4(d-1))`,

```text
p_c + delta <= 1/(d-1) + eta/(2(d-1)) <= q.
```

By (E2) and Step 2, `||T_{p_c+delta}|| <= ||T_q|| <= M(eta)`. Here
`d = 2k`, so `delta = eta/(4(2k-1)) = delta(k,eta)`. A bounded `T_p` means
`p <= p_(2->2)`. Also `p_(2->2) <= p_u`. For `p > p_u` there is a.s. a unique
infinite cluster (uniqueness monotonicity, Häggström–Peres–Schonmann). By
Harris–FKG, `tau_p(x,y) >= theta(p)^2 > 0` for all `x, y`, so `T_p` is
unbounded on the infinite graph. So
`p_c + delta(k,eta) <= p_(2->2) <= p_u`. QED.

## 5. The clopen and kernel sentences of the target

These use only the definitions
`X_{k,eta} = {(Gamma,S) in G_k : rho <= 1 - eta}` and
`D(Y) = Y \ union{V relatively open in Y : V subseteq U_{M,delta} for some M, delta}`,
with `U_{M,delta} = {||T_{p_c+delta}|| <= M}`, as defined in Sections 1 and 2
of the artifact.

- **Clopen.** `P_{k,eta}` is the set of members in which each of the finitely
  many nontrivial reduced words of length `< L(eta)` is nontrivial. Each
  condition "`w = e`" is clopen in the Chabauty topology, so `P_{k,eta}` is
  relatively clopen.
- **Kernel.** By Section 4, `P_{k,eta} subseteq U_{M(eta),delta(k,eta)}`, and
  it is relatively open. So `D(X_{k,eta}) subseteq X_{k,eta} \ P_{k,eta}`,
  which is the finite union of the cylinders `Z_{k,eta,w}` with
  `1 <= |w| < L(eta)`.
- Every later stage `Y_alpha` (`alpha >= 1`) of the derived sequence lies in
  `Y_1 = D(X_{k,eta})`, and so does its stabilized kernel. This uses no part of
  Theorems 2.1 and 2.2 and no claim about isolated points.

## 6. Scope

This proves the target exactly as stated. It does not repair
`fpbs-l2-gap-baire-dichotomy`. The route
`fpbs-uniform-l2-gap-from-relator-cylinders` also never used the dichotomy:
the high-girth patch and finitely many cylinders cover `X_{k,eta}`, and one
takes the maximum `M` and the minimum `delta`. After this route that route
waits only on `fpbs-uniform-l2-gap-short-relator-cylinders`.
