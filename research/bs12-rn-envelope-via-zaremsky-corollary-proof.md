---
rg: 2
id: bs12-rn-envelope-via-zaremsky-corollary-proof
kind: route
title: Apply Zaremsky's Corollary to the persistent Cornulier–Tessera host and embed it diagonally on disjoint cones
target: bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host
requires:
  - cornulier-tessera-host-is-rational-weakly-diagonal-self-similar
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

All TeX line numbers refer to Zaremsky arXiv:2305.15176, `main.tex`, read on
MSI.

**1. Persistence.** Lemma at TeX l.249–250, verbatim: "For any self-similar
group $G\le \Aut(\tree_{d-1})$, there is a faithful, persistent, self-similar
action of $G$ on $\tree_d$. If the action on $\tree_{d-1}$ is rational then so
is the action on $\tree_d$. If the action on $\tree_{d-1}$ is weakly diagonal
then so is the action on $\tree_d$." Applied to the 9-ary action of the
required claim, it gives a faithful, persistent, rational, weakly diagonal
self-similar action of `Gamma_2` on the 10-ary tree.

**2. Zaremsky's Corollary.** TeX l.258, verbatim: "Let $G\le\Aut(\tree_d)$ be a
finitely generated, persistent, weakly diagonal, rational, self-similar group.
Then $V_d(G)$ is virtually simple by virtue of $[V_d(G),V_d(G)]$ being simple
and finite index, and there exists a quasi-retraction $V_d(G)\to G$. If $G$ is
finitely presented, then so is $V_d(G)$ and we have $\delta_G\preceq
\delta_{V_d(G)}$."
- `Gamma_2` is finitely generated and finitely presented with quadratic Dehn
  function, by the required claim.
- So `V_10(Gamma_2)` is finitely presented, `S = [V_10(Gamma_2),V_10(Gamma_2)]`
  is simple of finite index, and `n^2 ≃ δ_(Gamma_2) ≼ δ_(V_10(Gamma_2))`.
- A finite-index subgroup of a finitely presented group is finitely presented,
  and the inclusion is a quasi-isometry. Dehn functions are quasi-isometry
  invariants (Zaremsky TeX l.181). So `δ_S ≃ δ_(V_10(Gamma_2))`.

**3. Embedding the host into S.**
- **The maps ι_w.** Zaremsky TeX l.240 defines, for a word `w`,
  `ι_w : V_d(G) → V_d(G)`: `ι_w(h)` acts like `h` on the cone `C_d(w)` and
  trivially elsewhere. At TeX l.242 he uses that `ι_1` is a homomorphism, and
  the same computation works for every `ι_w`. Each `ι_w` is injective, since
  `h ≠ 1` moves some point of `C_d`, so `ι_w(h)` moves a point of `C_d(w)`.
- **Conjugacy.** TeX l.240, verbatim: "$\iota_w(h)$ is conjugate in $V_d(G)$ to
  $\iota_{w'}(h)$, via conjugation by an element of $V_d$, for any $h\in
  V_d(G)$ and any non-empty $w$ and $w'$."
- **Choosing cones.** By step 2 the abelianization `Q` of `V_10(Gamma_2)` is
  finite. Let `N = |Q|`, choose `L` with `10^L >= N`, and pick `N` distinct
  words `w_1,...,w_N` of length `L`. Their cones are pairwise disjoint.
- **The diagonal map.** Define `φ(g) = ι_(w_1)(g) ⋯ ι_(w_N)(g)` for
  `g in Gamma_2 ⊂ V_10(Gamma_2)`. The factors have disjoint supports, so they
  commute, and `φ` is a homomorphism. It is injective, since `ι_(w_1)` is.
- **φ lands in S.** By the conjugacy statement, all `ι_(w_i)(g)` have the same
  image `q` in `Q`. So `φ(g)` maps to `N·q = 0`, and `φ(g) in S`.

Hence `Gamma_2` embeds in the simple group `S`. By the required claim,
`BS(1,2) <= Gamma_2`, so `BS(1,2)` embeds in `S`.
