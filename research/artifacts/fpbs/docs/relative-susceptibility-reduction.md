# Benjamini–Schramm through an amenable wq-normal subgroup

September 11, 2026 (lane bs-1). The target is `p_c(G) < p_u(G)` for every
Cayley graph `G = Cay(Gamma,S)` of a nonamenable finitely generated group. This
note proves one reduction for the class of groups having an infinite amenable
wq-normal subgroup, isolates the single analytic premise that remains, and
records three attempts on that premise and where each stops. Nothing here is
refereed or formally verified.

## 1. Imported relative theorems

Hutchcroft and Pan, *Percolation at the uniqueness threshold via subgroup
relativization*, [arXiv:2409.12283v1](https://arxiv.org/abs/2409.12283), read
from the PDF on 2026-09-11. `G` is a Cayley graph of a finitely generated group
`Gamma`, `H <= Gamma` is a subgroup, `K_o` is the cluster of the identity, and a
cluster `K` is *H-infinite* when `|K ∩ H| = infinity`. Definition 1.2 sets

    p_c(H;G) = inf{p : there is an H-infinite cluster a.s.},
    p_u(H;G) = inf{p : there is a unique H-infinite cluster a.s.}.

* **Theorem 1.4 (uniqueness and long-range order).** For `H` infinite and each
  `p`, there is a unique H-infinite cluster a.s. if and only if
  `inf_{x,y in H} tau_p(x,y) > 0`.
* **Theorem 1.7 (relative Burton–Keane).** If `H` is amenable then for every
  `p` there is at most one H-infinite cluster a.s. In particular
  `p_c(H;G) = p_u(H;G)`.
* **Theorem 1.8 (relative sharpness).** For each `p < p_c(H;G)` there is
  `c(p) > 0` with `P_p(|K_o ∩ H| >= n) <= exp(-c n)` for every `n >= 1`.
* **Proposition 1.9.** If `H_1 <= H_2 <= Gamma` and `H_1` is s-normal in `H_2`,
  then for each `p` there is a unique `H_1`-infinite cluster a.s. if and only if
  there is a unique `H_2`-infinite cluster a.s. In particular
  `p_u(H;G) = p_u(G)` for `H` s-normal in `Gamma`.
* **Proposition 1.10.** The same holds with s-normal replaced by wq-normal.
  (The v1 text says "Proposition 1.8 remains true"; the statement it modifies is
  the s-normal proposition 1.9, and the surrounding paragraph makes this clear.)

`H` is s-normal when `|sH ∩ Hs| = infinity` for every `s`; wq-normal (Popa)
when every intermediate subgroup `H <= I < Gamma` has some `g` outside `I` with
`g I g^(-1) ∩ I` infinite. Infinite normal subgroups and commensurated
subgroups are s-normal, and s-normal subgroups are wq-normal.

## 2. The uniqueness threshold is a relative critical threshold

**Proposition 2.1.** Let `H` be an infinite amenable wq-normal subgroup of
`Gamma`. Then `p_u(G) = p_c(H;G)` for every Cayley graph `G` of `Gamma`.

*Proof.* Theorem 1.7 gives `p_c(H;G) = p_u(H;G)`. Proposition 1.10 with
`H_1 = H` and `H_2 = Gamma` gives uniqueness of the H-infinite cluster exactly
when the Gamma-infinite cluster is unique; a Gamma-infinite cluster is an
infinite cluster, so `p_u(H;G) = p_u(G)`. QED.

## 3. Threshold separation equals finite relative susceptibility

Write `chi^H_p = E_p|K_o ∩ H| = sum_{h in H} tau_p(o,h)` for the relative
susceptibility.

**Theorem 3.1.** Let `H` be an infinite amenable wq-normal subgroup of
`Gamma` and `G = Cay(Gamma,S)`. The following are equivalent.

1. `p_c(G) < p_u(G)`.
2. There is `p > p_c(G)` with `chi^H_p < infinity`.
3. There are `p > p_c(G)` and `c > 0` with `P_p(|K_o ∩ H| >= n) <= e^(-cn)`
   for all `n`.

*Proof.* (1 ⇒ 3) By Proposition 2.1, `p_u(G) = p_c(H;G)`. Choose
`p_c(G) < p < p_c(H;G)`; Theorem 1.8 gives the exponential tail.
(3 ⇒ 2) Sum the tail. (2 ⇒ 1) Finite expectation gives `|K_o ∩ H| < infinity`
almost surely. For `h in H`, left multiplication by `h` is a graph automorphism
preserving the Bernoulli law and the set `H`, and it sends `K_o ∩ H` to
`K_h ∩ H`, so every `|K_h ∩ H|` is finite a.s. An H-infinite cluster contains
some `h in H` with `|K_h ∩ H| = infinity`; by countability none exists a.s. The
existence of an H-infinite cluster is increasing in `p` and a 0-1 event, so
`p <= p_c(H;G) = p_u(G)`, while `p > p_c(G)`. QED.

The proof uses nonamenability of `G` nowhere. For amenable `Gamma` the
equivalent statements are all false, which is consistent: there `p_c = p_u`.

**Examples of the class.** Every group with an infinite amenable normal
subgroup, hence: groups with infinite center (braid groups `B_n`, `n >= 3`;
irreducible spherical Artin groups; `Gamma x Z^k`); fundamental groups of
Seifert-fibred 3-manifolds with hyperbolic base orbifold, whose fibre subgroup
is infinite cyclic and normal; lamplighters `L wr Gamma` with `L` amenable;
`Z^d x| SL_d(Z)`. Commensurated amenable subgroups also qualify, e.g. `<a>` in a
non-solvable Baumslag–Solitar group `BS(m,n)`. Acylindrically hyperbolic groups
have no infinite amenable normal subgroup, so the groups with such a normal
subgroup lie outside Choi–Seo arXiv:2508.08932. For `Seifert-fibred` groups this
is Choi–Seo's own Question 1.6, and `F_2 x Z` is their Question 1.3.

## 4. The remaining premise, and three attempts

**Premise (relative subcriticality).** For every nonamenable finitely
generated `Gamma` with an infinite amenable wq-normal subgroup `H`, and every
finite generating set, `chi^H_p < infinity` for some `p > p_c(G)`.

### 4.1 Path counting reproduces the classical bound only

For `H` normal, a union bound over open walks gives

    chi^H_p <= sum_l (p d)^l P(X_l in H) = sum_l (p d)^l q_l(e,e),

where `X` is simple random walk on `G`, `d = |S|`, and `q_l(e,e)` is the
return probability of the projected walk on `Q = Gamma/H`, at most
`rho(Q)^l`. So `chi^H_p < infinity` whenever `p d rho(Q) < 1`. By Kesten,
`rho(Q) = rho(G)` because `H` is amenable, so this is exactly the classical
Benjamini–Schramm lower bound `p_u >= 1/(d rho)` and certifies only graphs
where `p_c < 1/(d rho)`, which are already known.

### 4.2 The mean-field prediction

For a critical branching random walk with mean offspring one, the expected
occupation of a vertex set is the Green function of the walk summed over that
set. Summed over `H` this is `sum_l q_l(e,e) <= 1/(1 - rho(Q)) < infinity`,
because the quotient is nonamenable. So mean-field heuristics predict
`chi^H_(p_c) < infinity`, and Theorem 3.1 then needs only a small interval above
`p_c`. This is a heuristic: the comparison with branching random walk is the
triangle-condition input that is itself open.

### 4.3 Hutchcroft's criterion meets the same quantity

Hutchcroft's sufficient condition (arXiv:1804.10191, Proposition 2.7; recast as
Choi–Seo Theorem 2.5) needs `iota_p -> 1`, i.e. for every finite `A`,
`sum_{g,h in A} tau_p(g,h) = o(chi_p |A|)`. For `H = <z>` central and `A` a long
segment `{z^k : 0 <= k <= L}`, the ratio tends to `chi^H_p / chi_p` as
`L -> infinity`. So on fibre-concentrated sets the two approaches ask for the
same thing, `chi^H_p = o(chi_p)` as `p` increases to `p_c`. Choi–Seo Section
2.3 shows that Hutchcroft's halfspace hypothesis (their Theorem 2.9) fails for
`F_2 x Z` on exactly these sets. Their WPD remedy is unavailable when `H` is
infinite amenable normal.

### 4.4 Openness does not come for free

If `{p : chi^H_p < infinity}` were open, relative subcriticality would follow
from `chi^H_(p_c) < infinity` alone. The sprinkling bound of arXiv:1804.10191
Lemma 2.4 gives

    T_(p') <= sum_k [((p'-p)/(1-p)) T_p A]^k T_p.

Summing its `(o,H)` row involves `sum_u tau_p(o,u) sigma_p(u)`, where
`sigma_p(u) = sum_{h in H} tau_p(u,h)` is the mass on the coset of `u`. That is
a quadratic sum over cosets (a quotient bubble), not a multiple of
`chi^H_p`. For `H` normal the function `u -> sigma_p(u)` is positive definite on
the quotient (it is the pushforward of the positive-definite `tau_p`), so
`sigma_p(u) <= chi^H_p`; but the remaining sum over cosets still needs an ℓ²
bound on the coset operator, an L2-boundedness-type input. The diagonal entry
alone does not control it.

## 5. Dangling bridges under uniqueness (supporting lemma)

**Lemma 5.1.** Let `G` be connected, locally finite and quasi-transitive, and
let `p in (0,1)` with a unique infinite cluster `C` a.s. Then almost surely every
open edge whose removal disconnects `C` leaves exactly one infinite side.
Consequently, for `o, x in C`, every open edge pivotal for `{o <-> x}` is a
bridge of `C` whose finite side contains `o` or `x`, and
`N_(o<->x) <= N_o + N_x`, where `N_v` counts the bridges of `C` with `v` on the
finite side. This bound does not depend on the distance between `o` and `x`.

*Proof.* For an edge `e` let `A_e` be the event that `e` is open and `C \ e`
has two infinite components. Closing `e` maps `A_e` into the event of at least
two infinite clusters, and deletion tolerance gives
`P(N_infinity >= 2) >= ((1-p)/p) P(A_e)`. Uniqueness forces `P(A_e) = 0`; take
the union over the countably many edges. If `e` is pivotal for `o <-> x` with
both endpoints in `C`, closing `e` separates `o` from `x`, so `e` disconnects
`C`, and the side that is finite contains `o` or `x`. QED.

**Where this stops.** Integrating Russo's formula for `log tau_s(o,x)` from
`p_c` with this bound costs the conditioning factor `tau_s(o,x)^(-1) <=
theta(s)^(-2)`, and the resulting integrand is not integrable at `p_c` under
mean-field behaviour. Russo's formula also has to be applied to finite-volume
events, whose pivotal edges need not be dangling bridges. So the lemma gives no
route by itself.
