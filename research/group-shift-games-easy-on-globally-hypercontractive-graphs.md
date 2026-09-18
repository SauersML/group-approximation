---
rg: 2
id: group-shift-games-easy-on-globally-hypercontractive-graphs
kind: claim
title: Bafna--Minzer Theorems 1.6--1.8 hold verbatim for left-shift games x_v = b_e x_u over every finite group, abelian or not, once differences are read as right quotients X_u^-1 X'_u and global shifts as right multiplication
distinct_from:
  affine-ug-easy-on-globally-hypercontractive-graphs: that is the imported theorem for Z_q shifts; this is its extension to every finite group, which that theorem does not state.
  general-unique-games-easy-on-globally-hypercontractive-graphs: that is the question for arbitrary permutation constraints; this is its group-shift form, which implies it through unique-games-lift-to-group-shift-games-on-the-same-host.
  unique-games-reduce-to-shifts-over-their-holonomy-group: that transfers the cyclic case to all cyclic-holonomy games; this is about the algorithm itself for non-cyclic alphabet groups.
artifacts:
  - experiments/ugc-coset-lift-2026-09-17/check_coset_lift.py
  - experiments/ugc-coset-lift-2026-09-17/output.txt
---

**OPEN.** An audit of the full proof, listed under Attempts, found no
obstruction. What is still missing is an independent line-by-line referee of
Sections 3.3--3.5 and 4.1--4.2 of Bafna--Minzer. Those sections are argued
below to be alphabet-agnostic.

**Claim.** Let `A` be a finite group, `alpha in (0, 1)` and `c > 0`. There is
`delta = delta(alpha, c) > 0` such that the following holds on each host family
below. There is an algorithm running in time `n^D` with
`D = l^(poly(|A| l^(1/c)))`. On every left-shift game `x_v = b_e x_u`,
`b_e in A`, of value `>= c`, it returns a labeling of value `>= delta`. The
host families are:

* `J(n, l, alpha l)`;
* `Grass(n, l)`;
* the depth-`alpha` canonical walk on `X(l)` of a two-sided
  `gamma`-local-spectral expander, as in Theorem 1.8.

This is Bafna--Minzer (arXiv:2304.07284) Theorems 1.6, 1.7 and 1.8, with
"affine UG instance" (their Definition 1.4, alphabet `Z_q`, maps
`sigma -> sigma + b_e`) replaced by left shifts over `A`.

**Consequence.** Together with the ESTABLISHED
`unique-games-lift-to-group-shift-games-on-the-same-host` (item 5), this
claim implies `general-unique-games-easy-on-globally-hypercontractive-graphs`:
every unique game with alphabet `k` and value `>= c` on these hosts gets a
labeling of value `>= min_A delta(alpha, c/k!)` in time
`n^(l^(poly(k! l^(k!/c))))`. The route is
`general-ug-on-bm-hosts-from-group-shift-games`.

## The dictionary (proved here)

Write `A` multiplicatively. `X_(u,a)` is the Boolean indicator variable of
program (1), with `sum_a X_(u,a) = 1`. Let
`Y_e(X) = sum_a X_(u,a) X_(v, b_e a)` be the indicator that `e = (u, v)` is
satisfied. Let `val_v(X)` be the local value at `v`. The replacements are:

| Bafna--Minzer / BBKSS (`Z_q`) | here (group `A`) |
|---|---|
| `Z_(u,s) = sum_a X_(u,a) X'_(u,a+s)`, "`X'_u - X_u = s`" | `Z_(u,s) = sum_a X_(u,a) X'_(u,a s)`, "`X_u^(-1) X'_u = s`" |
| `I[X_v - X_u = s] = sum_a X_(u,a) X_(v,a+s)` | `I[X_v X_u^(-1) = s] = sum_a X_(u,a) X_(v,s a)` |
| global shift `X -> X + s` | right translation `X -> X s` |
| condition on `X_u = 0` | condition on `X_u = e` |
| random affine constraint `b_e in Z_q` | uniform `b_e in A` |

All the new indicators have the same degree as the old ones.

**Lemma D.** Let `I` be a left-shift game over `A`. Let `mu` be a degree-`D`
pseudodistribution satisfying the axioms `A_I` of program (1).

1. *(Partition, Fact 2.10 (1)--(2).)* `Z_(u,s)^2 = Z_(u,s)`,
   `Z_(u,s) Z_(u,s') = 0` for `s != s'`, and `sum_s Z_(u,s) = 1`, modulo `A_I`.
2. *(Crossing edges violate, Fact 2.10 (3).)*
   `Z_(u,s) Z_(v,t) Y_e(X) Y_e(X') = 0` for every edge `e = (u, v)` and every
   `s != t`, modulo `A_I`.
3. *(Symmetrization, Definition 2.11 and BBKSS Lemma 3.8.)* Define `mu.t` by
   `E_(mu.t)[prod_i X_(u_i, a_i)] = E_mu[prod_i X_(u_i, a_i t^(-1))]`, and let
   `mu^sym` be the average of `mu.t` over `t in A`. Then `mu^sym` is a valid
   degree-`D` pseudodistribution satisfying `A_I`, with the same value. It
   agrees with `mu` on every right-invariant polynomial. It has uniform
   marginals: `Pr[X_u = a] = 1/|A|`.
4. *(BBKSS Lemma 3.9.)* Suppose `mu = mu^sym`, `u, v in V`, `s in A`, and `f`
   is right-invariant with `deg f <= D - 2`. Then
   - (i) `Pr[X_v = s | X_u = e] = Pr[X_v X_u^(-1) = s]`;
   - (ii) `E[f | X_v X_u^(-1) = s] = E[f | X_u = e, X_v = s]`.

   Each `val_v` is right-invariant.
5. *(The identity behind BM eq. (23) and BBKSS Lemma 3.5.)* Modulo `A_I`,
   `sum_s Z_(u,s) Z_(v,s) = sum_s I[X_v X_u^(-1) = s] I[X'_v X'_u^(-1) = s]`.
6. *(Condition&Round, BBKSS Lemma 3.6 and BM Lemma 3.29.)* Let `mu` be
   shift-symmetric in the sense of item 3, with degree `>= 4`. Define
   `Psi(mu) = E_(u,v ~ pi) sum_s Pr[X_v X_u^(-1) = s]^2 E[val_v | X_v X_u^(-1) = s]`.
   Condition on `X_u = e` for `u ~ pi`, then round each vertex independently
   from its conditional marginal. The expected value of the result is
   `>= Psi(mu)`.
7. *(Randomized constraints, BM Claim A.4.)* If `b_e` is uniform in `A`, then
   every fixed labeling satisfies `e` with probability exactly `1/|A|`.
8. *(Potential invariance.)* Take `F_s(u) = Z_(u,s) p(val_u(X)) p(val_u(X'))`
   as in BM Definition 3.2. Then
   `Phi(X, X') = sum_s (E_u F_s(u))^2` is invariant under `X -> X t` and
   `X' -> X' t'`, because these permute the index `s`. Hence
   `Phi(mu_1^sym x mu_2^sym) = Phi(mu_1 x mu_2)`.

**Proofs of Lemma D.** Throughout, `A_I` contains `X_(u,a)^2 = X_(u,a)`,
`X_(u,a) X_(u,a') = 0` for `a != a'`, and `sum_a X_(u,a) = 1`. So every product
of indicators reduces, modulo `A_I`, to a sum of monomials indexed by
consistent assignments of the variables it mentions. An identity between such
polynomials holds modulo `A_I` as soon as it holds on every Boolean assignment
of those variables. That is the case for items 1, 2 and 5, which are identities
among polynomials of degree at most 8 in at most four vertices.

1. On an assignment, `Z_(u,s) = [X_u^(-1) X'_u = s]`, and exactly one `s`
   satisfies this.
2. If `Y_e(X) Y_e(X') = 1` then `X_v = b_e X_u` and `X'_v = b_e X'_u`, so
   `X_v^(-1) X'_v = X_u^(-1) b_e^(-1) b_e X'_u = X_u^(-1) X'_u`, which forces
   `s = t`.
3. `mu.t` is the pushforward of `mu` under the variable relabeling
   `X_(u,a) -> X_(u,a t^(-1))`. That relabeling maps the axioms to themselves,
   because `x_v = b_e x_u` iff `x_v t = b_e (x_u t)`. So `mu.t` is a
   pseudodistribution of the same degree satisfying `A_I`, with the same value,
   and so is the convex combination `mu^sym`. A right-invariant polynomial has
   the same expectation under every `mu.t`. The marginal of `X_u` under
   `mu^sym` is the average of the right translates of one distribution on `A`,
   hence uniform.
4. By right invariance of `mu`, translating by `t = a^(-1)` gives
   `Pr[X_u = a, X_v = s a] = Pr[X_u = e, X_v = s]`, and the same with `f`
   inserted, since `f` is right-invariant. Summing over `a`,
   `Pr[X_v X_u^(-1) = s] = |A| Pr[X_u = e, X_v = s]`. Item 3 gives
   `Pr[X_u = e] = 1/|A|`, which proves (i). For (ii), divide the two sums.
   `val_v` is right-invariant because `x_w = b x_v` is.
5. For group elements, `a^(-1) a' = b^(-1) b'` iff `b a^(-1) a' = b'` iff
   `b a^(-1) = b' a'^(-1)`. The two sides count the same set of quadruples
   `(X_u, X'_u, X_v, X'_v)`.
6. This follows BBKSS Lemma 3.6 word for word. After conditioning on
   `X_u = e`, the rounded labeling satisfies the edge `(v, w)` with probability
   `sum_s Pr[X_v = s | .] Pr[X_w = b s | .]`. This is at least
   `sum_s Pr[X_v = s | .] Pr[X_v = s, X_w = b s | .]`. Averaging over `w` gives
   `sum_s Pr[X_v = s | .]^2 E[val_v | X_u = e, X_v = s]`. Item 4 then turns it
   into the summand of `Psi`. The only property used is the one-to-one
   correspondence `s -> b s`, which holds in every group.
7. For fixed `x_u` and `x_v`, exactly one `b in A` satisfies `x_v = b x_u`.
8. Under `X -> X t`, `Z_(u,s) -> Z_(u, t s)`; under `X' -> X' t'`,
   `Z_(u,s) -> Z_(u, s t'^(-1))`. `val_u` is invariant under both (item 4).
   So `F_s` is permuted in `s`, and `Phi` is a symmetric function of the
   `E_u F_s(u)`.

The artifact `check_coset_lift.py`, Part B, verifies the following exactly,
with rational arithmetic, over `S_3` and the quaternion group `Q_8`:

* items 3, 4 and 6 on explicit distributions (B1--B3, B6);
* the identities behind items 2, 5 and 7 over the whole group (B4, B5, B7);
* control B8: the wrong-sided difference `a a'^(-1)` is not invariant under a
  common left shift, so the side conventions above are forced.

Real distributions are a special case of pseudodistributions, so this is a
sanity check of the algebra, not of the SoS degree bookkeeping.

## Attempts

* **2026-09-18, swarm-0917-w10-w10-ugc-break (reframing).** I audited every
  place where Bafna--Minzer (arXiv:2304.07284) or BBKSS (arXiv:2006.09969)
  uses the algebra of the alphabet. Each one transfers.

  | location | use of `Z_q` | status for group `A` |
  |---|---|---|
  | BM Fact 2.10 (1)--(3), page 17 | shift partition, crossing edges violate | Lemma D items 1--2 |
  | BM Definition 2.11; BBKSS Lemma 3.8 | symmetrization over global shifts | item 3 (right translation) |
  | BBKSS Lemma 3.9 | invariance under `t = a^(-1)` | item 4 |
  | BBKSS Lemma 3.5; BM eq. (23) | `a' - a = b' - b` iff `b - a = b' - a'` | item 5 |
  | BBKSS Lemma 3.6; BM Lemma 3.29 | Condition&Round bound `Psi` | item 6 |
  | BM Definitions 3.2--3.3 and the potential near line 2474 | `F_s`, `Phi`, `Psi` invariance | item 8 |
  | BM Algorithm 3.4 step (e); Algorithm A.2 (c); Claim A.4 | random constraints `b_e` | item 7 |
  | BM Lemmas 3.11, 3.12, 3.26 | hypercontractivity of `F_s` on the host | host only; `F_s` enter as generic degree-bounded functions of the vertex |
  | BM Section 4 and Section 5.1 | edge-covering theorem, shift partition | host only |
  | BM Appendix C | characters of `Z/nZ` | characters of the host approximations to `J(n, l)`, not of the alphabet |

  *Not yet refereed.* BM Sections 3.3--3.5 and 4.1--4.2 are the global
  hypercontractivity and iteration arguments. They are stated for arbitrary
  functions `F_s(u)` and local tuples `Y_(u,v)`. On my reading they never
  inspect the alphabet beyond items 1--8, but I have not checked them line by
  line. That check is what would make this claim ESTABLISHED. The exponent
  `|Sigma|` in `D` becomes `|A|` throughout.

  *Falsifier.* A line of those sections that uses commutativity of the
  alphabet: for example, an identity `Z_(u,s) Z_(u,s') = Z_(u,s+s')`-type
  composition of two shift partitions, or a Fourier expansion over `Z_q` of
  the labels. With left shifts, composition becomes
  `X_u^(-1) X''_u = (X_u^(-1) X'_u)(X'_u^(-1) X''_u)`, which is still a group
  law, so even that would transfer unless it commutes two factors.
