---
rg: 2
id: higman-host-coset-soficity-makes-compiler-rope-sofic
kind: claim
title: On INF the compiler rope R_e is sofic once the Higman host acts soficly on the cosets of the finite-index subgroups of the embedded bridge
artifacts:
  - research/higman-host-coset-soficity-makes-compiler-rope-sofic-proof.md
distinct_from:
  hub-incidence-color-code-makes-edge-coset-action-sofic: that reduces the edge coset action to an abstract incidence code (HC) on K_e; this builds (HC_e) from coset models of the Higman host and so removes K_e, M_e and the graph witness from the problem.
  compiler-rope-edge-is-not-co-amenable: its (R3) makes the first rope Gamma_e sofic from the two-sided host action; this handles the edge coset action and hence the twisted rope R_e itself.
  first-rope-edge-coset-action-is-sofic: that is the open edge statement; this derives it from a statement about H_e alone.
  envelope-coset-action-sofic-once-edge-coset-action-sofic: that passes from the edge coset action to R_e; this supplies the edge coset action.
---

ESTABLISHED (unreviewed). Full proof in the artifact. Soficity of an action is
GKP Definition 2.1(5).

**Data** (items 3--7 of `research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`),
on `INF`:

- `F = F(x,y,t)`, `q : F ->> Q_e = B3(1)` with kernel `N_e`;
- `j : Q_e -> P = F_2 x F_2`, the injective embedding of item 3;
- the Higman host `H_e = < X_e | R_e >`, `pi : F(X_e) ->> H_e`, and the Higman
  embedding `iota : Q_e -> H_e` (injective);
- `K_e = F x F(X_e) x F(X_e) x F x P`,
  `L_e = F x M_e x graph(jq)`, with `F` embedded as
  `f -> (f, w_f, 1, f, 1)` and `pi(w_f) = iota q(f)`;
- `Gamma_e = < K_e, v | [v, L_e] = 1 >`, `S_e = < F, F^v > = F *_(N_e) F^v`, and
  the twisted rope `R_e` of [[mf-safe-finite-presentation-compiler]].

**Hypothesis (HQ).** For every finite-index normal subgroup `J ◁ Q_e`, the coset
action

```text
H_e  ↷  H_e / iota(J)
```

is sofic.

**Theorem.** Let `e in INF` and assume (HQ). Then:

1. `H_e` is sofic, and so is `Gamma_e`;
2. `Gamma_e ↷ Gamma_e/S_e` is sofic;
3. `R_e` is sofic.

It is enough to know (HQ) along one chain `J_n = j^-1(ker r_n)`, where
`r_n : P -> C_n` are finite quotients with `∩ ker r_n = 1`.

**Proof outline** (artifact).

1. *The quotient `K_e/L_e`.* `K_e` acts on `H_e x P` by
   `(a,u,u',b,p).(h,x) = (pi(u) h pi(u')^-1, jq(b) x p^-1)`. The stabilizer of
   `x_0 = (1,1)` is `L_e`, and `F.x_0` is the **untwisted** diagonal
   `Q'' = {(iota q, j q) : q in Q_e}`. So `k in F L_e` iff `k.x_0 in Q''`.
2. *(HC_e) from a product-form relative model.* Suppose there are sofic
   approximations `sigma_n` of `H_e` on `D_n`, the quotients `r_n`, and colors
   `gamma_n` on `D_n x C_n` that are exact for `Q''` under `sigma_n x r_n`. On
   `A_n = D_n x Sym(D_n) x C_n x C_n x K_e/N_n`:
   - `u` acts on `d` through the exact extension `lambda` of `sigma_n pi`, and
     `u'` on the frame `s` by `s -> s lambda(u')^-1`;
   - `b` acts on `e` by left multiplication with `r_n jq(b)`, and `p` on the
     frame `t` by `t -> t r_n(p)^-1`;
   - `K_e` acts on the last coordinate by right translation.

   Then `zeta = (s(d), t e)` is exact for `L_e`, and
   `omega = (gamma(d,e), s, t, z F_n)` is exact for `F`. The relation
   `gamma(s^-1 zeta_1, t^-1 zeta_2) = gamma(d,e)` decides `k in F L_e`. This is
   (HC_e), so [[hub-incidence-color-code-makes-edge-coset-action-sofic]] gives
   item 2.
3. *The relative model from (HQ).* `H_e x C_n ↷ (H_e x C_n)/Q''_n` has orbits
   `H_e/iota(J_n)` with finite multiplicity. Let `phi, delta` be a one-color code for
   `H_e/iota(J_n)`, and write `e = r_n j(q_e) tau(e)` along a right transversal of
   `r_n j(Q_e)` in `C_n`. Then the color
   `gamma(beta, e) = ( delta(phi(iota q_e)^-1 beta), tau(e) )` is exact for
   `Q''_n`. A diagonal extraction over `n` gives step 2's data. The models
   `phi` are free a.e., because `delta` moves off `iota(J_n)` and `∩ iota(J_n) = 1`.
   So `H_e` is sofic.
4. *Assembly.* [[free-cover-left-right-action-over-sofic-group-is-sofic]] with (R3) of
   [[compiler-rope-edge-is-not-co-amenable]] gives `Gamma_e` sofic, and
   [[envelope-coset-action-sofic-once-edge-coset-action-sofic]] gives `R_e`.

## Consequences

- **Where a nonsoficity proof must live.** If some `R_e` (`e in INF`) is
  nonsofic, then for some finite-index `J ◁ B3(1)` the Higman host acts
  nonsoficly on `H_e / iota(J)`. The lamps, the hub `K_e`, the Mikhailova
  subgroup `M_e`, the graph witness and the twist all drop out. A heretic proof
  of [[compiler-positive-rope-is-not-sofic]] is therefore a proof that a
  specific finitely presented group, which contains the residually finite group
  `B3(1) = (F_oo x F_oo) x| Z`, has a nonsofic coset action on a finite-index
  subgroup of that copy.
- **Positive route.** Conversely, `SOFIC_fp` is `Pi^0_2`-complete
  ([[sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group]]) as soon as
  every host `H_e` with `e in INF` satisfies (HQ). These are the hosts that the
  explicit Higman construction ([[mikaelian-explicit-higman-embedding]]) outputs
  for the recursive presentations of `B3(S_c)` on `INF`. So the positive branch
  becomes a permanence question: does soficity of coset actions survive the
  HNN and amalgam steps of that construction? Only `INF` matters.
- **Not claimed.** The converse (that soficity of `R_e` forces (HQ)) is open.
  Whether (HQ) for `J = Q_e` alone implies (HQ) is also open.
