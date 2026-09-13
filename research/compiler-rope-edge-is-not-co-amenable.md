---
rg: 2
id: compiler-rope-edge-is-not-co-amenable
kind: claim
title: The compiler rope's edge is not co-amenable and has no amenable core quotient, and the rope is sofic once the Higman host's two-sided action is sofic
distinct_from:
  compiler-rope-is-coset-wreath-of-an-a-t-menable-base: that records that no (T)-driven obstruction applies to the rope; this proves that the amenability tools do not apply either, and names the one action whose soficity would suffice.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that proves quotient models fail because the edge is not separable; this proves that amenable-image models and co-amenable induction fail too, because the edge is not co-amenable.
  amenable-base-makes-mikhailova-edge-co-amenable: that concerns an amenable Mikhailova base chosen by design; this shows the compiler's actual base, the Higman host, is never amenable, so that design cannot carry the switch.
---

ESTABLISHED (unreviewed).

**Data.** Take the compiler of [[mf-safe-finite-presentation-compiler]], using
items 3--7 of `research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`:

- `F = F(x,y,t)`, and `N_e ◁ F` with `F/N_e = Q_e = B3(S_c)`;
- a Higman host `H_e = < X_e | R_e >` containing `Q_e`;
- the Mikhailova subgroup `M_e = {(u,v) : u =_(H_e) v} <= F(X_e)^2`;
- `K_e^0 = F x F(X_e)^2` and `L_e^0 = F x M_e`;
- the graph witness `L^g = graph(F -> P) <= K^g = F x P`;
- `K_e = K_e^0 x K^g` and `L_e = L_e^0 x L^g`, with `F` embedded diagonally
  so that `L_e ∩ F = N_e`;
- the first rope `Gamma_e = < K_e, v | [v, L_e] = 1 >`.

**(R1) General lemma.** Let `L <= K` and `F <= K`, and suppose `L ∩ F = N`
is normal in `F` with `F/N` non-amenable. Then `K / core_K(L)` is
non-amenable.

**(R2) The compiler.** On every branch `K_e / core(L_e)` is non-amenable, and
`L_e` is **not co-amenable** in `K_e`.

**(R3) Reduction.** Suppose the two-sided action

```text
F(X_e) x F(X_e)  ↷  H_e,       (g,h).q = g q h^-1,
```

is sofic in the sense of GKP Definition 2.1(5). Then `Gamma_e` is sofic.

DERIVATION [[compiler-rope-edge-is-not-co-amenable-proof]].

## Consequences

- The amenable-image route does not apply to the rope. That route covers GKP
  Theorem 2.17 with Proposition 2.15(1), the Elek--Szabó splitting over the
  core, and [[separating-sofic-quotient-sets-make-an-action-sofic]] (C2) with
  a single amenable quotient. By (R1) the switch is lost whenever a benign
  witness has an amenable core quotient.
- [[co-amenable-induction-of-sofic-actions]] does not apply, by (R2).
- The step "choose the base amenable" of
  [[mikhailova-coset-action-is-two-sided-q-action]] cannot be carried out
  inside this compiler. The base is `H_e`, which contains `F(x,y)`.
- (R3) moves the whole first rope onto one concrete action. That action is
  a pullback of the two-sided translation action of the finitely presented
  group `H_e`, and it is sofic whenever `H_e` is residually amenable
  (separating-sofic-quotient-sets (C3)). On `FIN`, `H_e` contains the
  nonsofic seed, so it is not residually amenable. That is harmless, because
  only `INF` matters. On `INF` the question is open.
- Even with (R3) the positive branch needs the second, twisted rope
  `R_e = < Gamma_e x Q_e, u | u(s,1)u^-1 = (s, tau_e(s)), s in S_e >` over the
  non-amenable edge `S_e = F *_(N_e) F^v`. That rope is an HNN extension with
  a non-identity associated isomorphism, not a free wreath product, and no
  result recorded here covers it.
