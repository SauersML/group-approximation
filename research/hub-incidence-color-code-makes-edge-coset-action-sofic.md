---
rg: 2
id: hub-incidence-color-code-makes-edge-coset-action-sofic
kind: claim
title: A lamp-free incidence color code on the base group makes a centralizer-HNN edge coset action sofic
artifacts:
  - research/hub-incidence-color-code-makes-edge-coset-action-sofic-proof.md
distinct_from:
  first-rope-edge-coset-action-is-sofic: that is the compiler instance of the conclusion, still open; this reduces it to a statement about K_e alone, with no lamps and no hub.
  gkp-free-generalized-wreath-soficity: that is soficity of the regular action (the case F = 1 here); this handles the coset action of the edge S = <F, vFv^-1> for an arbitrary F <= K.
  free-cover-left-right-action-over-sofic-group-is-sofic: that builds exact free extensions for a left-right action over a sofic quotient; this glues free lamp fibres over the hub of a centralizer HNN extension.
---

ESTABLISHED (unreviewed). Full proof in the artifact.

**Setting.** `K` is a countable group, `L, F <= K`, `X = K/L`, `x_0 = L`, and

```text
Gamma = < K, v | [v, l] = 1, l in L > = F(X) x| K,     v = z_(x_0),
S     = < F, v F v^-1 > = A_Y x| F,                    Y = F.x_0,
```

by [[centralizer-hnn-is-free-generalized-wreath]], where
`A_Y = < z_y z_(y')^-1 : y, y' in Y >`.

**Hypothesis (HC): a hub incidence color code on K.** There are a free
ultrafilter `U`, finite sets `A_n`, a homomorphism `b : K -> prod_U Sym(A_n)`
(with representatives `b_n(k)`), colorings `omega_n, zeta_n : A_n -> Nat`, and
relations `R_n <= Nat x Nat` such that, for every fixed `k in K`, as `n -> U`:

- (HC1) `omega_n(b_n(k)^-1 a) = omega_n(a)` for asymptotically almost every `a` if `k in F`,
  and `!=` for asymptotically almost every `a` if `k notin F`;
- (HC2) the same for `zeta_n` with `L` in place of `F`;
- (HC3) `(omega_n(a), zeta_n(b_n(k)^-1 a)) in R_n` for asymptotically almost every `a` if `k in FL`,
  and `notin R_n` for asymptotically almost every `a` if `k notin FL`.

**Theorem.** (HC) implies that `Gamma action Gamma/S` is sofic (GKP Definition 2.1(5)).

**Why this is the right statement.** The Attempts of
[[first-rope-edge-coset-action-is-sofic]] record that the direct gluing dies:
the space `Gamma/S` fibres over `K/F`, the fibres are free, but the base coset is a
hub (all points `z_y^-1 S`, `y in Y`, coincide), and the hub relations couple
the lamp permutations of different fibres. The theorem removes the lamps
entirely. The model is `A_n x T_n`, where `T_n` is a finite quotient of the free
group on the lamp palette, chosen by M. Hall separability so that the hub
subgroups `A_J` stay closed up to radius `r_n -> infinity`. The coupling is
absorbed into one K-level datum: the relation (HC3), which says in the model
whether a lamp is incident to a base point.

**Calibrations.**
- `F = 1`: (HC) is implied by soficity of `K action K ⊔ K/L` (take
  `omega = (omega', zeta)` and let `R` match the second coordinate). This recovers GKP
  Theorem 3.7 for the regular action.
- `[F : F cap L] < infinity`: (HC) is implied by soficity of
  `K action K/F ⊔ K/L`. Take `omega = (omega_F, {zeta(b(f_i)^-1 a)}_i)` over
  representatives `f_i` of `F/(F cap L)`, and let `R` be membership.
- `S` is not assumed co-amenable, and `K` need not be amenable.

**Consequence for the compiler (one direction only).** Apply the theorem to
`K = K_e`, `L = L_e`, `F` diagonal, on `INF`. Then (HC_e) implies
[[first-rope-edge-coset-action-is-sofic]]. Combined with
[[envelope-coset-action-sofic-once-edge-coset-action-sofic]], soficity of
`Gamma_e` and (HC_e) make `R_e` sofic. So a proof of
[[compiler-positive-rope-is-not-sofic]] must refute (HC_e), which contains no
lamps, or refute soficity of `Gamma_e`. Whether (HC) is necessary for the
conclusion is open.
