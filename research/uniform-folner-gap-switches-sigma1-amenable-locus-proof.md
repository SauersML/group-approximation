---
rg: 2
id: uniform-folner-gap-switches-sigma1-amenable-locus-proof
kind: route
title: Semi-decide Følner sets at the fixed scale, and bound free witnesses through coset averaging and Namioka's trick
target: uniform-folner-gap-switches-have-sigma1-amenable-locus
requires: [recursive-amenable-classes-have-uniform-folner-bounds]
---

**(UG0).**
- *Amenable members.* An amenable group has `n`-Følner sets for every `n`, in
  particular for `n*`.
- *Non-amenable members.* By (UG) they have none.
- *Semi-decision.* Corollary 3.4 in `recursive-amenable-classes-have-uniform-folner-bounds`
  says the set of finitely generated recursive presentations admitting `n*`-Følner
  sets is recursively enumerable, uniformly in the presentation. So its preimage
  under the computable map `e -> P_e` is recursively enumerable.

**No 2-Følner sets in `F(a,b)`.** In the left Cayley graph for `S = {a^±1, b^±1}`,
a 4-regular tree, a finite `Ω` spans a forest with at most `|Ω|-1` edges. Its
edge boundary therefore has at least `4|Ω| - 2(|Ω|-1) = 2|Ω| + 2` edges, and the
boundary edges labelled `s` number `|Ω \ s^-1 Ω|`. Using
`|Ω \ x^-1Ω| = |xΩ \ Ω| = |Ω \ xΩ|`,

```text
2 ( |Ω \ aΩ| + |Ω \ bΩ| )  >=  2|Ω| + 2,
```

so `max(|Ω \ aΩ|, |Ω \ bΩ|) > |Ω|/2`.                                       (NF2)

**Word lengths.** For `x_1,...,x_k in X^±1`,

```text
|Ω \ x_1...x_k Ω|  <=  sum_i |Ω \ x_iΩ|,
```

since `|x_1 Ω' \ x_1 Ω''| = |Ω' \ Ω''|`. So an `n`-Følner set satisfies
`|Ω \ wΩ| <= L|Ω|/n` for every word `w` of length at most `L`.            (NF3)

**(UG1) => (UG) with `n* = 4L`.** Let `Ω` be `4L`-Følner in `P = P_e`, and let
`H = <u,v> ≅ F_2`. Split `Ω` along right cosets, `Ω_c = Ω ∩ Hc`. For `h in H` we
have `hΩ ∩ Hc = hΩ_c`, so by (NF3)

```text
sum_c ( |Ω_c \ uΩ_c| + |Ω_c \ vΩ_c| )  <=  2L|Ω|/(4L)  =  sum_c |Ω_c|/2.
```

Some nonempty `Ω_c` satisfies the inequality, and then `Ω_c c^-1 ⊆ H` has both
defects at most `|Ω_c|/2`. This contradicts (NF2).

**(UG2) => (UG) with `n* = 4L`.** Let `π : P ->> F(a,b)` with `a = π(w_a)`,
`b = π(w_b)` and `|w_a|, |w_b| <= L`. Let `Ω` be `4L`-Følner in `P` and put
`h = π_*(χ_Ω)`, so `||h||_1 = |Ω|`. Pushforward commutes with translation,
`π_*(χ_(wΩ)) = _(π(w)) h`, and does not increase `l^1` distances (Cavaleri,
Remark 2.5). So by (NF3), for `x in {a,b}` with lift `w_x`,

```text
||h - _x h||_1  <=  ||χ_Ω - χ_(w_x Ω)||_1  =  2|Ω \ w_xΩ|  <=  2L|Ω|/(4L)  =  ||h||_1/2.
```

The layer-cake identities are

```text
||h - _x h||_1 = ∫_0^∞ |L_t Δ xL_t| dt,    ||h||_1 = ∫_0^∞ |L_t| dt,    L_t = {h > t}.
```

Summing over `x in {a,b}` gives some `t` with `L_t` finite and nonempty and
`|L_t Δ aL_t| + |L_t Δ bL_t| <= |L_t|`. Hence both `|L_t \ aL_t|` and
`|L_t \ bL_t|` are at most `|L_t|/2`, contradicting (NF2).

**Recovered screens.**
- *Centralizer switch.* If `K_e != A_e`, some presentation generator `a` of `A_e`
  lies outside `K_e` (otherwise `K_e = A_e`), and Britton gives
  `<t, a t a^-1> ≅ F_2`. So (UG1) holds with `L = 3`.
- *Raw simulator.* With `s >= 2` substitution letters, killing `X_e` maps
  `t_1, t_2` onto a basis. So (UG2) holds with `L = 1`. `∎`
