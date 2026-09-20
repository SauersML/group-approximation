---
rg: 2
id: clifford-witness-refutes-kazhdan-profile-regularization-proof
kind: route
title: Conjugate the root lamp by the stable letter, read the failure through injectivity, and feed a regularized representation of a chain-envelope configuration into the CKN conclusion
target: clifford-witness-refutes-kazhdan-profile-regularization
requires:
  - sofic-normalization-fails-for-finite-index-kazhdan-pairs
  - sofic-non-mf-witness
  - ckn-forces-nonsofic-incompressible-affine-coset-wreath
---

Conventions. `[x,y] = x y x^-1 y^-1`. Notation is that of
`sofic-normalization-fails-for-finite-index-kazhdan-pairs` and its proof route (Steps 1–3).
- `V` acts on `X = V/Gamma` on the left, and `g c_x g^-1 = c_(g x)` in `W`.
- The `c_x` are pairwise distinct.
- `Stab_V(g Gamma) = g Gamma g^-1`.

For a subgroup `H <= S_U`, `C(H)` denotes its centralizer in `S_U`. For every `s in S_U`,
`s C(H) s^-1 = C(s H s^-1)`, and `H_1 <= H_2` implies `C(H_2) <= C(H_1)`.

## Step 0: sofic representations are injective

If `tr sigma(g) = 0` for `g != 1`, then `sigma(g) != 1 = sigma(1)`, since `tr 1 = 1`. So `sigma`
is injective. `W` is sofic (`sofic-non-mf-witness`), so such a `sigma` exists for every
nonprincipal `U`, as in Step 3 of the calibration route.

## Step 1: (R0)

- `Stab_V(x_0) = Gamma`, so every `g in Gamma` satisfies `g c_(x_0) g^-1 = c_(x_0)`. Hence
  `c_(x_0) in C_W(Gamma)`.
- `t Gamma t^-1 = alpha(Gamma) = Gamma' <= Gamma`, so `t in Comp_W(Gamma)`.
- `t c_(x_0) t^-1 = c_(t x_0) = c_y`, with `y = t x_0` and `Stab_V(y) = Gamma'`.
- `a = (e_1, I)` lies in `Gamma \ Gamma'`, so `a y != y` and `a c_y a^-1 = c_(a y) != c_y`
  (calibration route, Step 2). Hence `[c_y, a] != 1`.

So `[t c_(x_0) t^-1, a]` is a nontrivial generator of `D_W(Gamma)`, of the form `[g z g^-1, l]`
with `g = t`, `z = c_(x_0)` and `l = a`.

## Step 2: (R1)

Let `sigma` be a sofic representation of `W`, and put `C = C(sigma Gamma)` and
`C' = C(sigma Gamma')`.
- `sigma(t) C sigma(t)^-1 = C(sigma(t Gamma t^-1)) = C'`.
- `Gamma' <= Gamma` gives `C <= C'`.
- `sigma(c_(x_0)) in C` by Step 1. Its conjugate `sigma(t) sigma(c_(x_0)) sigma(t)^-1 = sigma(c_y)`
  lies in `C'`. It does not commute with `sigma(a) in sigma(Gamma)`, because `[c_y, a] != 1` and
  `sigma` is injective (Step 0). So `sigma(c_y) notin C`.

Hence `C < C' = sigma(t) C sigma(t)^-1` strictly, and `sigma(t)` does not normalize `C`.

## Step 3: (R2) and (R3)

- **(R2).** Suppose `P` is normalizing and `sigma` is a sofic representation of `W` with
  `P(sigma, Gamma, t)`. Then `W` is sofic, `Gamma` is Kazhdan [calibration (F1)] and
  `t in Comp_W(Gamma)`, so normalizing gives that `sigma(t)` normalizes `C(sigma Gamma)`. This
  contradicts Step 2.
  - So `(Reg_P)` fails at `G = W`, `L = Gamma`, `u = t`.
  - `W` is finitely generated (`sofic-non-mf-witness`).
  - `[Gamma : t Gamma t^-1] = 8` and `<<t Gamma t^-1>>^Gamma = Gamma` by (F1).
- **(R3a).** A profile property is a special case of a representation property. For the
  finite-scale property, the normalizing implication is FSK1: "If `sigma|_L` is finite-scale,
  then `sigma(s) C sigma(s)^-1 = C` for every `s in Comp_G(L)`." That node is on the session
  branch only, so it is not a formal prerequisite here. Its setting ("`L` is a Kazhdan group
  with finite symmetric generating set `S`, and `L <= G` for a countable group `G`") covers
  `Gamma <= W`, since `Gamma` is finitely generated. Given FSK1, (R2) with `P = finite-scale`
  says that no sofic representation of `W` is finite-scale on `Gamma`, which contradicts (PR).
- **(R3b).** Given (KT\*), item 1 of `bounded-period-compressors-carry-no-sofic-defect` reads:
  "If `u` is tame, then `[u c u^-1, l] = 1` for all `c ∈ C_G(L)` and `l ∈ L`." Step 1 gives
  `c = c_(x_0)` and `l = a` with `[t c t^-1, l] != 1`. So `t` is not tame, which by that node's
  definition means it is wild. This item is recorded as an implication from (KT\*), which is
  OPEN, and is not part of what this route establishes unconditionally.

## Step 4: (R4)

Assume `(Reg_P^env)` with `P` normalizing. Let `G` be sofic, `L <= G` Kazhdan and
`u in Comp_G(L)`, with `union_n u^-n L u^n` inside a Kazhdan subgroup of `G`; these are the
hypotheses of (CKN).
1. `(Reg_P^env)` gives a sofic `sigma` with `P(sigma, L, u)`.
2. Normalizing then gives `sigma(u) C sigma(u)^-1 = C`, where `C = C(sigma L)`.
3. Let `c in C_G(L)`. Then `sigma(c) in C`.
   - So `sigma(u c u^-1) in C` and `sigma(u^-1 c u) in sigma(u)^-1 C sigma(u) = C`.
   - Hence `[sigma(u c u^-1), sigma(l)] = 1` and `[sigma(u^-1 c u), sigma(l)] = 1` for every
     `l in L`.
   - By injectivity, `u c u^-1` and `u^-1 c u` lie in `C_G(L)`.
4. So `u C_G(L) u^-1 = C_G(L)`, which is the conclusion of (CKN).

Display (CK10) of `ckn-forces-nonsofic-incompressible-affine-coset-wreath` reads
"CKN ==> W_aff,p is not sofic". Directly: if `W_aff,p` were sofic, then the coset wreath `W'`
of (CK1) for `(M_p, alpha, L)` would be sofic by (CK4). It satisfies the hypotheses of (CKN) by
(CK2), so items 1–4 above would make `u` normalize `C_(W')(L)`, contradicting (CK3). By (F4), no Kazhdan subgroup of `W` contains `union_n t^-n Gamma t^n`, so
`W` does not satisfy the hypothesis of `(Reg_P^env)`.

## Step 5: the kernel-specific form

In the setting of `(Reg_P^K)`, every compressor chain of `L <= K` lies in the Kazhdan subgroup
`K`. So each instance `(G, L, u)` of `(Reg_P^K)` satisfies the hypotheses of `(Reg_P^env)`, and
`(Reg_P^env)` implies `(Reg_P^K)` in its per-compressor form, which is all the kill below uses.
With `P` normalizing, apply items 2–4 of Step 4 to the representation that `(Reg_P^K)` supplies.
They show that every `u in Comp_G(L)` normalizes `C_G(L)`, so every defect generator
`[u c u^-1, l]` is trivial.

`D_G(L)` is normally generated by `[g z g^-1, l]` with `g` in the group generated by
`Comp_G(L)`. The set of `g` that normalize `C_G(L)` is a subgroup and contains `Comp_G(L)`, so it
contains every such `g`. Hence `D_G(L) = 1`, which kills (EK1). The survival conditions stated
in the claim follow from (R2) and (R4).
