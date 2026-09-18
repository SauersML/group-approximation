---
rg: 2
id: busemann-transplant-minimality-is-horospherical-minimality
kind: claim
title: A Busemann transplant of a minimal fibre is minimal once the skeleton's zero-lag (horospherical) relation is minimal; this holds for F_m x F_n outright, and for Ã2 lattices it follows from germ primitivity; the phase skeleton also needs the fibre's finite factors prime to its modulus; so F_2 x F_2 carries a free minimal quantum-rigid SFT
requires:
  - tree-product-busemann-transplants-preserve-quantum-rigidity
  - a2-busemann-transplants-preserve-quantum-rigidity
  - minimal-crossing-wire-fixed-point-shift-is-quantum-rigid
distinct_from:
  busemann-transplants-give-free-sfts-on-building-lattices: that proves finite type and freeness of transplants and leaves minimality open; this decides minimality.
  tree-product-busemann-transplants-preserve-quantum-rigidity: that transfers rigidity and freeness; this transfers minimality, under a horospherical condition on the skeleton.
  f2-times-f2-has-a-quantum-rigid-free-minimal-sft: that is gate G2(c); this answers it, conditionally on the minimal crossing-wire fibre.
---

**ESTABLISHED** for items 1–5, by the lane proofs below (bh-invent-04, 2026-09-18; unreviewed; no
priority claimed). Item 6 and the Corollary are **CONDITIONAL** as stated.

## Setting

- `Γ` acts minimally on a compact skeleton `X_s`, with a continuous Busemann cocycle
  `β : Γ × X_s -> L ≅ Z^r`.
- `Y` is a minimal `Z^r`-subshift, and `M : Z^r -> L` is an isomorphism.
- The transplant is the skew product `X_s ×_β Y`, `γ(x, y) = (γx, σ^(M^(-1) β(γ,x)) y)`. This is
  item 1 of `busemann-transplants-give-free-sfts-on-building-lattices` and of the two transplant
  theorems in `requires`.
- **Zero-lag relation:** `K = {(x, γx) : β(γ, x) = 0}`.
- **Reach:** `Reach(x, U) = {β(γ, x) : γx ∈ U}`.
- **(Onto)** For every `x`, `β(Γ, x) = L`. This holds for Busemann cocycles of groups acting simply
  transitively on vertices, since `b_c` maps them onto a full coset of `L`.

## Theorem

1. **Criterion.** Let `E ≤ L` be a subgroup such that `M^(-1)E` acts minimally on `Y`. Suppose
   `Reach(x, U)` contains a coset of `E` for every `x` and every nonempty open `U`. Then `X_s ×_β Y`
   is minimal.
2. **Horospherical minimality.** Suppose every `K`-orbit is dense in `X_s`. Then `Reach(x, U) = L`, so the
   transplant of **every** minimal `Y` is minimal. Under (Onto), density of `K`-orbits is equivalent to
   minimality of `Γ ↷ X_s ×_β L`. In a building it says: *every horosphere of every chamber at
   infinity sees every skeleton germ type.*
3. **Obstruction.** Let `L' ≤ L` have finite index. Suppose there is a continuous
   `q : X_s -> L/L'` with `q(γx) = q(x) + β(γ, x)`, and `Y` has an equivariant factor `π` onto
   `Z^r / M^(-1)L' ≠ 0`. Then `q(x) − Mπ(y)` is a nonconstant invariant continuous function, so the
   transplant is **not** minimal.
4. **The phase skeleton.** Let `P ⊆ Ω × L/nL` be a minimal piece, as in
   `a2-lattice-boundary-skew-shifts-are-quantum-rigid`.
   - The phase coordinate is a `q` as in item 3. So the transplant over `P` of any fibre with a
     factor onto a nontrivial quotient of `Z^r / nZ^r` is never minimal.
   - If `K` is minimal on `Ω`, then `P = Ω × L/nL`, and the transplant over `P` is minimal **iff**
     `nZ^r` acts minimally on `Y`.
5. **Free groups.** For `Γ = F_{n_1} × … × F_{n_r}` with free bases, all `n_i >= 2`, and the arrow skeleton
   `∂T_1 × … × ∂T_r`, `K` is minimal. So every minimal fibre has a minimal transplant.
6. **Ã2 lattices (Setting of `a2-busemann-transplants-preserve-quantum-rigidity`).**
   - **(GP) Germ primitivity.** For each `R` there is `μ ∈ L ∩ C°` such that every radius-`R` germ type
     `S` can be followed at offset `μ` by every radius-`R` germ type `T`. That is, some sector piece at
     `o` extends `S` and has type `T` at its vertex of offset `μ`.
   - (GP) implies that `K` is minimal on `Ω`.
   - (GP) holds whenever a finite 2-graph coding the sectors, such as the Robertson–Steger tile system,
     is primitive: some `M_1^(p_1) M_2^(p_2)` with `p_1, p_2 >= 1` is entrywise positive.
   - That is a finite matrix check per lattice. **It was not performed.**

**Topological freeness** is automatic in every case: the transplant is free when `Y` is (item 2 of the
transplant theorems).

## Corollary (gates G2(c) and G2 over Kazhdan lattices)

Let `Ω_min` be the minimal crossing-wire shift in the causal diagonal-time layout, `Ω_SW` of
`sw-minimal-crossing-wire-shift-is-rigid`. It is free, minimal, quantum rigid and SW-deterministic, conditional
on that node's §2 layout. **Correction (bh-invent-04, after the referee FAIL of the SW Layout Lemma).** An
earlier version of this sentence cited the "one-way (A4) variant" with a generic one-way zone. The
causality lemma in that node rules that variant out. The transplant needs a cone-deterministic fibre, so
this Corollary, including the `F_m × F_n` case, rests on the causal layout. It does not rest on the
two-way-head fibre of `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`, which is not
cone-deterministic. Put `Y = Ω_min ∘ M^(-1)` with `M(−e_1) = (2,1)`,
`M(−e_2) = (1,1)`. Recoding by `GL_2(Z)` keeps minimality, freeness and rigidity at large scale.
- **`F_m × F_n`, `m, n >= 2`.** The transplant is an SFT that is **free, minimal and quantum rigid**
  over every field. This combines items 1, 2 and 4 of `tree-product-busemann-transplants-preserve-quantum-rigidity`
  with item 5 here. It answers `f2-times-f2-has-a-quantum-rigid-free-minimal-sft`, conditional on the
  lane proof of `Ω_min` and its A4 variant.
- **Ã2 lattices** (Kazhdan, one-ended). Under (GP), the transplant over `P` is free, minimal and
  quantum rigid, provided `nZ^2` acts minimally on `Ω_min`.
  - DR zooms are powers of 3 (`N_k = 3^(C^k)`), and the maximal equicontinuous factor is the
    corresponding odometer (recalled, not re-checked). So `n` prime to 3 suffices.
  - Over the skeleton `X_Ω^K` (case (i)), only (GP) and that case's hypotheses are needed.

## Proof

**Item 1.** Fix `(x, y)` and nonempty open sets `U ⊆ X_s`, `V ⊆ Y`.
- Pick `ℓ_0 + E ⊆ Reach(x, U)`.
- By minimality of `M^(-1)E` on `Y`, the orbit `σ^(M^(-1)(ℓ_0 + E))y` is dense, so some `ℓ` in the coset
  has `σ^(M^(-1)ℓ) y ∈ V`.
- Choose `γ` with `γx ∈ U` and `β(γ, x) = ℓ`.

**Item 2.** Given `x`, `U` and `ℓ`:
- by (Onto) pick `γ_1` with `β(γ_1, x) = ℓ`;
- by density of `K`-orbits pick `γ_2` with `β(γ_2, γ_1 x) = 0` and `γ_2 γ_1 x ∈ U`;
- the cocycle identity gives `β(γ_2γ_1, x) = ℓ`.

Minimality of the `L`-skew product gives density of `K`-orbits at level `0`, and conversely.

**Item 3.** Invariance: `q(γx) − Mπ(σ^(M^(-1)β) y) = q(x) + β − Mπ(y) − β`. The function is
nonconstant because `π` is onto and `q` is fixed on a fibre `{x} × Y`.

**Item 4.**
- *`P` is everything.* `K`-orbits preserve the phase, and their closures are `Ω`. So each phase slice
  of `P` is `Ω` or empty, and `P = Ω × S`. Invariance and (Onto) give `S + L = S`, so `S = L/nL`.
- *Sufficiency.* For `U` inside one phase slice `φ_U`, item 2's argument gives
  `Reach((ω, φ), U) ⊇ (φ_U − φ) + nL`. Apply item 1 with `E = nL`.
- *Necessity.* If `nZ^r` is not minimal on `Y`, its orbit closures form a finite clopen partition that
  `Z^r` permutes transitively. This gives a factor onto `Z^r/H` with `nZ^r ⊆ H ≠ Z^r`, and item 3
  applies.

**Item 5.** It suffices to treat one factor: the action is a product, so `K` is the product of the factors'
zero-lag relations. On `∂F_n`, the relation `K` is tail equivalence with equal prefix lengths: `uz ~ vz`
with `|u| = |v|`. With `γ = uv^(-1)`, the level of `γ^(-1) o` relative to the end is `|v| − |u| = 0`.
Given `x = x_1 x_2 …` and a cylinder `[w]`:
- take `m >= |w| + 2` and `z = x_(m+1) x_(m+2) …`;
- choose a reduced `u` of length `m` with prefix `w` and `u_m ≠ z_1^(-1)`. Each free letter avoids at
  most two values, and `2n >= 4`.

Then `uz ∈ [w]` and `(x, uz) ∈ K`.

**Item 6 ((GP) implies `K` minimal).** Fix `c ∈ Ω` and a target cylinder `Z_S(o)` of radius `R`. We need
`u ∈ V_0` with `b_c(u) = b_c(o)` and `type_c(u) = S`. Then `γ = γ_u`, the unique element with
`γ_u u = o`, satisfies `β(γ, c) = 0` and `γc ∈ Z_S(o)`.
1. **Choose the realiser.** Let `μ` be given by (GP), put `w = p_μ^c(o)` and `T = type_c(w)`. (GP)
   gives `c''` whose sector at `o` has piece `S` and has type `T` at `w'' = p_μ^(c'')(o)`.
2. **Transport it.** Put `g = γ_w^(-1) γ_(w'')`, so `g w'' = w`, and `u = g o`. Then `gc''` and `c` have
   the same radius-`R` piece at `w`, and `w ∈ Q(u, gc'')` at offset `μ`.
3. **Opposite sectors.** Let `S'` be the sector at `w` opposite to `Q(w, gc'')` in an apartment
   containing `Q(u, gc'')`, so `u ∈ S'`.
   - Its base chamber is opposite, in `lk(w)`, to the base chamber of `Q(w, c)`, which equals that of
     `Q(w, gc'')`.
   - Two sectors at one vertex with opposite base chambers lie in a common apartment (standard;
     recalled).
   - In that apartment, `Q(u, c) = u + C̄ ⊇ Q(w, c)`, so `b_c(u) = b_c(w) − μ = b_c(o)`.
4. **Compare the pieces.** Both `Q(u, c)` and `Q(u, gc'')` contain:
   - the corner parallelogram between `u` and `w`, which lies in `S'`;
   - the same radius-`R` piece at `w`.

   The proof of the Determination Lemma (`a2-busemann-transplant-rigidity-proof`, Step 2) uses only
   these two inputs, since the corner region is all it reads from the germ at `v`. So the radius-`R`
   pieces at `u` agree. Hence `type_c(u) = type_(gc'')(u) = S`, because `γ_u = g^(-1)`.

**The 2-graph clause.** Radius-`R` types are paths of bounded degree in the coding 2-graph. Suppose
`M_1^(p_1) M_2^(p_2) > 0`. Since the `M_i` have no zero rows, `M^q > 0` for all `q >= p`. This lets any
such path be joined to any other at offset `μ = p + (R, R)`. ∎

## Lesson for general BH

- **Minimality of a transplant is a horospherical statement about the skeleton.** Every horosphere of
  every boundary point must see every germ. Given that, *every* minimal fibre transplants to a
  minimal shift.
- **Only arithmetic can obstruct it.** A finite phase that the Busemann cocycle carries must avoid
  the fibre's finite factors, so their moduli should be coprime.
- **Consequence.** Rigidity (co-location), freeness (aperiodic fibre), minimality (horospherical
  mixing) and non-amenability (the tree or building) are four independent layers, and none of them
  interferes with another.
- **Result.** This gives the first free minimal quantum-rigid SFT over a non-amenable one-ended group,
  `F_2 × F_2`, conditional on the minimal crossing-wire fibre. Over Ã2 Kazhdan lattices it holds up to
  one finite primitivity check.

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS for the transfer (items 1–5, and item 6's implication); the Corollary is correctly conditional

I checked items 1–6 and the Corollary line by line. I did not check the fibre `Ω_min`; that is with
another referee.

- **Item 1, the criterion.** A translate of a dense `M^(-1)E`-orbit is dense. A coset inside
  `Reach(x, U)` gives, for each of its elements `ℓ`, some `γ` with `γx ∈ U` and `β(γ,x) = ℓ`. So
  every orbit meets every `U × V`. Correct.
- **Item 2.** The cocycle identity `β(γ_2γ_1, x) = β(γ_2, γ_1 x) + β(γ_1, x)`, together with (Onto),
  gives `Reach = L`. The equivalence with minimality of `X_s ×_β L` is correct, since `L` is discrete.
- **Item 3.** `f = q − Mπ` is invariant, as checked, and nonconstant on a fibre `{x} × Y`.
- **Item 4.**
  - `K` preserves the phase, so each slice is closed and `K`-invariant, hence all of `Ω` or empty.
    (Onto) gives `S = L/nL`.
  - Sufficiency: the coset `(φ_U − φ) + nL` lies in `Reach`, and item 1 applies with `E = nL`.
  - Necessity: `nZ^r`-minimal subsets of a minimal `Y` are equal or disjoint and cover `Y`, so they
    give a finite factor onto `Z^r/H` with `nZ^r ⊆ H ≠ Z^r`.
- **Item 5, `F_m × F_n`.** `K` is the product of the factors' relations. Only the inclusion "equal-lag
  tail pairs `(vz, uz)` lie in `K` via `γ = uv^(-1)`" is needed.
  - I checked it with the horoheight: for `|u| = |v| = m`, `u_m ≠ z_1^(-1)`, the vertex `vu^(-1)` has
    horoheight `0` toward `vz`.
  - The density construction (a reduced `u ∈ [w]`, each letter avoiding at most two values, `2n >= 4`)
    is correct.
  - (Onto) holds for the simply transitive product action.
- **Item 6, (GP) ⇒ `K` minimal on `Ω`.** It is correct, granted one recalled fact.
  - `γ_u c ∈ Z_S(o)` iff `type_c(u) = S`, and `β(γ_u, c) = 0` iff `b_c(u) = b_c(o)`.
  - Equal types at `w` mean equal radius-`R` pieces at `w`, and `g w'' = w` puts `w` at offset `μ` in
    `Q(u, gc'')`.
  - In an apartment containing the opposite sector `S'` and `Q(w,c)`, `u + C̄ ⊇ w + C̄`.
  - The corner parallelogram lies in `S'`, which is common to both apartments. So the uniqueness
    steps of the Determination Lemma reconstruct the same radius-`R` piece at `u` for `c` and for
    `gc''`, with input radius `R` at `w` and output radius `R + min(s,t)`.
  - `γ_u = g^(-1)`, which gives `type = S`.
  - The recalled fact is that two sectors at one vertex with opposite germs lie in a common apartment.
    It is standard, but it is cited, not proved.
- **Freeness and topological freeness transfer.**
  - Γ acts freely on the transplant whenever `Z^r` acts freely on `Y`, by item 2 of
    `tree-product-busemann-transplants-preserve-quantum-rigidity`. For Ã2 it is item 2 of the Ã2
    theorem, which rests on the lane node on chamber-fixing translations. Both are refereed.
  - Topological freeness follows from freeness.
  - So for the Corollary it suffices that `Ω_min` is strongly aperiodic.
- **Corollary for `F_m × F_n`.**
  - `M(−e_1) = (2,1)` and `M(−e_2) = (1,1)` give `det M = 1`. SW-determinism becomes the cone rule
    with offsets `(2,1), (1,1) ∈ Z_(>=1)^2`, so tree-product item 4 gives rigidity, and item 2 gives
    freeness.
  - Items 5 and 2 here give minimality for every minimal fibre.
  - So the answer to `f2-times-f2-has-a-quantum-rigid-free-minimal-sft` is exactly as conditional as
    the node says: it holds iff the lane proof of `Ω_min` (A4) holds.

**Minor.**
1. **The 2-graph clause.** The matrix step "positive times nonnegative stays positive" needs no zero
   rows **and** no zero columns. Both hold for 2-graphs without sources or sinks. (GP) itself is
   unverified for any lattice, so item 6's Ã2 Corollary remains conditional, as stated.
2. **The Ã2 phase condition.** It uses the recalled DR fact that the maximal equicontinuous factor is
   the 3-adic odometer. Given that fact, `n` prime to 3 suffices, because finite factors then have
   3-power index.
3. **"First free minimal quantum-rigid SFT over a non-amenable one-ended group."** This is a priority
   claim, not checked, and it is conditional.
