# The lamplighter Kazhdan host needs no approximation hypothesis

Lane `swarm-0917-w4-bh-wreath-fa`, 2026-09-17. Supports
`fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree` (route
`fg-groups-simple-kazhdan-hosts-lamplighter-proof`) and, through it,
`decidable-groups-embed-in-decidable-simple-fa-groups`.

**Observation.** The host of `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`,

```text
H_Δ = EL_3(R_Δ),   R_Δ = LC(2^Δ, F_2) ⋊ L_Δ,   L_Δ = Z/2 ≀ Δ,
```

is proved there under the hypothesis that `Δ` is LEF. Reading the proof in
`research/artifacts/sk-universal-embedding-b-lamplighter-2026-09-13.md` line by line:

| Step there | Uses LEF? |
|---|---|
| §1 Lemma 1: minimality, topological freeness, generation of `R` | no, only `Δ` infinite and finitely generated |
| §1 Lemma 2: `R` simple, `Z(R) = F_2` | no (Baire density of free points + minimality) |
| §2 Lemma 3, Proposition 4: matricial models | **yes** |
| §3 Theorem 5, (T) | no (EJZ needs only `R` finitely generated) |
| §3 Theorem 5, simplicity | no (Steinberg criterion + Lemma 2) |
| §3 Theorem 5, LEF | **yes** (via Proposition 4) |
| §3 Theorem 5, infinite | no |
| §3 Theorem 5, embedding of `[L,L]` | no |

So LEF enters only to prove that the host is LEF. The route
`lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts-proof` uses the half-line
overgroup `C(Γ)` for two purposes: to keep LEF, and to put `Γ` inside a derived
subgroup, because Theorem 5 embeds only `[L,L]`. Neither is needed for a simple
Kazhdan host: the second is replaced by Whitehead's lemma below. This is the step
where Attempt 2 of `decidable-groups-embed-in-decidable-simple-fa-groups`
("its lamplighter host needs a LEF overgroup") stopped.

## Theorem

Let `Γ` be a finitely generated group. Put `Δ = Γ × Z`. Then `H = H_Δ` is an
infinite, finitely generated, simple group with property (T), `Γ` embeds in `H`,
and

```text
WP(Γ) ≤_m WP(H) ≤_T WP(Δ) ≡_T WP(Γ).
```

In particular, if `Γ` has solvable word problem then so does `H`, and `H` has
Serre's property FA.

## Proof

Notation of the 2026-09-13 artifact: `Δ` acts on `Z = 2^Δ` by `(δx)(h) = x(δ^(-1)h)`, `a` flips the coordinate at
`e`, `L = ⟨Δ, a⟩ ≅ Z/2 ≀ Δ` consists of the affine maps `x ↦ δx + c` with `c ∈ ⊕_Δ Z/2`, and
`R = LC(Z, F_2) ⋊ L`. `Δ = Γ × Z` is infinite and finitely generated, with finite generating set `S`.

**Step 1 (dynamics and the ring).** Lemma 1 and Lemma 2 of the 2026-09-13 artifact assume only that `Δ` is finitely
generated and infinite. They give:
- `L ↷ Z` is minimal and topologically free (the orbit of `x` contains the dense set `x + ⊕_Δ Z/2`; for
  `ℓ ≠ 1` and a cylinder window `W`, infinitude of `Δ` gives two fresh coordinates `h ≠ δ^(-1)h` on which a point of
  the cylinder is moved);
- `R` is generated as a ring by `u_s^(±1)` (`s ∈ S`), `u_a` and `p = 1_[x(e)=1]`;
- `R` is simple and `Z(R) = F_2`.

**Step 2 (property (T) and finite generation).** `R` is a finitely generated associative ring with `1`, so
`H = EL_3(R)` has property (T) by `elementary-groups-over-fg-rings-have-property-t` (Ershov--Jaikin-Zapirain). It is
finitely generated: `e_ij(r + r') = e_ij(r) e_ij(r')` and `e_ij(r r') = [e_ik(r), e_kj(r')]` for distinct `i, j, k`,
so the matrices `e_ij(t)` with `t` among the ring generators and `1` generate every `e_ij(r)`.

**Step 3 (simplicity).** `R = A_(F_2)(L ⋉ Z)` is the Steinberg algebra of the transformation groupoid, which is ample,
Hausdorff, with compact infinite unit space `Z`, minimal (Step 1) and effective (topologically free, Step 1). By
`steinberg-elementary-groups-are-simple-mod-centre`, every normal subgroup of `H` is central or all of `H`, and
`Z(H) ⊆ F_2^× I_3 = {I_3}`. So `H` is simple. It is infinite since `r ↦ e_12(r)` is injective on the infinite ring
`LC(Z, F_2)`.

**Step 4 (property FA).** By `property-t-implies-property-fa`, `H` has property FA.

**Step 5 (embedding, all of `Δ`).** `Δ` acts faithfully on `Z`: for `δ ≠ e`, `δ·1_{e} = 1_{δ} ≠ 1_{e}`. So
`Γ ≤ Δ ≤ L ≤ Homeo(Z)`, and `ℓ ↦ u_ℓ` is an injective homomorphism `L -> GL_1(R)`, since `R` is a free left
`LC(Z,F_2)`-module on the `u_ℓ`. For any unit `u` of any ring (Whitehead's lemma),

```text
e_12(u) e_21(-u^(-1)) e_12(u) = [[0, u], [-u^(-1), 0]] =: w(u),     w(u) w(-1) = diag(u, u^(-1)).
```

Check: `e_12(u) e_21(-u^(-1)) = [[0, u], [-u^(-1), 1]]`, and right multiplication by `e_12(u)` gives
`[[0, u], [-u^(-1), -u^(-1)u + 1]] = w(u)`; then `w(u) w(-1) = [[0,u],[-u^(-1),0]] [[0,-1],[1,0]] = diag(u, u^(-1))`.
No commutativity is used. Hence

```text
ι : Γ -> H,   γ ↦ diag(u_γ, u_γ^(-1), 1)
```

is a homomorphism into `E_2(R) ≤ EL_3(R) = H`, injective because its `(1,1)` entry is `u_γ`. This replaces the
commutator embedding of Theorem 5 there, and makes the derived-subgroup overgroup unnecessary.

**Step 6 (word problem).** Generate `H` by `e_ij(u_t^(±1))`, `t ∈ S ∪ {a}`, and `e_ij(p)`.
- `F_x(ℓ) = (ℓ^(-1)x)(e)` maps `Z` `L`-equivariantly, continuously and injectively (`F_x(δ) = x(δ)`) onto a subshift
  `X ⊆ F_2^L`, and carries `p` to the letter indicator `{y : y(e) = 1}`. So `R ≅ LC(X,F_2) ⋊ L` with the generators
  of `crossed-product-el-word-problem-is-group-wp-plus-language`, which gives `WP(H) ≡_T WP(L) ⊕ L(X)`.
- `WP(L) ≤_T WP(Δ)`: a word in `S^(±1) ∪ {a}` is normalized to `(c, δ)` with `c` a finite list of positions (words
  in `S`); positions are compared, and cancelled in pairs, with the oracle for `WP(Δ)`. The word is trivial iff
  `δ = e` and all positions cancel.
- `L(X) ≤_T WP(Δ)`: for `ℓ = (x ↦ δx + c)`, `ℓ^(-1)x = δ^(-1)(x + c)`, so `F_x(ℓ) = x(δ) + c(δ)`. A pattern `q` on a
  finite set `W` of words occurs in `X` iff the constraints `x(δ_w) = q(w) + c_w(δ_w)`, `w ∈ W`, agree whenever
  `δ_w = δ_(w')`. Every consistent family is realized because `Z` is the full shift. All tests use `WP(Δ)` only.
- `WP(Δ) = WP(Γ × Z) ≡_T WP(Γ)`.
- `WP(Γ) ≤_m WP(H)`: substitute for each generator of `Γ` a fixed word for its image under `ι`.

This is exactly Steps 3-5 of `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts-proof`, which never use LEF.
`∎`

## Consequences recorded as nodes

1. `decidable-groups-embed-in-decidable-simple-fa-groups` holds, in the stronger Kazhdan form. The hole of Attempt 2
   there is closed for every decidable input, LEF or not.
2. Part (D) of `finitary-permanence-closures-collapse-boone-higman-to-base` becomes unconditional: closure of a base
   class under subgroups, extensions, arbitrary products, directed unions **and** arbitrary graphs of groups, in any
   mixture, reaches every decidable group only if the base class already does
   (`mixed-permanence-closures-collapse-boone-higman-to-base`).
3. `boone-higman-conjecture` is equivalent to its restriction to infinite finitely generated simple Kazhdan groups
   with solvable word problem (`boone-higman-iff-simple-kazhdan-decidable-inputs`).

## Sanity checks

- No contradiction with `input-encoded-sft-groupoid-hosts-are-not-universal` or with Kazhdan-free host classes: the
  host `H` is not a topological full group and is not claimed to be finitely presented.
- No contradiction with `free-rf-actions-force-residually-finite-groups`: the action is not free (constant
  configurations are fixed by `Δ`), and no finite models are claimed.
- Finite `Γ` is handled by `Δ = Γ × Z`, which is infinite. The hypothesis "infinite" in Lemma 1 is used to find fresh
  coordinates and to make `Z` a Cantor set.
- The host is not claimed to be LEF, sofic or hyperlinear. For non-LEF `Γ` it is not LEF.
