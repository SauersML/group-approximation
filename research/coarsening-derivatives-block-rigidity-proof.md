---
rg: 2
id: coarsening-derivatives-block-rigidity-proof
kind: route
title: Proof that coarsening derivative data are block-rigid, window-avoiding colourings with large derivatives on Følner mass
target: coarsening-derivatives-are-block-rigid-and-window-avoiding
requires: [marginal-derivative-amplification-is-sharp-at-log-height]
---

Notation is as in the target. The required claim supplies only the definitions (derivative
datum, (E′), `c`-thin, `bd`). The imports from Moore, arXiv:0905.1118v7, quoted verbatim from
the TeX source (as also done in the proof of the grafting class kill of swarm-0917-w21), are
the generators
"$x_0 = \seq{00} \mapsto \seq{0}, \seq{01} \mapsto \seq{10}, \seq{1} \mapsto \seq{11}$" and
"$x_1 = \seq{0} \mapsto \seq{0}, \seq{100} \mapsto \seq{10}, \seq{101} \mapsto \seq{110},
\seq{11} \mapsto \seq{111}$", and the action "If $T$ is in $\Tcal$ and $f$ is in $F$ with $f$
defined on all of $T$, then $T \cdot f$ is the pointwise image of $T$ under $f$."

## Step 0: definedness is read off the window

`T·f` is defined iff every leaf of `T` extends a domain piece of `f`. For a complete prefix
code `T` and a finite set of pieces forming a complete prefix code `D`, this holds iff every
internal node of the tree `D` is an internal node of `T` (i.e. `T` refines `D`). The domain
codes are:
- `x0`: `{00, 01, 1}`, internal nodes `{∅, 0}`;
- `x0^{-1}`: `{0, 10, 11}`, internal nodes `{∅, 1}`;
- `x1`: `{0, 100, 101, 11}`, internal nodes `{∅, 1, 10}`;
- `x1^{-1}`: `{0, 10, 110, 111}`, internal nodes `{∅, 1, 11}`.

Write `Σ(T)` for the set of internal nodes of `T` lying in `W = {∅,0,1,10,11}`. It is
prefix-closed. By the list, the set `def(T) = {γ : T·γ defined}` is a function of `Σ(T)`.
Running through the eleven prefix-closed subsets of `W`:
`∅ ↦ ∅`, `{∅} ↦ ∅`, `{∅,0} ↦ {x0}`, `{∅,1} ↦ {x0⁻¹}`, `{∅,0,1} ↦ {x0,x0⁻¹}`,
`{∅,1,10} ↦ {x0⁻¹,x1}`, `{∅,1,11} ↦ {x0⁻¹,x1⁻¹}`, `{∅,1,10,11} ↦ {x0⁻¹,x1,x1⁻¹}`,
`{∅,0,1,10} ↦ {x0,x0⁻¹,x1}`, `{∅,0,1,11} ↦ {x0,x0⁻¹,x1⁻¹}`, `W ↦ Γ`.
The map is injective except that `∅` and `{∅}` both give `∅`.

## Theorem 1

Let `U` be dominated by `T`. Every internal node of `U` is internal in `T`, so
`Σ(U) ⊆ Σ(T)`.

*Claim: `Σ(T) ⊆ Σ(U)` iff `U` is window-avoiding for `T`.*
- Suppose `w ∈ Σ(T) ∖ Σ(U)`. Since `U` is a complete prefix code dominated by `T`, `w` is
  at or below some leaf `u` of `U`: `u` is a prefix of `w`. As `W` is prefix-closed, `u ∈ W`.
  As `w` is internal in `T` and `w` extends `u`, `T/u` has at least 2 leaves. So `U` is not
  window-avoiding.
- Conversely, if a leaf `u ∈ W` of `U` has `|T/u| ≥ 2`, then `u` is internal in `T` but a
  leaf of `U`, so `u ∈ Σ(T) ∖ Σ(U)`.

*Proof of the theorem.* `def(T) = def(U)` iff `Σ(T)` and `Σ(U)` have the same image under
the map of Step 0. With `Σ(U) ⊆ Σ(T)` and the injectivity list, this happens iff
`Σ(U) = Σ(T)`, or `Σ(U) = ∅` and `Σ(T) = {∅}`. The first case is window avoidance by the
Claim. In the second, `U` has no internal node in `W`, so `U = {∅}`; and `T` splits `∅` but
not `0`, `1`, so `T = {0, 1}`. ∎

## Theorem 2

Let `T ∈ A`, `U = ∂T` with leaves `u_1 <_lex … <_lex u_m`, and `γ ∈ Γ` with `T·γ` defined.
By (E′), `U·γ` is defined and `∂(T·γ) = U·γ`. (E′) is a condition at `T ∈ A` only, so this
does not need `T·γ ∈ A`.
- `U·γ` defined means each `u_i` extends a domain piece: `u_i = s x` with `s ↦ t`, and
  `u_i·γ = t x`. Every leaf of `T` below `u_i` has the form `u_i y`, it extends the same
  piece `s`, and it maps to `(u_i·γ) y`.
- Hence the leaves of `T·γ` below `u_i·γ` are exactly `{(u_i·γ) y : u_i y ∈ T}`, so
  `(T·γ)/(u_i·γ) = T/u_i`. The decorations agree.
- `γ` preserves `<_lex` on leaves: the domain pieces and the range pieces of each generator
  are listed in lex order in the quoted definitions, and within one piece `s x ↦ t x`
  preserves `<_lex`. Also `|T·γ| = |T|`, since the pointwise image is injective. So
  the `i`-th leaf of `U·γ` is `u_i·γ` and the index interval of leaves of `T·γ` below it is
  the index interval of leaves of `T` below `u_i`. The partitions agree.

*Item 1.* Along any edge between two points of `A` the pair `(π, β)` is preserved, so it is
constant on components of the restricted Schreier graph. For a fixed `β`, the map
`V ↦ σ_β(V)` is injective (the leaves of `V` are the minimal common prefixes of the
blocks), and `∂(σ_β(V)) = V` on the component by the definition of `β`.

*Item 2.* The forward direction is Theorem 1 plus the computation above. Conversely,
suppose `U = ∂T` is window-avoiding for `T` (or the exceptional pair) and
`π(T·γ, ∂(T·γ)) = π(T, U)` whenever `T·γ` is defined. By Theorem 1, `T·γ` is defined iff
`U·γ` is. If both are defined, `U·γ` is a coarsening of `T·γ` with partition `π(T, U)` by
the computation above. A coarsening of a given tree is determined by its leaf-index
partition (its leaves are the minimal common prefixes of the blocks), so
`∂(T·γ) = U·γ`. ∎

## Theorem 3

Put `T_j = T·x0^j` (successive single steps), `U_j = ∂T_j`, `j < ℓ`. By Theorem 2 all `T_j`
have the same partition `π`, since consecutive ones are joined by edges out of `A`.
- `x0` maps `00 ↦ 0`, `01 ↦ 10`, `1 ↦ 11`. So for `j ≥ 0`, the leaves of `T_{j+1}` below
  `10` are the images of the leaves of `T_j` below `01`, and the leaves of `T_{j+1}` below
  `01` are the images of the leaves of `T_j` below `001`.
- By induction, for `0 ≤ k ≤ ℓ − 2` the leaf-index set `I_k` of `T_{k+1}` below `10` equals
  the leaf-index set of `T_0` below `0^{k+1}1`. These nodes exist, since `T_k·x0` is
  defined, so `T_k` splits `0`, and `T_k/0 = T_0/0^{k+1}` by the same induction. The sets
  `I_0, …, I_{ℓ−2}` are nonempty and pairwise disjoint, since the nodes `0^{k+1}1` are
  pairwise incomparable.
- Fix `k ≤ ℓ − 2`. `T_{k+1} ∈ A` splits `∅` and `1`, because `T_{k+1} = T_k·x0` has leaves
  under `10` and `11`. By Theorem 1, `U_{k+1}` splits them too, unless
  `(U_{k+1}, T_{k+1}) = ({∅},{0,1})`, which is impossible as `T_{k+1}` splits `1`. So the
  leaves of `U_{k+1}` below `10`, or `10` itself, cover exactly `I_k`. Hence `I_k` is a
  union of at least one block of `π`.
- Disjoint nonempty unions of blocks: `m = |∂T| ≥ ℓ − 1`. ∎

## Corollary 4

Consider the partial bijection `T ↦ T·x0`. Its orbits are finite paths.
- Delete the points of `B`. Each path splits into *A-segments* `s_1, …, s_L` (in forward
  order), each followed by an *exit*: either `e = s_L·x0 ∈ B`, or `s_L·x0` undefined.
- Let `G_ℓ` be the set of `T ∈ A` with `T, T·x0, …, T·x0^{ℓ−1}` all defined and in `A`. A
  point `s_i ∈ A ∖ G_ℓ` is one of the last `ℓ − 1` points of its segment.
- Put `μ(e) = 0` for an undefined exit. For each `i`,
  `μ(s_i) ≤ μ(e) + Σ_{k=i}^{L} |μ(s_k·x0) − μ(s_k)|`, where the `k = L` term is `|μ(e) −
  μ(s_L)|`. With Moore's convention it is the `bd_{x0}` term of `s_L` in both exit cases.
- So the last `ℓ − 1` points of a segment carry mass at most `(ℓ − 1)(μ(e) + V_σ)`, with
  `V_σ` the `bd_{x0}` terms of the points of the segment.
- The segments are disjoint and each `e ∈ B` has at most one `x0`-predecessor. Summing,
  `μ(A ∖ G_ℓ) ≤ (ℓ − 1)(μ(B) + bd_{x0}(μ)) ≤ (ℓ − 1)(c + 1)·bd(μ)`.
- By Theorem 3, `{T ∈ A : |∂T| ≥ ℓ − 1} ⊇ G_ℓ`, and
  `μ(G_ℓ) ≥ μ(𝒯) − μ(B) − μ(A ∖ G_ℓ) ≥ μ(𝒯) − (c + (ℓ − 1)(c + 1))·bd(μ)`.
- If `bd(μ) < ε μ(𝒯)` and `ℓ − 1 = ⌊1/(2(c+1)ε) − c/(c+1)⌋ ≥ 0`, then
  `(c + (ℓ−1)(c+1))ε ≤ 1/2`, so the mass exceeds `μ(𝒯)/2`. ∎

## Proposition 5

- `V ∈ Full_m` splits every node of `W`, so its leaves lie below `00`, `01`, `100`, `101`,
  `110` or `111`. None of these is in `W`, and no leaf of `V` is in `W`. So `V` is
  window-avoiding for `S = σ_β(V)` whatever `β` is.
- `V` is dominated by `S` by construction. By Theorem 1, `S·γ` is defined iff `V·γ` is, and
  `V·γ` is defined for all `γ`.
- `σ_β(V·γ) = σ_β(V)·γ` is the grafting equivariance (Theorem 2 of
  `tree-grafting-inflations-kill-superlinear-ratio-proof`, re-proved in our Theorem 2 above:
  blocks are carried to blocks with the same index). Hence with `∂(σ_β V') = V'` on
  `σ_β(𝒯_m)` (well defined as `σ_β` is injective), (E′) holds at every point of
  `σ_β(Full_m)`. ∎

The remark "What this means for `H_k`" in the target is interpretation, and uses only
Theorem A(3) of the required claim for the comparison `Ack_k(Ω(1/ε)) ≪ Ack_{k+1}(Ω(log 1/ε))`.
