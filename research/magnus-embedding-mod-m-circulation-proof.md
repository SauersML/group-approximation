---
rg: 2
id: magnus-embedding-mod-m-circulation-proof
kind: route
title: The Magnus image of N is exactly the module of integral circulations on the Cayley graph, which is pure in the base, so reducing lamps modulo m has kernel [N,N]N^m
target: magnus-embedding-mod-m-into-wreath-product
requires:
  - magnus-embedding-f-over-n-prime-into-wreath-product
---

Direct proof (2026-09-13, lane `bh-solvable-general`). Not independently reviewed.
Notation as in the target. Write `ḡ = g^μ` for `g ∈ F`.

## Step 0. The cocycle `d`

Write `φ(w) = (w^μ, d(w))` with `d : F -> T`. From the product rule
`(g, t)(h, u) = (gh, t + g·u)` in `T ⋊ G`:

- `d(uv) = d(u) + u^μ · d(v)`;
- `d(x_i) = t_i`;
- `d(u^(-1)) = -(u^μ)^(-1) · d(u)`.

On `N` the twist disappears, so `d|_N : N -> T` is a homomorphism of groups. It is
also `G`-equivariant under conjugation: for `ĝ ∈ F` with image `g` and `v ∈ N`,

```text
d(ĝ v ĝ^(-1)) = d(ĝ) + g·d(v) + g·d(ĝ^(-1)) = g·d(v),
```

using `v^μ = 1` and `g·d(ĝ^(-1)) = -d(ĝ)`. By the integral Magnus embedding
(`magnus-embedding-f-over-n-prime-into-wreath-product`), `ker φ = [N,N]`, so
`ker(d|_N) = [N,N]`.

## Step 1. `d(N)` lies in the kernel of the boundary map

Define the left `ZG`-linear map `ε : T -> ZG` by `ε(Σ_i a_i t_i) = Σ_i a_i (x̄_i - 1)`.
By induction on word length, `ε(d(w)) = w^μ - 1` for all `w ∈ F`:

- it holds for `x_i`;
- `ε(d(uv)) = (ū - 1) + ū(v̄ - 1) = ūv̄ - 1`;
- `ε(d(u^(-1))) = -ū^(-1)(ū - 1) = ū^(-1) - 1`.

So `ε(d(v)) = 0` for `v ∈ N`.

## Step 2. `ker ε ⊆ d(N)`: circulations are sums of cycles

**The graph.** Let `Γ` be the Cayley graph of `G` with respect to `x̄_1, ..., x̄_r`:
vertex set `G`, and one directed edge `e(g, i)` from `g` to `g x̄_i` for each `g` and
`i`. Parallel edges and loops are allowed. The map

```text
Σ_(g, i) c_(g,i) g t_i  <->  (e(g, i) -> c_(g,i))
```

identifies `T` with the finitely supported integer functions on edges. Identifying
`ZG` with finitely supported integer functions on vertices,
`ε(t) = Σ c_(g,i) (g x̄_i - g)` is the boundary `∂c`: `+c` at each head and `-c` at
each tail. So `ker ε` is the group of finitely supported integral circulations.

**Paths.** For a word `w = x_(i_1)^(η_1) ... x_(i_n)^(η_n)`, `d(w)` is the signed
edge function of the path in `Γ` that starts at `1` and reads `w`:
- a letter `x_i` traverses `e(g, i)` forwards, contributing `+1`;
- a letter `x_i^(-1)` at vertex `g` traverses `e(g x̄_i^(-1), i)` backwards,
  contributing `-1`.

Induction: `d(x_i) = t_i` is the edge `e(1, i)`, and
`d(x_i^(-1)) = -x̄_i^(-1) t_i` is minus the edge `e(x̄_i^(-1), i)`. The rule
`d(uv) = d(u) + ū·d(v)` appends the path of `v`, translated to start at `ū`.

**Decomposition.** Let `c ≠ 0` be a finitely supported integral circulation, and
induct on `|c| = Σ_e |c(e)|`.
- Reverse every edge with `c(e) < 0`. This gives a finite directed multigraph with
  positive weights and zero net flow at every vertex.
- Start at the tail of a weighted edge and keep leaving each vertex along an
  outgoing weighted edge. One exists because inflow equals outflow and the inflow
  is positive.
- The support is finite, so a vertex repeats. This gives a closed directed path
  `C`, with the signs of the original orientation restored. Let `χ_C` be its signed
  edge function.
- Then `c - χ_C` is a circulation with `|c - χ_C| < |c|`.

So `c` is a finite sum of signed edge functions of closed paths.

**Cycles are in `d(N)`.** A closed path starting at a vertex `g` reads a word `v ∈ F`
with `v̄ = 1`, i.e. `v ∈ N`. Its edge function is `g·d(v)`. For a lift `ĝ` of `g`,
Step 0 gives `g·d(v) = d(ĝ v ĝ^(-1))`, and `ĝ v ĝ^(-1) ∈ N`. Since `d|_N` is a
homomorphism, every finite signed sum of such functions is in `d(N)`. So
`ker ε = d(N)`.

## Step 3. The kernel of `ρ_m ∘ φ`

**`[N,N]N^m` is in the kernel.** `[N,N] ⊆ ker φ`. For `u ∈ N`,
`φ(u^m) = (1, m·d(u))`, which reduces to `(1, 0)` modulo `m`.

**The kernel is in `[N,N]N^m`.** Let `u ∈ ker(ρ_m ∘ φ)`.
- The top coordinate gives `ū = 1`, so `u ∈ N`. The lamps give `d(u) ∈ mT`, say
  `d(u) = m·t` with `t ∈ T`.
- By Step 1, `m·ε(t) = ε(d(u)) = 0` in `ZG`. The group ring `ZG` is torsion-free as
  an abelian group, so `ε(t) = 0`.
- By Step 2, `t = d(v)` for some `v ∈ N`.
- `d|_N` is a homomorphism, so `d(u v^(-m)) = d(u) - m·d(v) = 0`. By Step 0,
  `u v^(-m) ∈ [N,N]`.
- So `u ∈ [N,N] N^m`.

**The wreath product.** `T/mT` is the free `(Z/m)G`-module on `t_1, ..., t_r`. The
identification used in the import, coordinates `g -> (n_(g,1), ..., n_(g,r))` with
left translation, gives `(T/mT) ⋊ G ≅ (Z/m)^r wr G`. `∎`

**What is used.** Only the integral Magnus embedding. The rest is the elementary
decomposition of finitely supported integral circulations on a graph into cycles.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/bh-solvable-general-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
