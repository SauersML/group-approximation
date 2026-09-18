# Referee report (gq-referee-b, citation/hypothesis lens): the odometer 2V is fp, simple, and contains BS(1,2)

**Reviewed.** `odometer-2v-is-fp-simple-and-contains-bs12` and its `-proof` (lane gq-affq, 6b7a38f77), read on
origin/main.

**Sources read.** The local TeX in `gq/src/kep/`:
- Li, arXiv:2110.04505v2;
- Matui, arXiv:1210.5800;
- Exel–Pardo, arXiv:1409.1107.

**Verdict: PASS on (a), (b) and (c).** Every cited statement matches its source, and every hypothesis is
verified in the route. There are three minor notes, all non-blocking.

## (a) Li, Example ex:ZS (III) and Theorem thm:k-graphs

**The setting of Example ex:ZS** (l.2372), verbatim: "Assume that we are in the setting of §s:Gars-deg of a cancellative
small category C with a degree map d: C → P. Assume that the self-similar action G ↷ C satisfies d(g.a) = d(a) for all
g ∈ G and a ∈ C. If P is right cancellative, then D := C ⋈ G is automatically right cancellative up to =^* [...] This
means that if C satisfies the same assumptions as for Theorem thm:deg, and condition (F) holds, then [...]".

**Case (III)** (l.2378): "If P = Z_{≥0}^k and S_P, ε_j are as in §ss:k-graphs, for all v ∈ C^0 and 1 ≤ j ≤ k, we have
#v d^(-1)(ε_j) v ≥ 2, and if X ⊆ Ω_∞ is a closed invariant subspace, then [...] F((I_l(D) ⋉ X̃)^Ỹ_Ỹ) is of type F_n
if D^*(w,w) is of type F_n for all w ∈ D^0."

The hypotheses, checked one by one:

| Hypothesis | Check |
|---|---|
| `C` cancellative with a degree map | `Λ = F_2^+ × F_2^+` is cancellative, and `d(p,w) = (|p|,|w|)`. |
| The assumptions of Theorem thm:deg (l.2059) | Li requires "finite C^0 [...] P-valued degree map d such that v d^(-1)(p) < ∞" together with (UFP*) and `d^(-1)(1) = C^*` (l.1835). All hold: one vertex, finitely many words of each degree, unique factorization, and no nontrivial invertibles. The conditions on `P = Z_{≥0}^2` are Li's own, from §ss:k-graphs. |
| `d(g.a) = d(a)` | Step A. |
| Two edges of each colour | Holds. |
| Condition (F) | Definition, l.1454: "for all v ∈ C^0, a, b ∈ C^*(v,v) and U = X(v;e) ∈ 𝔛, [a,U] = [b,U] in 𝐂 implies a=b". Sufficient condition, l.1456: "Note that (F) holds if, for instance, C is right cancellative." |
| `D^*(w,w)` of type F_n | `rem:ZS-Stab` (l.2361): "If we even have C^* = C^0, then D^*(ṽ,ṽ) = St(G,v)". Here that is `Z`, which is of type F_∞. |
| `Y` | The monotonicity at l.1178 (`f' ⊆ f` gives `X(d(s); f') ⊇ X(d(s); f)`) gives `X(v;∅) = vX = X`. With `e_P = ∅`, this matches thm:k-graphs' "Y_v = X(v; v d^(-1)(e_P))". |

**Right cancellativity of `D`, needed for (F).** (F) is applied to `D`, so `D` must be right cancellative. The route's
step A shows this.
- From `(λ,g)(μ,h) = (λ',g')(μ,h)`, degrees and unique factorization give `λ = λ'` and `g.μ = g'.μ`.
- The cocycle identity `(g^(-1)g')|_μ = (g|_μ)^(-1) g'|_μ = 1`, together with pseudo-freeness (`a^n` strongly fixes
  `μ` only if `n = 0`), gives `g = g'`.
- **Correct.**

**The full group.** Li l.747: "the topological full group of G is given by the group of compact open bisections a of G
which are global, in the sense that r(a) = X = s(a)".

**Note 1.** The identification `Ω_∞ = C × C`, the infinite-path space of the one-vertex 2-graph, rests on Li's Part I
(arXiv 2021), which is not in this file. It is standard for finite 2-graphs without sources. The theorem only needs
`X` to be a closed invariant subspace of `Ω_∞`, so this is safe.

## (b) Matui, Theorem simple2

- **Standing assumption** (l.1183): "we let G be an essentially principal étale groupoid whose unit space is a Cantor
  set".
- **Hausdorff is explicit, not implicit.** l.347: "by an étale groupoid we mean a second countable locally compact
  Hausdorff groupoid such that the range map is a local homeomorphism". So the Hausdorff verification in step B is
  required, and it is done:
  - the unit-germ set of `Z(λ,n,μ)` is `μX` or empty, hence clopen;
  - second countability holds, since there are countably many basic bisections.
- **Essentially principal** (l.365): "When the interior of G' is G^(0), we say that G is essentially principal."
  This is exactly the effectiveness proved in step B: only units act trivially on open sets.
  - **Note 2.** The route's extra "points with trivial isotropy are dense" is not needed for Matui's definition. It is
    harmless.
- **Definition pi** (l.1194): "A clopen set A ⊂ G^(0) is said to be properly infinite if there exist compact open
  G-sets U, V ⊂ G such that s(U) = s(V) = A, r(U) ∪ r(V) ⊂ A and r(U) ∩ r(V) = ∅. [...] We say that G is purely
  infinite if every clopen set A ⊂ G^(0) is properly infinite."
  - Step D's `U`, `V` append the colour-2 letter `0` or `1` inside each cylinder. So `s = A`, and the ranges are
    disjoint subsets of `A`.
  - **Match.**
- **Minimal** (l.356): "When every G-orbit is dense in G^(0), G is said to be minimal". Holds, since `2V ⊆ F` acts
  minimally.
- **Theorem simple2** (l.1466): "Suppose that G is purely infinite and minimal. Then any non-trivial subgroup of [[G]]
  normalized by the commutator subgroup D([[G]]) contains D([[G]]). In particular, D([[G]]) is simple." **Match.**
- **Matui's `[[G]]` equals Li's `F(·)`.**
  - Definition defoftfg (l.396): `[[G]]` is the set of `α ∈ Homeo(G^(0))` with `α = π_U` for a compact open G-set
    `U`.
  - l.412–413: "For α ∈ [[G]] the compact open G-set U as above uniquely exists [...] because G is essentially
    principal."
  - So `U ↦ π_U` is a bijection from Li's global compact open bisections onto `[[G]]`, and it is a group isomorphism.
  - **Yes, they match.**
- **Perfectness.**
  - All proper `σ_μ` are conjugate in `2V`, and `σ_μ = σ_(μ(ε,0)) σ_(μ(ε,1))`, so their common class is `0`.
  - `qs = σ_((1,∅))`, and `2V` is simple (Brin).
  - So `F_ab = 0`, and `F = D(F)` is simple. **Correct.**

## (c) Exel–Pardo, the Katsura triple A = (2), B = (1)

Exel–Pardo, around l.570–585: "denote the set of edges in E from i to j by {e_{i,j,n}: 0 ≤ n < A_{i,j}}. Given m ∈ Z [...]
we first perform the Euclidean division of mB_{i,j}+n by A_{i,j}, say mB_{i,j}+n = k̂ A_{i,j} + n̂ [...] We then put
σ_m(e_{i,j,n}) := e_{i,j,n̂} [...] φ(m, e_{i,j,n}) := k̂". The self-similarity equation (l.553) is
"g(αβ) = (gα)(φ(g,α)β)".

- **With `N = 1`, `A = (2)`, `B = (1)`, `m = 1`:**
  - `e_0 ↦ e_1` with cocycle `0`;
  - `e_1 ↦ e_0` with cocycle `1`.
- So `1·(0w) = 1w` and `1·(1w) = 0(1·w)`. That is `τ(0w) = 1w` and `τ(1w) = 0τ(w)`, the binary odometer. **Match.**
- Step A's formula, `a^n·p` equals the word of `b+n mod 2^j` with restriction `a^(⌊(b+n)/2^j⌋)`, is the iterate of
  this cocycle, in little-endian binary.

## Other checks

- **Compatibility on the 2-graph.** `a·(xy) = (a·x)y` and `a·(yx) = y(a·x)` for a colour-1 letter `x` and a colour-2
  letter `y`. The restrictions agree. So the action is well defined on `F_2^+ × F_2^+`.
- **BS(1,2).**
  - `usu^(-1)(x_0x', y) = (x_0 τx', y) = s^2(x_0x', y)`, since `τ^2(jw) = jτ(w)`.
  - Injectivity holds because every nontrivial normal subgroup of `BS(1,2)` meets `Z[1/2]`. It then contains an
    integer power of the generator, and `s` has infinite order. Correct.
- **Note 3.** "Not claimed" is accurate: the node proves no embedding into `nV` and no copy of `Aff(Q)`.
