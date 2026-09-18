---
rg: 2
id: rational-leavitt-path-k1-k2-scalar-dichotomy
kind: claim
title: For a rational Leavitt path algebra, either the rational scalars die in K_1 or the rational symbols survive in K_2, both in infinitely generated amounts
distinct_from:
  non-ibn-rational-hosts-have-infinite-elementary-centre: that kills hosts with [1] of finite order through the K_1 scalars; this shows that the surviving Leavitt path case, [1] of infinite order, is paid for in K_2.
  rational-scalars-obstruct-fp-elementary-hosts: that is the K_1 (centre) criterion for PE_N(R); this computes both K_1 and K_2 images of Q for Leavitt path algebras over Q.
  abc-leavitt-path-k-theory-exact-sequence: that is the imported long exact sequence; this is its consequence for the unital map Q -> L_Q(E).
---

**ESTABLISHED** by `rational-leavitt-path-k1-k2-scalar-dichotomy-proof` (lane proof,
not independently reviewed; elementary consequence of Ara--Brustenga--Cortiñas; no
novelty claimed).

**Statement.** Let `E` be a finite graph with no sinks, `L = L_Q(E)` (unital), and
`c = [1_L] ∈ K_0(L)`. For `n = 1, 2` the unital map `Q -> L` sends `x ∈ K_n(Q)` to
`x ⊗ c` in the subgroup `K_n(Q) ⊗ K_0(L) ⊆ K_n(L)`. Hence:
1. **K_1.** `ker(Q^x -> K_1(L))` is finitely generated if and only if `c` has infinite
   order. In that case it lies in `{±1}`. If `c` has finite order `m`, it contains
   `(Q^x)^m`.
2. **K_2.** The image of `K_2(Q) -> K_2(L)` is `0` if `c = 0`. Otherwise it is not
   finitely generated.
3. **Dichotomy.** For no finite sinkless `E` are both groups finitely generated:
   - `c = 0`: the scalars die in `K_1`;
   - `c` of infinite order: the symbols survive in `K_2`;
   - `c` of finite order `>= 2`: both fail.

**Example of the infinite-order case.** Take two vertices, where vertex 1 emits two
loops and two arrows to vertex 2, and vertex 2 emits one arrow to vertex 1 and three
loops. Use the graph-monoid presentation `[v] = Σ_(s(e)=v) [r(e)]`. Then
`K_0 = Z^2 / Z(1,2) ≅ Z` via `(a,b) -> 2a - b`, and `c = (1,1) -> 1`. The graph is
strongly connected and every cycle has an exit, so `L` is purely infinite simple.
Its `K_1` detects `Q^x` up to `±1`, but `K_2(L) ⊇ K_2(Q) ⊗ Z·c ≅ K_2(Q)`.

**Why it matters for `gl-n-q-embeds-in-fp-simple-group`.** By
`non-ibn-rational-hosts-have-infinite-elementary-centre`, a purely infinite ring host
needs `[1]` of infinite order in `K_0` and `K_1` detecting `Q^x`. For Leavitt path
algebras over `Q`, that escape forces the full symbol group `K_2(Q)`, which is not
finitely generated, into `K_2`. A finitely presented host built over such an `L` by
adding generators (a Leavitt--Nekrashevych or resolvent completion `R ⊇ L_Q(E)`)
therefore needs two things:
- it must cut the image of `K_2(Q)` down to a finitely generated group,
  which is necessary whenever `K_2(N,R)` is central in `St_N(R)`;
- it must not reintroduce `ker(Q^x -> K_1)`. The `K_1` kernel only grows under
  `L -> R`, while the `K_2` image can shrink.

Whether one ring can do both is open. It is the natural next target for the
Steinberg and `K_2` lanes.
