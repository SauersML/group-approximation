# Double-coset transport (T_j) holds at every depth

Author: swarm-0917-w18-w18-fp-pull (host-geometry), 2026-09-19.
Target: `fpbs-mal-overfold-merges-never-help` (O). Scripts:
`experiments/fpbs-doublecoset-transport-2026-09-17/`.

## Summary

The depth-shift reduction
(`research/artifacts/fpbs-overfold-depth-shift-reduction-2026-09-19.md`,
Lemma D and Corollary R) proved `(O) ⇔ (O'_j)` only for `j ≤ 4`. It needed
one finite input for larger `j`:

```text
(T_j):  U_j ∩ L_1 = U' = φ(U_{j-1}).
```

- `U_j` is the union of the nontrivial double cosets `HgH`, with
  `H = L_{j+1}`, realised by vertex pairs of the `(a,b)`-core `C_{j+1}`.
- `U'` is the same union for the core `C'` of `H` in the basis `(a, t_1)`
  of `L_1`.

This note proves (T_j) for **every** `j ≥ 1`, by a short Bass–Serre
argument. The key fact is that the `φ`-image of a minimal subtree is
explicit, and only its leaves need pruning.

**Consequences.** All of these hold modulo the cited relative-rank form, on
`L_{j+1}`-transitive `Q`:

- Lemma D holds for all `j` and all `i ≤ j`. The general case uses
  (T_j), …, (T_{j-i+1}), and all of them now hold.
- Corollary R holds for all `j`. That is, (O) at depth `j` is equivalent to
  (O'_j): level-0 seeds, those whose images in `C_1` differ, are never
  needed.

**What this does not do.**
- It does not prove (O'_j).
- It does not fix the recorded caveat: a weak level-0 bound compounds to
  `c^j`.

**By-product.** An explicit recursion `C_{j+1} = Exp(C_j)` for the cores.
It is verified against Stallings folding for `j ≤ 8`.

## 1. Setting

- `X = T(L; a, b)` is the Cayley tree. Its vertices are the elements of
  `L`, and `L` acts on the left.
- For a nontrivial finitely generated `B ≤ L`, `T_B ⊂ X` is its minimal
  invariant subtree. It has no leaves, and `T_B / B` is the core `C_B`.
- The link of a vertex is the set of letters labelling its edges in the
  subtree. Links are `L`-invariant.
- As in the cited artifact (§2, "Why (T_j) is a real condition"),
  `HgH` is realised in `C` iff `T_H ∩ g T_H ≠ ∅` in `X`. Likewise, `HgH`
  (with `g ∈ L_1`) is realised in `C'` iff `T'_H ∩ g T'_H ≠ ∅` in
  `T(L_1; a, t_1)`.
- `Y = T_{L_1} ⊂ X`, and `C_1 = Y / L_1` has three vertices:
  - vertex 0, with an `a`-loop;
  - vertex 1;
  - vertex 2.

  Its edges are `b: 0→1`, `a: 1→2` and `b: 1→2`.

## 2. The φ-expansion of a subtree

**The map `f`.** Define `f : V(X) → V(Y)` by `f(w) = φ(w)`. It is injective
and `φ`-equivariant: `f(hw) = φ(h) f(w)`.

**The three sheets of `Y`.** `L_1` acts freely on `Y`, and the vertex types
of `Y` are the orbits of `1`, `b` and `b²`. So every vertex of `Y` is
exactly one of the following, each determined by `w ∈ L`:

```text
f(w) = φ(w)          (type 0)
α(w) = φ(w) b        (type 1)
β(w) = φ(w) b²       (type 2)
```

**The edges of `Y`.** They are the lifts of the four edges of `C_1`:

```text
a : f(w) → f(wa)
b : f(w) → α(w)
a : α(w) → β(wb)      since φ(w) b a = φ(wb) b²
b : α(w) → β(w)
```

**The images of the edges of `X`.** An `a`-edge `w — wa` of `X` goes to the
`a`-edge `f(w) — f(wa)`. A `b`-edge `w — wb` goes to the reduced path
`φ(b) = b a b⁻¹ b⁻¹`:

```text
f(w) —b→ α(w) —a→ β(wb) ←b— α(wb) ←b— f(wb).
```

**The expansion of a subtree.** For a leafless subtree `B ⊂ X`, let `f(B)`
be the union of these images. It is a subtree of `Y`, because it is
connected. Its vertices are:

- `f(v)` for `v ∈ B`;
- `α(v)` for each `v` that has a `b`- or `b⁻¹`-edge in `B`;
- `β(w)` for each edge `wb⁻¹ — w` of `B`.

**Degrees in `f(B)`.** Using `deg_B ≥ 2`:

- `β(w)` has degree 2, with neighbours `α(wb⁻¹)` and `α(w)`.
- `α(v)`, when present, is joined to three kinds of neighbour:
  - `f(v)`;
  - `β(vb)`, when `v — vb ∈ B`;
  - `β(v)`, when `vb⁻¹ — v ∈ B`.

  So `α(v)` has degree `1 + #(b-letters of v)`, which is at least 2.
- `f(v)` has degree `#(a-letters of v) + [v has a b-letter]`. This equals 1
  iff `link_B(v) = {b, b⁻¹}`. The other possibility, one `a`-letter and no
  `b`-letter, would give `deg_B(v) = 1`.

**Pruning.** Delete the leaves `f(v)` with `link_B(v) = {b, b⁻¹}`. The only
neighbour of such an `f(v)` is `α(v)`, which drops from degree 3 to 2. So no
new leaves appear. Write `E(B)` for the leafless subtree that remains. Its
vertices are:

```text
f(v)  for v ∈ B whose link contains a or a⁻¹,
α(v)  for v ∈ B whose link contains b or b⁻¹,
β(w)  for each edge wb⁻¹ — w of B.
```

**Lemma 1.** `E(T_{L_j}) = T_{L_{j+1}}` for every `j ≥ 0`.

*Proof.* Let `A = T_{L_j}`. Then `E(A)` is `φ(L_j) = L_{j+1}`-invariant,
by equivariance. Its quotient `E(A)/L_{j+1}` is finite, since it is covered
by the expansion of the finite graph `C_j`. The quotient also has no
vertices of degree ≤ 1, because the action is free and `E(A)` is leafless.
Now `T_{L_{j+1}} ⊂ E(A)`, so the finite graph `G = E(A)/L_{j+1}` contains
the core `C_{j+1}`. Both are quotients of trees by the same free action, so
the inclusion is an isomorphism on `π_1`. Hence the closure of
`G ∖ C_{j+1}` is a forest in which each component meets `C_{j+1}` in one
point. A nonempty such forest has a leaf of `G`, and `G` has none.
Hence `G = C_{j+1}` and `E(A) = T_{L_{j+1}}`. ∎

**Corollary (explicit cores).** `C_{j+1} = Exp(C_j)`, where `Exp` is the
quotient of the recipe above:

- vertices `(0,v)` for `v` whose link has an `a`-letter;
- vertices `(1,v)` for `v` with a `b`-letter;
- vertices `(2,w)` for each `b`-edge `v → w` of `C_j`.

`transport.py` checks that `Exp(C_j)` equals the Stallings folding of
`⟨a, t_{j+1}⟩` as based labelled graphs, for `j ≤ 8`. Its output is
`transport_j9.txt`, with `|C_j| = 1, 3, 8, 20, 49, 119, 288, 696, 1681,
4059`.

Two further regularities hold for `j ≤ 9`; they are observed, not proved:
- `|C_{j+1}| = 2|C_j| + |C_{j-1}| + 1`;
- `#{v : link {b,b⁻¹}} = |C_{j-2}|`.

## 3. Proof of (T_j) for all j ≥ 1

**Proposition 2.** Let `B ⊂ X` be leafless and `h ∈ L`. Then
`E(B) ∩ E(hB) = ∅` while `B ∩ hB ≠ ∅` iff `B ∩ hB` is a single vertex `v`
and the two links at `v` are `{b, b⁻¹}` and `{a, a⁻¹}`, in either order.
In every other case, `E(B) ∩ E(hB) ≠ ∅` iff `B ∩ hB ≠ ∅`.

*Proof.* Equivariance gives `E(hB) = φ(h) E(B)`, and the vertex lists of §2
apply to both subtrees.

(⇒) A common vertex `f(v)`, `α(v)` or `β(v)` forces `v ∈ B ∩ hB`.

(⇐) Suppose `I = B ∩ hB ≠ ∅`. It is a subtree.
- If `I` contains an `a`-edge at `v`, then `f(v)` lies in both.
- If `I` contains a `b`-edge `v — vb`, then `α(v)` lies in both.

Otherwise `I = {v}`. Then `f(v)` lies in both unless one of the links at `v`
has no `a`-letter, and `α(v)` lies in both unless one has no `b`-letter.
`β(v)` would need a common edge. Both links have size ≥ 2, so failure means
exactly that one link is `{b, b⁻¹}` and the other is `{a, a⁻¹}`. In that
case the two links are disjoint, so `I = {v}` does happen. ∎

**Lemma 3.** For every `j ≥ 0`, no vertex of `C_j` has link `{a, a⁻¹}`.

*Proof.* By induction on `j`. For `C_0`, the rose, every link is all four
letters. For the step, use §2 with `B = T_{L_j}` and `E(B) = T_{L_{j+1}}`.
The possible links are:
- at `α(v)`: a subset of `{b⁻¹, a, b}`, with no `a⁻¹`;
- at `β(w)`: exactly `{a⁻¹, b⁻¹}`;
- at `f(v)`: the `a`-letters of `link_B(v)`, plus `b` if `v` has a
  `b`-letter.

So `f(v)` has link `{a, a⁻¹}` iff `link_B(v) = {a, a⁻¹}`, which the
induction hypothesis excludes. ∎

**Theorem 4. (T_j) holds for every `j ≥ 1`.**

*Proof.* Let `g ∈ L_1 ∖ H`, where `H = L_{j+1}`, and write `g = φ(h)` with
`h ∉ L_j`.
- `HgH` is realised in `C` iff `T_H ∩ g T_H ≠ ∅` in `X`. By Lemma 1, with
  `A = T_{L_j}`, this is `E(A) ∩ E(hA) ≠ ∅`, because
  `g T_H = φ(h) E(A) = E(hA)`.
- `φ⁻¹` identifies `T(L_1; a, t_1)` with `X` and carries `T'_H` to `A`. So
  `HgH` is realised in `C'` iff `A ∩ hA ≠ ∅`.

Links of `hA` are links of `A` translated. By Lemma 3, `A` has no vertex
with link `{a, a⁻¹}`, so the exceptional case of Proposition 2 cannot occur.
Hence the two conditions agree:

```text
U_j ∩ L_1 = { g ∈ L_1 ∖ H : HgH realised in C }
          = { g : HgH realised in C' }
          = U'.
```

∎

**Remarks.**
- Proposition 2 shows exactly where basis-dependence could have bitten.
  For a general `B`, `(T)` fails as soon as `C_B` has both a
  `{b, b⁻¹}`-vertex and an `{a, a⁻¹}`-vertex. The chain `L_j` never
  produces the second kind.
- It also explains the dead end recorded in the cited artifact. A
  `{b, b⁻¹}`-vertex `v` of `C_j` loses its principal vertex `f(v)`, which
  is where the principal-vertex counts 3, 7, 17, 41 come from. Types
  through such `v` are still realised in `C_{j+1}`, via `α(v)`.
- **Independent check.** The tree-projection script
  `experiments/fpbs-overfold-breaker-2026-09-17/doublecoset_check.py`,
  rerun with `jmax = 6`, gives SET EQUAL for `j = 1..6`, with 1, 12, 88,
  560, 3381 and 19992 level-≥1 types. The output is in
  `experiments/fpbs-doublecoset-transport-2026-09-17/doublecoset_j6.txt`.
  Before this, the check went only to `j ≤ 4`.

## 4. Consequence for (O)

With Theorem 4, the depth-shift artifact's Lemma D holds for all `j ≥ 1` and
`i ≤ j`, on `L_{j+1}`-transitive `Q`, modulo the cited relative-rank form:

```text
deep_j^{≥i}(Q) = deep_{j-i}(Q^{(i)})   and   law_j(Q) = law_{j-i}(Q^{(i)}).
```

Its Corollary R therefore holds at every depth: (O) at depth `j` for all
`L_{j+1}`-transitive `Q` is equivalent to (O'_j),
`deep_j(Q) = deep_j^{≥1}(Q)`.

**What remains open for (O).**
- Level-0 domination (O'_j) itself. By Lemma 1, level-0 seeds are exactly
  the `g ∉ L_1` with `T_H ∩ g T_H ≠ ∅`. Since `T_H ⊂ Y`, these satisfy
  `Y ∩ gY ≠ ∅` with `g ∉ L_1`, which is the bounded overlap that gives
  tree size ≤ 3.
- The `L_{j+1}`-intransitive scope.
- The weak form `deep ≥ c · law` with `c` uniform in `j`. This does not
  follow from a weak level-0 bound.
