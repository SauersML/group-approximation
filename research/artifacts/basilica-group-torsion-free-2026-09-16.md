# The Basilica group: torsion-freeness, free abelian subgroups, and the substitution endomorphism

Proof artifact for `basilica-group-is-torsion-free-and-contains-every-z-n` (route
`basilica-group-is-torsion-free-and-contains-every-z-n-proof`). Swarm lane, 2026-09-16.
Every statement below is proved here from the recursion alone. The only outside inputs are
standard facts about free groups, HNN extensions and cohomological dimension. The classical
source for torsion-freeness is Grigorchuk–Żuk, IJAC 12 (2002) 223–246, whose title asserts
it. That paper was not fetched, and nothing below depends on it.

## 0. Conventions

- `T` is the rooted binary tree with vertex set `{0,1}^*`. Automorphisms act on the right,
  `v ↦ v^g`, and `gh` means "first `g`, then `h`". This is the convention of Bartholdi–Virág,
  arXiv:math/0305262v1, Section 1.
- For `g, h ∈ Aut(T)`, `(g,h)` sends `0v ↦ 0v^g` and `1v ↦ 1v^h`. `ε` sends `iv ↦ (i+1 mod 2)v`.
  Every automorphism is uniquely `(g_0,g_1)ε^s` with `s ∈ {0,1}`.
- Composition rule, checked on `0v` and `1v`:

  `(p_0,p_1)ε^c · (q_0,q_1)ε^s = (p_0 q_c , p_1 q_{c+1}) ε^{c+s}` (indices mod 2).

  In particular `ε(q_0,q_1) = (q_1,q_0)ε`.
- Commutators and conjugates: `x^y = y^{-1}xy` and `[x,y] = x^{-1}y^{-1}xy`.
- The **Basilica group** is `B = ⟨a,b⟩ ≤ Aut(T)` with

  `a = (1, b)`, `b = (1, a)ε`.

  Hence `a^{-1} = (1, b^{-1})` and `b^{-1} = ε(1,a^{-1}) = (a^{-1}, 1)ε`.
- `X = {a^{±1}, b^{±1}}`. For a word `w` over `X`: `|w|` is its length, `n_b(w)` is the number of
  letters `b^{±1}`, and `ε_a(w)`, `ε_b(w)` are the exponent sums.

## 1. Section words

Each letter `x ∈ X` has exactly one nontrivial section. Its index `m(x)` and value `x'` are:

| `x` | decomposition | `m(x)` | `x'` | `ε`-part |
|---|---|---|---|---|
| `a^{±1}` | `(1, b^{±1})` | 1 | `b^{±1}` | 0 |
| `b` | `(1, a)ε` | 1 | `a` | 1 |
| `b^{-1}` | `(a^{-1}, 1)ε` | 0 | `a^{-1}` | 1 |

**Lemma 1.** Let `w = x_1⋯x_n` be a word over `X`, and let `c_k ∈ {0,1}` be the parity of the
number of letters `b^{±1}` among `x_1,…,x_{k−1}`. Let `w_j` (`j = 0,1`) be the word obtained by
concatenating, in order, the letters `x_k'` with `m(x_k) + c_k ≡ j (mod 2)`. Then, as
automorphisms of `T`,

`w = (w_0, w_1) ε^{n_b(w) mod 2}`.

Consequently:

- `|w_0| + |w_1| = |w|`;
- `ε_b(w_0) + ε_b(w_1) = ε_a(w)` and `ε_a(w_0) + ε_a(w_1) = ε_b(w)`;
- `w ∈ St(1)`, the stabilizer of the first level, if and only if `n_b(w)` is even.

*Proof.* Induction on `n`. Write `x_1⋯x_{k−1} = (p_0,p_1)ε^{c_k}`. The letter `x_k` is
`(q_0,q_1)ε^s`, where `q_{m(x_k)} = x_k'` and the other section is trivial. By the composition
rule, coordinate `j` of the product is `p_j q_{j+c_k}`. So `x_k'` is appended to coordinate `j`
exactly when `j + c_k ≡ m(x_k)`, and the `ε`-part becomes `ε^{c_k + s}`. The consequences follow:
each letter contributes one letter to one section; `a^{±1}` contributes `b^{±1}` and `b^{±1}`
contributes `a^{±1}`; and the `ε`-part counts the letters `b^{±1}`. ∎

**Lemma 2 (one-coordinate words).** Let `w` be a freely reduced word over `X` such that `w_0`
or `w_1` is the empty word. Then `w` is one of `a^k`, `a^k b`, `b^{-1}a^k`, `b^{-1}a^k b`
(`k ∈ ℤ`). If moreover `n_b(w)` is even, then `w = a^k` or `w = b^{-1}a^k b`.

*Proof.* Suppose every letter contributes to coordinate `i`. By Lemma 1, a letter `a^{±1}` or
`b` must occur at parity `c_k = i+1`, and a letter `b^{-1}` at parity `c_k = i`. The parity
changes exactly at the letters `b^{±1}`.

- `i = 1`. At parity 0 only `a^{±1}` and `b` are allowed. After a `b` the parity is 1, and only
  `b^{-1}` is allowed there, which would cancel that `b`. So `w = a^k` or `w = a^k b`.
- `i = 0`. At parity 0 only `b^{-1}` is allowed. At parity 1 only `a^{±1}` and `b` are allowed.
  So `w` is empty, or starts with `b^{-1}` followed by a power of `a`. After a subsequent `b`
  the parity is 0, and only `b^{-1}` is allowed, which would cancel. So `w ∈ {1, b^{-1}a^k,
  b^{-1}a^k b}`.

Of these words, the ones with `n_b` even are `a^k` and `b^{-1}a^k b`. ∎

**Lemma 3.** `a` and `b` have infinite order.

*Proof.* `b^2 = (1,a)ε(1,a)ε = (1,a)(a,1) = (a,a)`. Suppose `a^k = 1` with `k ≠ 0` and `|k|`
minimal. Since `a^k = (1, b^k)`, we get `b^k = 1`, so `k` is even (the `ε`-part of `b^k` is
`ε^k`). Then `b^k = (a^{k/2}, a^{k/2})`, so `a^{k/2} = 1`, contradicting minimality. If `b^k = 1`
with `k ≠ 0`, then `k` is even and `a^{k/2} = 1`, which is impossible. ∎

## 2. Exponent sums

**Lemma 4.** If a word `w` over `X` represents `1 ∈ B`, then `ε_a(w) = ε_b(w) = 0`. Hence
`ε_a, ε_b : B → ℤ` are well-defined homomorphisms, and `B^{ab} ≅ ℤ^2` with basis the images of
`a` and `b`.

*Proof.* Induction on `|w|`; the empty word is fine. If `w` is not freely reduced, cancel a pair
`xx^{-1}`; the exponent sums do not change and the length drops. So let `w` be freely reduced,
nonempty, and trivial in `B`. Then `n_b(w)` is even and both section words `w_0, w_1` represent
`1`.

- If both are nonempty, each has length `< |w|` by Lemma 1, so all their exponent sums vanish by
  induction. By Lemma 1, `ε_a(w) = ε_b(w_0)+ε_b(w_1) = 0` and `ε_b(w) = ε_a(w_0)+ε_a(w_1) = 0`.
- Otherwise Lemma 2 gives `w = a^k` or `w = b^{-1}a^k b`, with `a^k = 1`. By Lemma 3, `k = 0`.
  The word `a^0` is empty, and `b^{-1}b` is not reduced, so this case cannot occur.

For the last sentence: the map `ℤ^2 → B^{ab}` sending the basis to the images of `a, b` is onto,
and its composite with `(ε_a, ε_b) : B^{ab} → ℤ^2` is the identity. ∎

## 3. Torsion-freeness

**Theorem 5.** `B` is torsion-free.

*Proof.* We show by induction on `n` that every torsion element of `B` of word length `≤ n` is
trivial. Let `g` be a torsion element, and let `w` be a geodesic word for `g`, so `w` is freely
reduced and `|w| = n`. Since `ε_b : B → ℤ` is a homomorphism (Lemma 4) and `g` has finite order,
`ε_b(g) = 0`. So `n_b(w)` is even and `g = (g_0,g_1) ∈ St(1)`, where `g_j` is represented by
`w_j`. If `g^m = 1`, then `g_0^m = g_1^m = 1`.

- If `w_0` and `w_1` are both nonempty, each has length `< n` (Lemma 1). By induction
  `g_0 = g_1 = 1`, so `g = 1`.
- Otherwise, by Lemma 2, `g` is conjugate to `a^k`, which then has finite order. By Lemma 3,
  `k = 0` and `g = 1`. ∎

## 4. Free abelian subgroups of every rank

**Proposition 6.** For all `x, y ∈ B'`, the automorphism `(x,y)` lies in `B'`. Consequently
`B'` contains a copy of `(B')^{2^k}` for every `k ≥ 0`, `B` contains `ℤ^{2^k}` for every `k`, and
`cd B = ∞`.

*Proof.*

1. The projection `St_B(1) → B`, `h = (h_0,h_1) ↦ h_1`, is onto, because `a = (1,b)` and
   `b^2 = (a,a)` lie in `St_B(1)`.
2. `[a, b^2] = (1,b^{-1})(a^{-1},a^{-1})(1,b)(a,a) = (1, b^{-1}a^{-1}ba) = (1, [b,a])`.
3. For `h = (h_0,h_1) ∈ St_B(1)`, `[a,b^2]^h = (1, [b,a]^{h_1})`. By step 1, every conjugate
   `[b,a]^g` (`g ∈ B`) arises this way. Since `B = ⟨a,b⟩`, `B'` is the normal closure of
   `[b,a]`. Products of these elements show that `(1,y) ∈ B'` for every `y ∈ B'`.
4. For any `x`, the composition rule gives `b^{-1}(x,1)b = (a^{-1},1)ε(x,1)(1,a)ε = (1,x)`.
   So `(y,1) = b(1,y)b^{-1} ∈ B'` for `y ∈ B'`, since `B'` is normal. Hence
   `(x,y) = (x,1)(1,y) ∈ B'`.
5. Let `P_0 = B'` and `P_{k+1} = {(x,y) : x,y ∈ P_k}`. By induction `P_k ≤ B'`: if
   `P_k ≤ B'`, then `P_{k+1} ≤ {(x,y) : x,y ∈ B'} ≤ B'` by step 4. The map
   `(x,y) ↦ (x,y)` is an injective homomorphism `P_k × P_k → Aut(T)`, so `P_k ≅ (B')^{2^k}`.
6. `c = [b,a] ≠ 1`. By the composition rule,
   `a^b = b^{-1}ab = (a^{-1},1)ε(1,b)(1,a)ε = (a^{-1}b,1)ε(1,a)ε = (a^{-1}ba,1) = (b^a,1)`.
   Its first coordinate `b^a` is nontrivial (Lemma 3), while the first coordinate of `a = (1,b)`
   is trivial. So `a^b ≠ a`, i.e. `c ≠ 1`. By Theorem 5, `c` has infinite order. Taking `⟨c⟩` in
   each factor of `P_k` gives `ℤ^{2^k} ≤ B`.
7. `cd ℤ^n = n`, and cohomological dimension does not increase on passing to subgroups, so
   `cd B = ∞`. ∎

## 5. The substitution endomorphism

**Proposition 7.** Define `σ : B → Aut(T)` by `σ(g) = (a^{ε_a(g)}, g)`. Then:

1. `σ` is an injective homomorphism with `σ(a) = b^2` and `σ(b) = a`. So `σ(B) = ⟨a, b^2⟩ ≤ B`,
   and `σ` is the endomorphism induced by the substitution `b ↦ a, a ↦ b^2` of Bartholdi–Virág,
   Lemma 11.
2. `[B : σ(B)] = ∞`.

*Proof.*

1. `ε_a` is a homomorphism (Lemma 4), and `(x,g)(y,h) = (xy, gh)`, so `σ` is a homomorphism. It
   is injective because the second coordinate of `σ(g)` is `g`. Also `σ(a) = (a,a) = b^2` and
   `σ(b) = (1,b) = a`. So the image is the subgroup generated by `b^2` and `a`.
2. Let `u = a^b = (b^a, 1) ∈ B`. If `u^k σ(B) = u^l σ(B)`, then `u^{k−l} = ((b^a)^{k−l}, 1)`
   lies in `σ(B)`. An element `σ(g)` with trivial second coordinate has `g = 1`, so it is
   trivial. Hence `(b^a)^{k−l} = 1`, and `k = l` by Lemma 3. So the cosets `u^kσ(B)` are pairwise
   distinct. ∎

## 6. Consequences for the ascending HNN extension

Let `B~ = ⟨B, t | t^{-1} g t = σ(g), g ∈ B⟩` be the HNN extension along the injective
endomorphism `σ`. `B` embeds in `B~` (Higman–Neumann–Neumann).

**Corollary 8.**

1. Every element of `B~` equals `t^p g t^{-q}` for some `p, q ≥ 0` and `g ∈ B`.
2. `B~` is torsion-free.
3. `B~` contains `ℤ^n` for every `n`, so `cd B~ = ∞`.
4. The Bass–Serre tree of `B~` has infinite valence, and its vertex stabilizers are the conjugates
   of `B`.

*Proof.*

1. The relations give `gt = tσ(g)` and `t^{-1}g = σ(g)t^{-1}`. The set of elements
   `t^p g t^{-q}` contains `1`, and it is closed under right multiplication by `h ∈ B`, by `t`
   and by `t^{-1}`:
   - `t^p g t^{-q}h = t^p gσ^q(h) t^{-q}`;
   - `t^p g t^{-q} t = t^p g t^{-(q−1)}` if `q ≥ 1`, and `t^p g t = t^{p+1}σ(g)` if `q = 0`;
   - `t^p g t^{-q} t^{-1} = t^p g t^{-(q+1)}`.

   So it is all of `B~`.
2. The homomorphism `χ : B~ → ℤ` with `χ(t) = 1` and `χ(B) = 0` is well defined, since each
   relator has `χ = 0`. A torsion element `x = t^p g t^{-q}` has `χ(x) = p − q = 0`, so it is
   conjugate to `g ∈ B`. Then `g` has finite order, so `g = 1` by Theorem 5.
3. This follows from Proposition 6.
4. The valence of a vertex is `[B:B] + [B:σ(B)] = ∞` by Proposition 7. ∎

## 7. Machine sanity checks

`experiments/basilica-hnn-2026-09-16/basilica_checks.py` implements the recursion with the
section-word rule of Lemma 1 and the standard word-problem recursion for contracting groups. Its
output is in `basilica_checks.out`; all checks pass. It checks:

- the identities `b^2 = (a,a)`, `a^b = (b^a,1)` and `[a,b^2] = (1,[b,a])`;
- `σ(g) = (a^{ε_a(g)}, g)` on 300 random words;
- the realisation of `1 × B'` and `B' × 1`;
- the relators `σ^n([a,a^b])` for `n ≤ 5`, and `[[b,a],a] = 1`, which is the reading of
  Bartholdi–Virág's relator under the conventions above;
- the shape statement of Lemma 2 for all reduced words of length `≤ 8`;
- a bounded torsion scan: no nontrivial word of length `≤ 7` has `g^k = 1` for `2 ≤ k ≤ 6`.

These checks are consistency evidence for the conventions, not part of the proof.
