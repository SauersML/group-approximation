# gq-referee-b: `bg-in-isometric-brick-hosts-needs-unbounded-exponents` (citation and scope lens)

Node as landed at cf3b0aad3 (lane bh-one-relator). The proof was passed by gq-referee-a (5d3e18e0b). Lens: are the
named hosts really groups of isometric-section brick maps, and can the entropy bound be pinned.

**Verdict: PASS.**
- The three families of hosts are groups of isometric-section brick maps, exactly as the node says.
- The Lipschitz entropy bound is not pinned at source. I reached only secondary pointers to Katok–Hasselblatt,
  Theorem 3.2.9, attributed there to Kushnirenko.
- The bound can be replaced by a four-line spanning-set argument that needs only Bowen's definition. It is given
  below, and I recommend putting it in the node (W1).
- Items 1 and 2 do not use the bound, as the node says.

## 1. The hosts are brick groups with isometric sections

**Isometries of `(C, d)`.** Put `d(x,y) = 2^(−m)`, where `m` is the common-prefix length. The isometries of `(C, d)` are
exactly the automorphisms of the binary rooted tree: they map each cone `C(w)` onto a cone of the same length. The
node's `𝔅_n` uses the product sup-metric, so a table with such sections is what the node calls isometric.

- **Brin's `nV`.** All sections are `id`. ✓
- **`2V_τ`** (`odometer-2v-is-fp-simple-and-contains-bs12`, Setting, "Concretely (proof, step B)").
  - The elements act on the rectangles of a finite partition as `(p_i x, w_i y) ↦ (p'_i τ^(n_i)(x), w'_i y)`.
  - `τ(0w) = 1w` and `τ(1w) = 0τ(w)` is a tree automorphism, hence so is every `τ^k`. So the sections are
    `(τ^(n_i), id)`, and the range rectangles `C(p'_i) × C(w'_i)` again partition `X`.
  - This is the node's example, "`h = τ^k` on coordinate 1, `id` on coordinate 2". ✓
  - `s = τ × id` has the table `C(0) × C → C(1) × C`, with section `id`, and `C(1) × C → C(0) × C`, with section `τ`.
    So `δ_s ≡ 0`, as the Consequences use. ✓
- **`2V_(G_N)`** (`affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`, Setting).
  - Colour 1 carries the digits of `Z_2` least-significant first, so the prefix metric on colour 1 is the 2-adic
    metric.
  - `G_N` acts by `x ↦ ax + b`, where `a` is a product of powers of the odd primes dividing `N` and `b ∈ Z[1/N] ⊆
    Z_2`. So `a ∈ Z_2^×`, and `|g(x) − g(y)|_2 = |x − y|_2`: every element is an isometry of `Z_2`, that is, a tree
    automorphism.
  - The sections of `x ↦ ax + b` at a digit are `x' ↦ ax' + b'`, with the same `a` and `b' ∈ Z[1/N]`. So the action
    is self-similar within `G_N`.
  - Each `g ∈ G_N` fixes colour-2 edges with restriction `g`, so on `X = C × C` it acts as `g × id`. Hence the
    bisections of `I_l(Λ ⋈ G_N) ⋉ X` act on rectangles as `(p x, w y) ↦ (p' g(x), w' y)`, and the elements of
    `2V_(G_N)` are isometric-section brick maps with sections `(g, id)`. ✓
- **`n = 1`, Röver–Nekrashevych groups `V_2(G)`.** The sections lie in `G ≤ Aut(T_2)`, which consists of isometries.
  ✓

## 2. The entropy bound

- **At source.** Not read. A search gave only secondary pointers. They attribute the bound
  `h(f) ≤ dim_B(X) · max(0, log Lip(f))` for Lipschitz `f` on compact metric spaces to Kushnirenko, via Katok–
  Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, Theorem 3.2.9.
  - Bobok–Roth (arXiv:1612.06095v2, Proposition 2.1, p. 2) state the one-dimensional case, `h(f) ≤ max{0, log λ}`
    on `[0, 1]`, citing their ref. [8].
  - I did not read Katok–Hasselblatt, and I have not verified the theorem number. It should be cited as "not read".
- **A self-contained replacement (recommended).** It uses only Bowen's spanning-set definition of topological
  entropy on a compact metric space.
  - Item 3's argument shows that `f ∈ 𝔅_n` is globally `λ`-Lipschitz, with `λ = 2^(L(f))`. So
    `d(x, y) ≤ ε λ^(−(k−1))` implies `d(f^i x, f^i y) ≤ ε` for `0 ≤ i < k`.
  - A closed `d`-ball of radius `2^(−m)` in `C^n` is a depth-`m` brick, and there are `2^(nm)` of them. Take
    `m = ⌈log_2(1/ε)⌉ + (k−1)L(f)`. The centres of the depth-`m` bricks then form a `(k, ε)`-spanning set, so
    `r(k, ε) ≤ 2^(n(⌈log_2(1/ε)⌉ + (k−1)L(f)))`.
  - Hence `limsup_k (1/k) log r(k, ε) ≤ n L(f) log 2` for every `ε`, and `h(f) ≤ n L(f) log 2`. This is item 3's
    inequality, and it needs no box-dimension theorem.
- **The other entropy facts in item 3** are also standard: `h(f^k) = k h(f)`, and entropy is invariant under
  topological conjugacy. They are needed for `h(g) = h(g^2) = 2h(g)` and for `h(φ(b)) = h(g)`. Cite a textbook, for
  example Walters, *An Introduction to Ergodic Theory*, Ch. 7. I did not re-read it.

## 3. Scope

- The Consequences exclude only `BS(1,2)` copies whose base element has bounded exponent sums, or whose conjugator has
  positive entropy. The landed `⟨s, u⟩ ≤ 2V_τ` is of the first kind, since `δ_s ≡ 0`.
  - It is also of the second kind: `u` is the inverse baker map, whose entropy is `log 2`, since it is conjugate to
    the full two-sided 2-shift. The node cites this through `brin-thompson-proper-power-conjugates-have-zero-entropy`,
    item 4.
  - The statement claims no more than this. ✓
- "Sharpness" is right: `u s u^(−1) = s^2` inside `2V_τ` has bounded sums for `s`. So item 2 genuinely needs the stable
  letter. ✓
- The title's claim is "never extend to BG", meaning `⟨s, u⟩` is not the `⟨a, b⟩` of any image of `BG`. That is what
  the Consequences prove. ✓

## Warnings

- **W1.** Replace "The textbook bound `h(f) ≤ dim_B · max(0, log Lip(f))`", which is not read, with the spanning-set
  argument of §2. Alternatively, cite it as "Katok–Hasselblatt, Thm 3.2.9 (Kushnirenko), not read".
- **W2.** The status line says "Citation review by gq-referee-b pending". It can now point to this report.
