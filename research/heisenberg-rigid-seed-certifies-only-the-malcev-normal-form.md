---
rg: 2
id: heisenberg-rigid-seed-certifies-only-the-malcev-normal-form
kind: claim
title: The rigid seed of H_3(Z) is the sign pattern of its Mal'cev coordinates; its forcing radius is linear, its forcing length is quadratic (the distortion of the center), and it certifies no complexity beyond the normal form; more generally, seeds built from locally finite splittings certify only Britton normal forms
requires:
  - locally-finite-splittings-preserve-rigid-sft-compactifications
distinct_from:
  locally-finite-splittings-preserve-rigid-sft-compactifications: that proves H_3(Z) ∈ 𝒞 abstractly; this writes the seed out, computes what it forces and how fast, and measures the word-problem complexity it certifies (rung 1b of the v6 CAP gate).
---

**ESTABLISHED** (lane proof, bh-emitter-a, 2026-09-18; elementary; not reviewed). This is
rung 1b of gate 1 (CAP) in SYNTHESIS v6. Terms are from the parent:
- seed SFT: conditions (C1) and (C2);
- rigidity: condition (R);
- `𝒞` is the class of groups with a rigid seed.

## 1. The explicit seed

**The group.** `H = H_3(Z) = ⟨x, y | [x, z], [y, z]⟩` with `z = [x, y] = xyx^{-1}y^{-1}`.
- Then `y x y^{-1} = x z^{-1}` and `y z y^{-1} = z`.
- `A = ⟨x, z⟩ ≅ Z^2` is normal, and every element has the unique normal form `g = x^a z^c y^b`.
- The *level* `λ(g) = b` is a homomorphism `H → Z`, and the cosets of `A` are the level sets. This is the
  mapping-torus splitting of the parent: one vertex group `A`, one loop edge with edge group `A`, and the
  Bass–Serre tree is the line of levels.

**`C_Z`.** Alphabet `{+, *, −}`. The allowed transitions `s(n) → s(n+1)` are `++`, `+*`, `*−` and `−−`.
- The seed `*` forces the point `…++*−−…`.
- Write `σ(n) = +` for `n < 0`, `*` for `n = 0`, and `−` for `n > 0`.

**The SFT `Y_H`.**
- **Alphabet.** `↑`, `↓` (pointers along `y` and along `y^{-1}`), and the sink letters `{+, *, −}²`.
- **(T) Transport,** for `s ∈ {x, z}`. A pointer at `h` equals the label at `hs`. The label at `h` is a sink letter
  iff the label at `hs` is.
- **(X) Exclusivity.** The label at `h` is `↑` iff the label at `hy` is not `↓`.
- **(Y) Sink.** On sink letters `(p, q)`:
  - `p` follows `C_Z` along `x` and is constant along `z`;
  - `q` follows `C_Z` along `z` and is constant along `x`.

  So on each sink coset `hA`, read through `g ↦ hg`, the labels form a point of `C_Z ⊠ C_Z`.
- **The seed.** The single letter `(*, *)` at `1`.

**The forced point.**

    y_*(x^a z^c y^b) = ↓ if b > 0,   ↑ if b < 0,   (σ(a), σ(c)) if b = 0.

*Check.*
- (T): `x` and `z` preserve levels, and on level 0 they move `(a, c)` by unit vectors.
- (X): `λ(hy) = λ(h) + 1`, and `λ(h) < 0` iff `λ(h) + 1 ≤ 0`.
- (Y): along `x` and `z` on level 0, the coordinates run through `C_Z`.
- (C1):
  - the seed makes level 0 the sink;
  - the unique sink forces every pointer toward it (parent, §2);
  - `C_Z ⊠ C_Z` with `(*, *)` at the origin forces `σ` on both coordinates.
  - `(*, *)` occurs only at `1`, so the stabilizer is trivial.
- (C2) and (R) are the parent theorem. `C_Z ⊠ C_Z` is a rigid seed on `A`, since `𝒞` is closed under
  products (`quantum-rigidity-is-product-stable`).

**The shear is harmless.** Rung 1b worried that the product seed on `Z²` is not shear-invariant: `y` moves the
central coordinate by `a`. That does not matter, because sink letters live on one coset only. Every other level
carries a pointer, and (T) makes pointers blind to `A`-coordinates.

## 2. What the seed forces, and how fast

Use the word metric in `{x, y}`. Recall `|z^c| ≍ √|c|`, so `g = x^a z^c y^b ∈ B_n` gives `|a|, |b| ≤ n` and
`|c| = O(n²)`.

**Forcing radius `m(n) ≤ 2n + O(1)`.** Every label of `y_*` on `B_n` is forced by rules whose sites stay in
`B_{2n+O(1)}`.
- **Pointers.** For `b > 0`, (X) applied down the chain `g y^{-j}`, `j = 1, …, b`, forces `↓`. The chain ends at
  `x^a z^c` on level 0. That site is a sink letter by (T), through `x^i` (`|i| ≤ |a|`) and then `x^a z^j`
  (`|j| ≤ |c|`). All these sites have length at most `|a| + |z^j| + b ≤ 2n + O(1)`. The case `b < 0` is symmetric.
- **Sink letters.**
  - `p` at `x^a z^c`: run `C_Z` along `x^i` from `1`, then constancy along `x^a z^j`.
  - `q`: run `C_Z` along `z^j`, then constancy along `x^i z^c`.
  - The same bound holds for these sites.

So in the notation of the synthesis remark (D′), `m(n) = Θ(n)`.

**Forcing length is quadratic.** The deduction above applies one rule per step. Forcing `q = −` at `z^c` runs
`C_Z` through the `|c|` sites `z, z², …, z^c`.
- For `g = z^c ∈ B_n` with `|c| ≍ n²`, the chain has `Θ(n²)` steps.
- This is the distortion of the central subgroup `⟨z⟩` (a lane observation: no other rule carries `q`, since
  pointers carry no coordinates and `x`-moves preserve `q`).
- So forcing length measures the distortion of the sink coordinates, while the forcing radius stays linear.

**Certified complexity.** Consider `(C1)` with a one-site seed.
- `g = 1` iff `y_*(g) = (*, *)`. So `WP(H)` reduces to evaluating `y_*` at a word.
- Evaluating `y_*(w)` along `w` needs the counters `b`, `a` and `c` of the prefixes. Each generator updates them
  (right multiplication by `x^{±1}` changes `c` by `∓b`), and `c` has `O(log n)` bits.
- So the seed certifies `WP(H) ∈ DLOGSPACE`, in linear time on a counter machine: exactly the Mal'cev normal
  form, and nothing more.
- The language of `Y_H` is decided the same way. A finite pattern occurs iff finitely many sign conditions on
  the coordinates of one translate hold. On the sink level these conditions are linear, so this is
  Presburger-decidable.

## 3. General: seeds from locally finite splittings certify only Britton normal forms

Let `Y` be the seed of the parent theorem for `Λ = π_1(𝔾)`, with sink type `a` and `(Y_A, y_{A*})`.
- **Proposition.** For `g ∈ Λ`, the forced point `y_*` at `g` has one coordinate per vertex type `u`:
  - if `gV_u` is the sink vertex `A` (so `u = a` and `g ∈ A`), the coordinate is `y_{A*}(g)`;
  - otherwise it is the first edge of the Bass–Serre geodesic from `gV_u` to `A`.
- **Proof.** This is §2 (C1) of `locally-finite-splittings-rigid-compactification-proof`: the seed forces the
  sink `A` with `y_{A*}` on it, and every vertex then points along its geodesic toward it.
- **Consequence.** Evaluating `y_*` on a word reduces to two computations:
  - the Britton normal form of the word in `𝔾`. This uses the word problems of the vertex groups and finite coset
    tables for the finite-index edge groups;
  - evaluating `y_{A*}` on words of `A`.
- `WP(Λ)` reduces to evaluating `y_*` (one-site seed as above; a ball seed is checked on a ball). So such a seed
  certifies at most "Britton normal forms plus the sink's own certificate". The seed layer adds no complexity.

**Hence rung 1b does not test CAP.** Neither does anything the parent reaches:
- BS(m,n) and GBS groups;
- mapping tori and polycyclic groups;
- finite-index overgroups.

In each case the vertex groups are commensurable with the sink (edge groups have finite index), so the
certified complexity is `WP(A)` plus Britton reduction with finite coset tables. A ¬CAP witness from this
construction would need that reduction itself to be hard over a tame sink, and no known locally finite
splitting does that (GBS groups and polycyclic groups have polynomial-time word problems).

## Lesson for general BH

In a rigid seed, complexity can enter only through distortion: forcing has to travel along the sink's own
generators.
- **H₃.** The forcing radius is linear, but forcing length is quadratic, the distortion of `⟨z⟩`. Evaluation needs
  exactly the Mal'cev counters.
- **Locally finite splittings.** Their seeds are pointers plus one sink, so they certify only Britton normal forms
  over the sink. The seed layer itself never adds complexity.
- **Where a CAP test must live.** A real test (rung 1c) needs relative seeds over infinite-index associated
  subgroups whose distortion encodes a computation. The right quantity to bound is forcing length, not forcing
  radius.
