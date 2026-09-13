# Finite-stabilizer coset shifts inherit surjunctivity from the host

Lane w6-free-pos-d, 2026-09-12. Node: `finite-stabilizer-coset-shifts-inherit-surjunctivity` (OPEN).
Verifier: w4-vf-positive-b.

## 0. Setting and question

- `G` is a countable group, `H <= G` a finite subgroup, and `A` a finite alphabet with `|A| = m >= 2`.
- The coset shift is `A^(G/H)` with `(g.y)(pH) = y(g^-1 pH)`.
- `X = A^G` carries the left shift `(g.z)(k) = z(g^-1 k)`.
- `Y` is the set of right-`H`-invariant configurations: `z(kh) = z(k)` for all `k` and all `h in H`.
- `iota(y)(k) = y(kH)` is an equivariant homeomorphism `A^(G/H) -> Y`:
  `iota(g.y)(k) = y(g^-1 kH) = (g.iota(y))(k)`.

So a continuous equivariant self-map of `A^(G/H)` is the same thing as a continuous equivariant self-map
of the subshift `Y`.

**Question.** If every injective automaton on `A^G` is surjective, is every injective continuous equivariant
self-map of `Y` surjective?

**Context on main.**
- `site-pullbacks-strict-iff-stabilizer-self-compressed`: one-site pullbacks are strict exactly on
  stabilizers properly conjugated into themselves, so never here.
- `compressed-coset-shifts-carry-strict-equivariant-embeddings`: infinite self-compressed stabilizers do carry
  strict self-embeddings, so a positive proof must use freeness.
- `invariant-output-injective-automata-need-invisible-symmetry`: injective automata from `X` into `Y`.
  - The restriction of such an automaton to `Y` is a strict self-map of `Y`.
  - Its image is `tau(Y) ⊆ tau(X) ⊆ Y`.
  - `tau(Y) = Y` would force `tau(X) = tau(Y)` with `Y ≠ X`, contradicting injectivity.

## 1. The coprime transfer

**Theorem 1.** Suppose `gcd(m, |H|) = 1`, identify `A` with `Z/m`, and let `tau : Y -> Y` be continuous,
equivariant and injective. Then there is a cellular automaton `Phi` on `A^G` with:
- `Phi` injective;
- `Phi(X) ∩ Y = tau(Y)`;
- `Phi` surjective iff `tau` surjective.

Hence, if every injective automaton on `(Z/m)^G` is surjective, then `tau` is surjective.

**Proof.**
1. *Averaging.* Let `c` be the inverse of `|H|` mod `m`, and put `P(z)(k) = c sum_(h in H) z(kh)`.
   - `P` is a linear automaton with memory `H`.
   - `P(z)` lies in `Y`: `P(z)(kh') = c sum_h z(kh'h) = P(z)(k)`, because `h -> h'h` permutes `H`.
   - `P(y) = c |H| y = y` for `y in Y`.

   So `P` is idempotent with image `Y`. `W = ker P` is a closed invariant subgroup, and `X = Y ⊕ W`.
2. *Extension.* Put `Phi(z) = tau(Pz) + (z - Pz)`, pointwise in `Z/m`. It is continuous and equivariant,
   hence an automaton (Curtis–Hedlund–Lyndon).
3. *Pieces.* `tau(Pz) in Y` and `z - Pz in W`, so `P(Phi z) = tau(Pz)` and `Phi z - P(Phi z) = z - Pz`.
4. *Injective.* If `Phi z = Phi z'`, step 3 gives `tau(Pz) = tau(Pz')` and `z - Pz = z' - Pz'`. Injectivity
   of `tau` gives `Pz = Pz'`, so `z = z'`.
5. *Image in `Y`.* `Phi z in Y` iff `z - Pz = 0` iff `z in Y`, and then `Phi z = tau(z)`. So
   `Phi(X) ∩ Y = tau(Y)`, and a configuration of `Y` missed by `tau` is missed by `Phi`.
6. *Onto when `tau` is.* Given `t in X`, choose `u in Y` with `tau(u) = Pt` and put `z = u + (t - Pt)`.
   Then `Pz = u` and `z - Pz = t - Pt`, so `Phi z = Pt + t - Pt = t`. QED.

**Remarks.**
- *Labels.* Any bijection `A ≅ Z/m` works. Relabelling symbols conjugates automata on `X` and self-maps
  of `Y` alike.
- *Memory.* Suppose `tau`, lifted to `X`, reads `F ⊆ G`: `tau(y)(k) = mu((y(kf))_(f in F))`. Then `Phi`
  has memory `FH ∪ H`.
- *Linear maps.* If `tau` is `Z/m`-linear, so is `Phi`. That gives the linear coprime transfer directly.
- *Several orbits.* Let `S` be a `G`-set with finitely many orbits `G/H_1, ..., G/H_r`, each `H_i` finite,
  and `m` coprime to every `|H_i|`. Then `A^S = Y_1 × ... × Y_r` sits in `(A^r)^G = X^r`, and
  `Phi = tau(Pz) + (z - Pz)` with `P = P_1 × ... × P_r` works the same way. It needs surjunctivity of `G` at
  alphabet size `m^r`.
- *No per-`H` converse is claimed.* A strict automaton on `A^G` does not obviously give a strict self-map of
  `A^(G/H)` for a fixed `H ≠ 1`. There is no injective equivariant map `A^G -> B^(G/H)` in general: over
  `Z/2 × Z` with `H = Z/2`, `H` acts trivially on the codomain and not on the domain. The equivalence in the
  node is over all finite `H`, including `H = 1`.
