# Finite-stabilizer coset shifts inherit surjunctivity from the host

Lane w6-free-pos-d, 2026-09-12. Node: `finite-stabilizer-coset-shifts-inherit-surjunctivity` (OPEN).
Verifier: w4-vf-positive-b.

## 0. Setting and question

- `G` is a group, `H <= G` a finite subgroup, and `A` a finite alphabet with `|A| = m >= 2`.
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

## 2. The shared-prime case: what the averaging step cannot be replaced by

Throughout this section a prime `p` divides both `m` and `|H|`.

**Lemma 2 (no retraction commutes with constants).** Give `A` any group structure, written
multiplicatively. No automaton `Q : X -> X` with image inside `Y` satisfies `Q(z c) = Q(z) c` for every
configuration `z` and every constant configuration `c`.

*Proof.*
1. By Cauchy, `H` has an element `h` of order `p`, and `A` has an element `a` of order `p`.
2. Let `mu` be a rule of `Q` with memory `F`, so `Q(z)(k) = mu((z(kf))_(f in F))`. Put `F' = <h> F` and let
   `mu'` ignore the added coordinates. Then `hF' = F'`, and `f -> hf` permutes `F'` with every orbit of
   size `p`, since `hf = f` forces `h = 1`.
3. Output in `Y` means `Q(z)(kh) = Q(z)(k)`, that is,
   `mu'((z(khf))_(f in F')) = mu'((z(kf))_(f in F'))` for all `z` and `k`.
4. Fix `k`. Choose a transversal `R` of the `<h>`-orbits on `F'`. Put `z(k h^i r) = a^i` for `r in R` and
   `0 <= i < p`, and any value elsewhere. The sites `k h^i r` are distinct, and `h^p = 1 = a^p`, so `z` is
   well defined.
5. Then `z(khf) = z(kf) a` for every `f in F'`. So the window at `kh` is the window at `k` multiplied
   pointwise by the constant `a`.
6. Step 3 and equivariance under constants give `mu'(w) = mu'(w a) = mu'(w) a`, where `w` is the window at
   `k`. That forces `a = 1`, a contradiction. QED

**Corollary 3 (the splitting property fails).** Let `A` be abelian. No automaton `Q` with image in `Y`
satisfies `Q(y w) = y` for all `y in Y` and all `w` in `{z (Qz)^(-1) : z in X}`.

*Proof.* For any `z` and constant `c`, `(Qz) c` lies in `Y`, and `zc = ((Qz) c)(z (Qz)^(-1))` pointwise.
So `Q(zc) = (Qz) c`, which Lemma 2 forbids. QED

Steps 3 to 6 of Theorem 1 use only three properties of `P`: its image is `Y`, it fixes `Y`, and it has this
splitting property. Those are what make `Phi(z) = tau(Pz)(z (Pz)^(-1))` work for every `tau` at once. So at
a shared prime the proof of Theorem 1 cannot run with a `tau`-independent automaton `P` of this kind. That
does not exclude other extensions of `tau`. The nonabelian case of Corollary 3 is not claimed.

**Min retraction (heuristic).** For an ordered alphabet `{0 < 1 < ... < m-1}`, the automaton
`rho(z)(k) = min_(h in H) z(kh)` has image `Y` and fixes `Y`. But the block fibre over base symbol `b`
has `(m - b)^|H| - (m - b - 1)^|H|` points. That depends on `b`, so no blockwise bijection moves the fibre
coordinate from base `b` to base `tau(rho z)(k)`. This rules out blockwise gauges only. Rules that also read
neighbouring blocks are not excluded by this count; Lemma 2 excludes the constant-equivariant ones.

**Amenable hosts (standard, not landed as a claim).**
- `Y` is a subshift of finite type: its forbidden patterns are two-cell patterns on `{k, kh}`.
- `Y` is strongly irreducible: patterns on `F_1` and `F_2` with `F_1 H ∩ F_2 H` empty glue.
- `tau(Y)` is a closed invariant subshift conjugate to `Y`, so it has the same topological entropy.
- Over an amenable group a strongly irreducible subshift has no proper subshift of full entropy
  (Ceccherini-Silberstein–Coornaert, strongly irreducible Garden of Eden theory; citation not re-read).

So `tau(Y) = Y` at every `m`, and the claim holds for amenable `G` with no coprimality. On a nonamenable
host nothing like this is available. The shared-prime case is where a finite-stabilizer coset shift might
carry strictness its host does not.

## 3. Reduction to subgroups of index coprime to m

For `S <= G` write `Y_S` for the right-`S`-invariant configurations in `A^G`. It is a copy of `A^(G/S)`.
When `S <= H`, `Y_H ⊆ Y_S`.

**Theorem 4.** Let `S <= H <= G`, with `H` finite and `[H : S]` coprime to `m`, and identify `A` with `Z/m`.
Let `tau : Y_H -> Y_H` be continuous, equivariant and injective. Then there is a continuous, equivariant,
injective `Phi : Y_S -> Y_S` with:
- `Phi(Y_S) ∩ Y_H = tau(Y_H)`;
- `Phi` onto iff `tau` onto.

*Proof.* Let `c` be the inverse of `[H : S]` mod `m`, and for `z in Y_S` put
`P(z)(k) = c sum_(hS in H/S) z(kh)`.
1. *Well defined.* Replacing the representative `h` by `hs`, `s in S`, does not change `z(kh)`, because `z`
   is right-`S`-invariant.
2. *Output in `Y_H`.* `P(z)(kh') = c sum_(hS) z(kh'h)`, and `hS -> h'hS` permutes `H/S`.
3. *Fixes `Y_H`.* For `z in Y_H` the sum is `[H : S] z(k)`, so `P(z) = z`.
4. `P` is linear, continuous and equivariant, so `Y_S = Y_H ⊕ (ker P ∩ Y_S)`.
5. Put `Phi(z) = tau(Pz) + (z - Pz)`. Every term lies in `Y_S`, so `Phi` maps `Y_S` to itself. Steps 3 to 6
   of Theorem 1 run verbatim inside `Y_S`. QED

For `S = 1` this is Theorem 1.

**Corollary 5 (minimal stabilizers).** Suppose the node's claim holds at `(G, S, m)`: every injective
continuous equivariant self-map of `Y_S` at size `m` is onto. Then it holds at `(G, H, m)` for every finite
`H >= S` with `[H : S]` coprime to `m`. Hence:
- **Prime-power alphabets.** For `m = p^k`, it suffices to treat finite `p`-subgroups of `G`. Take `S` a Sylow
  `p`-subgroup of `H`.
- **General `m`.** It suffices to treat finite subgroups `H` with no proper subgroup of index coprime to `m`.
  - For `m = p^k` these are exactly the `p`-groups. A Sylow `p`-subgroup has index coprime to `p`, and
    proper subgroups of a `p`-group have index a positive power of `p`.
  - For `m` with two prime factors both dividing `|H|`, no reduction may be available: over `m = 6`,
    `H = S_3` has no proper subgroup of index coprime to `6`.

So over prime-power alphabets, the open part of the node concerns only coset shifts `A^(G/S)` whose
stabilizer `S` is a nontrivial finite `p`-subgroup of the host, at alphabet size `p^k`.

**Remark (one step inside a `p`-group).** Let `H` be a `p`-group, `N` a normal subgroup of index `p`, and
`h in H \ N`.
- Right translation `R_h z(k) = z(kh)` preserves `Y_N`: `z(knh) = z(kh (h^(-1) n h)) = z(kh)` because `N` is
  normal in `H`.
- `R_h` commutes with the left shift and has order `p` on `Y_N`.
- `Y_H = Fix(R_h) ∩ Y_N`, because `H = <N, h>`.

So the minimal step asks the following. Let `theta` be a shift-commuting automorphism of order `p` of the coset
shift `Y_N`, and let `tau` be an injective self-map of `Fix(theta)`. Is `tau` surjective whenever every
injective self-map of `Y_N` is? The order `p` of `theta` shares the prime with the alphabet. For `N = 1` this
is the full shift with the right translation by an element of order `p`. Lemma 2 is stated for the full shift
only; it is not claimed here for ambient `Y_N`.
