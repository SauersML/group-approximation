---
rg: 2
id: fully-self-replicating-fp-infinity-groups-are-acyclic-proof
kind: route
title: The Lyndon-Hochschild-Serre sequence of R^X semidirect P collapses away from |P|, Kunneth turns the fibre into a signed permutation module, and orbits of the all-e tensor on X minus a point survive exactly when P is even
target: fully-self-replicating-fp-infinity-groups-are-acyclic
requires:
  - fully-self-replicating-tree-groups-give-fg-tits-hosts
artifacts:
  - experiments/self-replicating-homology-2026-09-17/verify_wreath_coinvariants.py
  - experiments/self-replicating-homology-2026-09-17/verify_wreath_coinvariants.out
---

The notation is that of the target. Fix a total order on `X`. `H = H_*(R; k)`,
`H_+ = H_{>0}(R; k)`, and `|u|` is the degree of a homogeneous class `u`.

## 0. Fully self-replicating groups are examples

Let `R ≤ Aut(X*)` satisfy (S), (B) and (A) with root image `P`. The section map
`ψ : R → R ≀_X P`, `s ↦ ((s|_x)_x, π_s)`, is an injective homomorphism. It is onto by
(R1) of `fully-self-replicating-tree-groups-give-fg-tits-hosts-proof`. That argument
uses only that the root permutation of the element to be matched lies in the root image,
so it holds verbatim with `P` in place of `A_d`. So `R ≅ R^X ⋊ P`.

## 1. The coinvariant identity

- **Collapse.** Apply the Lyndon--Hochschild--Serre spectral sequence to
  `1 → R^X → R^X ⋊ P → P → 1` with coefficients `k`:
  `E^2_{pq} = H_p(P; H_q(R^X; k)) ⇒ H_{p+q}(R^X ⋊ P; k)`.
  Since `|P|` is invertible in `k`, `H_p(P; M) = 0` for every `kP`-module `M` and every
  `p > 0`. Multiplication by `|P|` on `H_p(P; M)` factors through `H_p(1; M) = 0`, by
  restriction and transfer. So `H_n(R^X ⋊ P; k) ≅ H_n(R^X; k)_P`, the coinvariants for
  the action induced by conjugation, which is the permutation of coordinates.
- **Künneth.** Over a field, the cross product
  `H_*(G; k) ⊗ H_*(G'; k) → H_*(G × G'; k)` is an isomorphism for all groups `G`, `G'`,
  by Eilenberg--Zilber and the Künneth theorem over a field. No finiteness is needed.
  Iterating in the order of `X` gives `H_*(R^X; k) ≅ H^{⊗X}`.
- **The action.** The swap `G × G' → G' × G` sends `u × v` to `(−1)^{|u||v|} v × u`
  (Brown, *Cohomology of groups*, V.3). So `g ∈ P` acts on `H^{⊗X}` by permuting the
  tensor factors with the Koszul sign.
- With `ψ` this gives `H ≅ (H^{⊗X})_P` as graded vector spaces.

## 2. Counting the coinvariants

- **Basis.** Let `B_+` be a homogeneous basis of `H_+` and `B = {1} ⊔ B_+`. The tensors
  `e_β = ⊗_{x ∈ X} β(x)`, for functions `β : X → B`, form a basis of `H^{⊗X}`. For
  `g ∈ P`, `g e_β = ε(g, β) e_{gβ}`, where `(gβ)(x) = β(g^{−1}x)` and `ε(g, β) = ±1` is
  the sign of the permutation that `g` induces on the positions of the odd-degree
  factors of `e_β`. `deg e_β = Σ_x |β(x)|`, and `supp β = {x : β(x) ≠ 1}`.
- **Orbits.** `H^{⊗X}` is the direct sum of the spans `V_O` of the `P`-orbits `O` of
  basis tensors, and each `V_O` is a submodule. Pick `β ∈ O` with stabilizer `P_β`.
  The cocycle identity `ε(gh, β) = ε(g, hβ) ε(h, β)` makes `χ_β = ε(·, β)|_{P_β}` a
  character `P_β → {±1}`. Every vector of `V_O` is congruent modulo
  `span{gv − v}` to a multiple of `e_β`. The relation `h e_β − e_β` with `h ∈ P_β` is
  `(χ_β(h) − 1) e_β`.
  - If `χ_β` is trivial, the functional `e_{gβ} ↦ ε(g, β)` is well defined and
    `P`-invariant, and it is nonzero on `e_β`. So `(V_O)_P = k`.
  - If `χ_β(h) = −1`, then `2e_β = 0` in the coinvariants. The characteristic of `k` is
    not `2`, since `2` then divides `|P|`, so `(V_O)_P = 0`.
- **Supports of size `0` and `1`.** Support `∅` gives one orbit, `k` in degree `0`. For
  support `{x}` and value `e ∈ B_+`, the stabilizer is the point stabilizer `P_x`. It
  moves only unit factors, which have degree `0`, so `χ = 1`. `P` is transitive, so these
  orbits are in bijection with `B_+`, degree by degree. They contribute a copy of `H_+`.
- **Excess.** Let `E_*` be the sum of the `(V_O)_P` over orbits with `|supp| ≥ 2`. Then
  `H_n ≅ H_n ⊕ E_n` for `n ≥ 1`, as abstract vector spaces. So `h_n = h_n + dim E_n` as
  cardinals, and `E_n = 0` whenever `h_n` is finite. This is item 1.

## 3. Excess classes (item 2)

In each case exhibit `β` with `|supp β| ≥ 2` and `χ_β = 1`.

- **(i)** Let `e ≠ e'` in `B_+`, of degrees `a` and `b`. Pick `x ≠ y`, using `d ≥ 2`, and
  put `β(x) = e`, `β(y) = e'`, and `β = 1` elsewhere. An element of `P_β` must fix `x`
  and `y`, since the values differ, so it moves only unit factors and `χ_β = 1`. This
  gives a class in `E_{a+b}`.
- **(ii)** Let `e ∈ B_+` have even degree `a`, and put `β = e` on `{x, y}` and `1`
  elsewhere. No factor of `e_β` has odd degree, so `ε ≡ 1`. This gives a class in
  `E_{2a}`.
- **(iii)** Let `S` be as stated, `e ∈ B_+` of degree `a`, and `β = e` on `S`, `1` off `S`.
  Then `P_β = P_S`. For `g ∈ P_S`, the odd-degree factors of `e_β` are all `|S|` copies
  of `e` when `a` is odd, and there are none when `a` is even. So `ε(g, β) = sgn(g|_S)`
  for odd `a`, and `ε(g, β) = 1` for even `a`. In both cases `χ_β = 1` by hypothesis.
  This gives a class in `E_{|S| a}`.
  - If `P ≤ Alt(X)` and `d ≥ 3`, take `S = X ∖ {x}`. Its setwise stabilizer is `P_x`.
    An element of `P_x` is even on `X` and fixes `x`, so it is even on `S`, and
    `|S| = d − 1 ≥ 2`. (`S = X` also qualifies and gives `E_{da} ≠ 0`.)

## 4. Items 3 and 4

- **Item 3.** Let `P ≤ Alt(X)`, `d ≥ 3`, and `h_a ≠ 0`. By (iii), `E_{(d−1)a} ≠ 0`, so
  `h_{(d−1)a}` is infinite by item 1.
  - (a) Type `FP_m` over `k` gives `h_j < ∞` for `j ≤ m`. With `m = (d−1)a` and
    `j ≤ a`, we get `(d−1)j ≤ m`, so `h_{(d−1)j} < ∞` and hence `h_j = 0`.
  - (b) Apply (a) for every `a`.
  - (c) Type `FP_∞` over `Z` passes to every field, by tensoring a resolution of finite
    type. It also makes every `H_n(R; Z)` finitely generated. By the universal
    coefficient theorem, `H_n(R; Z) ⊗ k ↪ H_n(R; k) = 0` for `n ≥ 1`. With `k = Q` this
    makes `H_n(R; Z)` finite. With `k = F_p` and `p ∤ |P|` it has no `p`-torsion.
  - (d) Finite presentation gives type `FP_2` over `Z`, hence over `k`, so `h_2 < ∞`.
    - By (i) with `a = b = 1`, two distinct basis classes in degree `1` are impossible,
      so `h_1 ≤ 1`. This holds for every transitive `P`, and `H_1(R; Z) ⊗ Q = H_1(R; Q)`
      gives `rank ≤ 1`.
    - For `d = 3`, `(d − 1) · 1 = 2`, so (a) gives `h_1 = 0`.
    - Under `FP_{d−1}`, (a) with `a = 1` kills `H_1(R; Q)` and `H_1(R; F_p)` for
      `p ∤ |P|`. `R^{ab}` is finitely generated, so it is finite with no such `p`-torsion.
- **Item 4.** Let `R` be of type `FP_∞` over `k`, so every `h_n` is finite and every
  `E_n = 0`. Suppose `H_+ ≠ 0`, and let `a` be the least degree with `h_a ≠ 0`.
  - By (ii), `a` is odd.
  - By (i), there is only one basis class `e` in degree `a`, and no basis class in any
    other degree `b`, since that would put a class in `E_{a+b}`. So `H_+ = k e`.
  - `E_{2a} = 0` requires the orbit of `β = e` on `{x, y}` to die, that is some `g ∈ P`
    to swap `x` and `y`. This holds for every pair. `E_{|S|a} = 0` rules out every `S`
    as in (iii).
  - Conversely, for `P = Sym(X)` and `H_+ = k e` with `|e|` odd, every `β` with
    `|supp β| ≥ 2` has value `e` on its support `S`. `P_S` contains a transposition of
    `S`, which acts by `−1`. So `E = 0`, and item 1 imposes nothing. ∎

## 5. The script

`verify_wreath_coinvariants.py` computes `dim (H^{⊗X})_P` in each degree by Gaussian
elimination over `F_{10007}`, for small graded `H`. It uses `P = A_5, A_4, S_4, Z/3`.
It compares the result with the orbit count of §2 and prints the excess `E_n`. The
output agrees in every case. It shows the predicted first excess degrees:

- `A_5` with one class in degree `1`: excess in degrees `4 = d − 1` and `5 = d`, and none
  in degree `2`;
- `A_5` with one class in degree `2`: excess in degree `4`;
- `A_5` with two classes in degree `1`: excess in degree `2`;
- `A_4` with classes in degrees `1` and `2`: excess in degree `3`;
- `Z/3` with one class in degree `1`: excess in degree `2`;
- `S_4` with one odd class: no excess, up to degree `4|e|`.

## Scope

The argument uses only the abstract isomorphism `R ≅ R ≀_X P`. It never uses the tree,
finite-state or contraction properties, so it applies equally to non-contracting
candidates. It says nothing about characteristics dividing `|P|`. There the spectral
sequence does not collapse, and in particular `2`- and `3`-torsion in `H_1` of a
finitely presented candidate with root image `A_d` is not constrained.
