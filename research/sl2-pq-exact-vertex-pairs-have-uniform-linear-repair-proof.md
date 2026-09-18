---
rg: 2
id: sl2-pq-exact-vertex-pairs-have-uniform-linear-repair-proof
kind: route
title: "Congruence extension, one Kazhdan projection, the depth-drift bound to strip the q-adic part, and a second projection over the prime-to-pq completion"
target: sl2-pq-exact-vertex-pairs-have-uniform-linear-repair
requires:
  - iwahori-depth-drift-bounds-smooth-vertex-mismatch
  - sl2-s-arithmetic-pair-is-codense-kazhdan
---

Notation is as in the target. Put:
- `K_0 = SL_2(Z_q)`, `K_1 = g K_0 g^(-1)` and `I = K_0 ∩ K_1`;
- `P' = ∏_(ℓ ∤ pq) SL_2(Z_ℓ)`;
- `||·||_2 = ||·||_F/√N`, where `N = dim W`.

## Step 0: the amalgam and the closures

**The amalgam `(VR0)`.**
- `A` is dense in `SL_2(Q_q)`. Its upper and lower unipotent subgroups have
  entries in `Z[1/pq] ⊃ Z[1/q]`, which is dense in `Q_q`, and these two
  subgroups generate `SL_2(Q_q)`.
- `SL_2(Q_q)` acts on its tree without inversion, with an edge `[v_0, v_1]` as
  fundamental domain. Density transfers this to `A`, because vertex
  stabilizers are open.
- The stabilizers in `A` are `A ∩ K_0 = C`, `A ∩ K_1 = g(A ∩ K_0)g^(-1) = C'`
  (conjugation by `g^{±1}` preserves `A`) and `A ∩ I = D`.
- Serre, *Trees*, Ch. I §4.1, Theorem 6 now gives `A = C *_D C'`.

**The closures.** Strong approximation (already `SL_2(Z)` is dense in every
finite product of `SL_2(Z_ℓ)`) gives:
- `C` is dense in `K_0 × P'`;
- `C'` is dense in `K_1 × P'`, since `g` is a unit away from `q`;
- `D`, the preimage in `C` of the open subgroup `I × P'`, is dense in `I × P'`;
- `A` is dense in `P'`.

## Step 1: congruence extension

This is the argument of item 3 of `sl2-s-arithmetic-pair-is-codense-kazhdan`,
applied verbatim to `C = SL_2(O_S)` with `S = {∞, p}` and `|S| = 2`:
- `diag(p,1/p) u diag(p,1/p)^(-1) = u^(p^2)`, so `σ_0(u)` has finite order;
- Serre's congruence subgroup property for `SL_2(O_S)`, `|S| >= 2`, then applies.

So `σ_0` factors through a congruence quotient `SL_2(Z/M)` with `p ∤ M`, and
it extends continuously to `K_0 × P'`. In the same way, `σ_1` extends to
`K_1 × P'`. The two extensions restrict on `I × P'` to the continuous
extensions of `σ_0|_D` and `σ_1|_D`.

## Step 2: a Kazhdan pair for D

`C` has (T;FD) by item 1 of `sl2-s-arithmetic-pair-is-codense-kazhdan`. Let
`(F_C, κ_C)` be a Kazhdan pair for the finite-dimensional unitary
representations of `C` that have no invariant vectors. Such a pair exists
because isolation of the trivial representation from a class closed under
direct sums is witnessed by one finite set.

Now let `ω` be a finite-dimensional representation of `D` with no invariant
vectors, and `v` a vector.
- Choose coset representatives `t_1, ..., t_r` for `C/D`.
- `ξ(t_i h) = ω(h)^(-1) v` defines `ξ ∈ Ind_D^C ω`.
- `Ind_D^C ω` has no `C`-invariants, by Frobenius reciprocity.
- For `s ∈ F_C`, write `s^(-1) t_i = t_j h_(s,i)`.
- Then `||λ(s)ξ - ξ|| <= max_(s,i) ||ω(h_(s,i))^(-1) v - v|| · √r`, while `||ξ|| = √r ||v||`.

So `F_D = {h_(s,i)}` and `κ = κ_C` form a Kazhdan pair for `D`. We take
`S_D ⊇ F_D`. For every finite-dimensional unitary representation `ω` of `D`,
with `P_ω` the projection onto invariants,

```text
||v - P_ω v|| <= κ^(-1) max_(s ∈ S_D) ||ω(s)v - v||.              (K)
```

## Step 3: the first projection

Let `D` act on `End(W)` with the normalized trace inner product by
`ω(h)X = σ_0(h) X σ_1(h)^(-1)`. Then `||ω(s)I - I||_2 = ||σ_0(s) - σ_1(s)||_2 <= δ`.

`(K)` gives an intertwiner `Y ∈ Hom_D(σ_1, σ_0)` with
`||Y - I||_2 <= η := δ/κ`. By density and continuity, `Y` intertwines the
extensions over `I × P'`.
- `ker Y` is `σ_1`-invariant.
- `Y` maps `(ker Y)^⊥` isomorphically and equivariantly onto `range Y`.
- `I - Y` is the identity on `ker Y`, so `dim ker Y/N <= ||I - Y||_2^2 <= η^2`.

So `σ_0|_(I×P')` and `σ_1|_(I×P')` have a common subrepresentation of
codimension at most `η^2 N`.

## Step 4: stripping the q-adic part

Apply `iwahori-depth-drift-bounds-smooth-vertex-mismatch` in its `K_i × P'`
form. It gives

```text
1 - θ_i <= η^2/c     (i = 0, 1),
```

where `θ_i` is the fraction of `W` fixed by `σ_i(K_i)`.

**The q-adically trivial replacements.**
- `W_0 = W^(σ_0(K_0))` is `K_0 × P'`-invariant, because the factors commute.
- Let `λ_0` be the representation of `P'` equal to `σ_0|_(P')` on `W_0` and
  trivial on `W_0^⊥`, and regard it as a representation of `K_0 × P'` trivial
  on `K_0`.
- The two representations differ only on `W_0^⊥`, so on every group element

  ```text
  ||λ_0 - σ_0||_2 <= 2 √(1-θ_0) <= 2η/√c.
  ```

- Define `λ_1` from `σ_1` in the same way; it obeys the same bound.

## Step 5: the second projection

On `S_D`, viewed in `P'` through `D → I × P' → P'`,

```text
||λ_0(s) - λ_1(s)||_2 <= δ + 4η/√c.
```

`(K)` gives `Y' ∈ Hom_D(λ_1, λ_0)` with
`||Y' - I||_2 <= η' := (δ + 4η/√c)/κ`. Since `D` has dense image in `P'`,
`Y'` intertwines `λ_1` and `λ_0` as representations of `P'`.

## Step 6: exact gluing

**The polar decomposition.**
- Write `Y' = U'|Y'|`. Here `|Y'|` commutes with `λ_1`.
- So the partial isometry `U' : (ker Y')^⊥ → range Y'` intertwines `λ_1` and `λ_0`.
- Complete it by any unitary `ker Y' → (range Y')^⊥` to a unitary `Ũ`.

**Bounding `Ũ - I`.** Von Neumann's inequality `|tr Y'| <= Σ s_i(Y')` gives
`|| |Y'| - I ||_F <= ||Y' - I||_F`. Hence:
- on `(ker Y')^⊥`, `||(Ũ - I)||_F <= || |Y'| - I ||_F + ||Y' - I||_F <= 2||Y' - I||_F`;
- on `ker Y'`, `||(Ũ - I)||_F^2 <= 4 dim ker Y' <= 4||Y' - I||_F^2`.

So `||Ũ - I||_2 <= √8 η' <= 3η'`.

**The glued representations.**
- Let `λ_0^♭` be `λ_0` on `range Y'` and trivial on its complement.
- Let `λ_1^♭` be `λ_1` on `(ker Y')^⊥` and trivial on `ker Y'`.
- Then `λ_0^♭ = Ũ λ_1^♭ Ũ^*` exactly.
- Each differs from its original on a subspace of dimension `<= η'^2 N`, so by at most `2η'`.

**The output.** Put `π = λ_0^♭ ∘ (A → P')`, an exact representation of `A`.
- On `s ∈ S_C`, `π(s) = λ_0^♭(s̄)` and `σ_0(s) = σ_0(ŝ)`, where `ŝ` is the image of `s` in `K_0 × P'`. So

  ```text
  ||π(s) - σ_0(s)||_2 <= 2η' + 2η/√c.
  ```

- On `s ∈ S_(C')`, `π(s) = Ũ λ_1^♭(s̄) Ũ^*` and `σ_1(s)` is within `2η/√c` of `λ_1(s̄)`. So

  ```text
  ||π(s) - σ_1(s)||_2 <= 2||Ũ - I||_2 + 2η' + 2η/√c <= 8η' + 2η/√c.
  ```

Substituting `η = δ/κ` and `η' = δ(1 + 4/(κ√c))/κ` gives `(VR1)`. ∎

**Where each input is used.**
- The congruence property (Step 1) is what makes the vertex representations
  smooth at `q`, so that the finite-group theorem applies.
- (T;FD) of `D` (Step 2) converts the HS edge defect into an honest common
  subrepresentation twice.
- Depth drift (Step 4) is the only q-adic input. Without it, a vertex pair
  could match on `I` while carrying a large q-nontrivial part that no
  representation of `A` can glue.
