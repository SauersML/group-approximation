---
rg: 2
id: bmw-40-40-281-irreducible-mobius-proof
kind: route
title: Conjugate the invariant-subtree automaton of 40_40#281 into semilinear Möbius maps over F_3((s)) by an explicit contracting coordinate system; the image contains an element of infinite order
target: bmw-40-40-281-is-irreducible
requires: []
artifacts:
  - experiments/bmw-281-linear-model-2026-09-17/README.md
  - experiments/bmw-281-linear-model-2026-09-17/aut.py
  - experiments/bmw-281-linear-model-2026-09-17/checkaut.py
  - experiments/bmw-281-linear-model-2026-09-17/checkaut.log
  - experiments/bmw-281-linear-model-2026-09-17/mobius281.py
  - experiments/bmw-281-linear-model-2026-09-17/mobius281.log
  - experiments/bmw-281-linear-model-2026-09-17/ser.py
  - experiments/bmw-281-linear-model-2026-09-17/rho2.py
  - experiments/bmw-281-linear-model-2026-09-17/rho2.log
  - experiments/bmw-281-linear-model-2026-09-17/rho3.py
  - experiments/bmw-281-linear-model-2026-09-17/rho3.log
---

The proof is by hand. §2 is a finite list of identities between rational functions, and
`mobius281.py` checks them exactly (sympy, coefficients mod 3). The coordinates were found by the
search `rho2.py`, which is not part of the proof.

## 0. Setting and reduction

`Γ` is the BMW group of degree (4,4) in class `40_40#281` of
`experiments/bmw-census-left-orders-2026-09-17/census_40_40.json`. `H_x ≤ Aut(T_V)` is the image of
the vertex stabilizer. As recorded in `bmw-44-sat-survivor-parity-kernels-not-left-orderable` and in
the header of `selfrep.py`:
- a vertical letter `f` is fixed by every element of `H_x` at every vertex;
- the reduced words `l_0 f l_1 f …` (`l_j ≠ f`) form an `H_x`-invariant subtree;
- `H_x` acts on that subtree through the automaton group `K` on the ternary tree `X^*`;
- `K` is a quotient of `H_x`, so if `K` is infinite then `H_x` is infinite, `pr_V(Γ)` is not
  discrete, and `Γ` is irreducible (Burger–Mozes, Prop. 1.2).

`checkaut.py` (`checkaut.log`) confirms that on both sides `selfrep.build` returns the automaton below,
with `f = 3` and `X = {0,1,2}`. Write `g(xw) = out_g(x) · g|_x(w)`. Then:

| state | `out` on `(0,1,2)` | sections at `(0,1,2)` |
|---|---|---|
| `a_0` | `(0,1,2)` | `(a_1,a_1,a_1)` |
| `a_1` | `(0,2,1)` | `(a_0,a_2,a_2)` |
| `a_2` | `(0,2,1)` | `(a_2,a_0,a_0)` |
| `τ`   | `(1,0,2)` | `(τ,τ,τ)` |

**Theorem.** `K` contains an element of infinite order, namely `τ a_2`. Hence `Γ` is irreducible.

## 1. Coordinates

Let `O = F_3[[s]]`, and let `σ` be the ring automorphism `s ↦ −s` of `F_3((s))`, applied
coefficientwise. Identify the letter `x ∈ X` with the digit `0, 1, −1` (`2 ≡ −1`). Put
`C(y) = (1 − y)/(1 + y)` and define:

    t_0(z) = s·σ(z),      t_1(z) = C(s·σ(z)),      t_2(z) = −C(s·z).

Then `t_x(z) = x + s·f_x(z)`, where:
- `f_0 = σ`;
- `f_1(z) = σ(z)/(1 + sσ(z))`, since `C(y) = 1 − 2y/(1+y) = 1 + y/(1+y)` in characteristic 3;
- `f_2(z) = −z/(1 + sz)`.

Each `f_x` is a composition of `σ` with a Möbius map `z ↦ (αz+β)/(γz+δ)` with `α, δ ∈ O^×`,
`β ∈ O` and `γ ∈ sO`. Such a map is an isometric bijection of `O`: the denominator is a unit, and the
map is invertible within the same class. `σ` is an isometric bijection too.

**Lemma 1.** For an infinite word `w = x_0 x_1 …`, put
`Φ(w) = lim_k t_{x_0} ∘ … ∘ t_{x_{k-1}}(0)`. Then:
- the limit exists;
- `Φ(xw) = t_x(Φ(w))`;
- `Φ(w) mod s^k` depends only on `x_0 … x_{k-1}`;
- this gives a bijection `X^k → O/s^k` for every `k`, compatible with reduction.

So `Φ` is an isomorphism of rooted trees from `X^*` onto the tree of residue balls of `O`.

*Proof.* Each `t_x` is `|s|`-Lipschitz, so the composites form a Cauchy sequence, uniformly in the
starting point. That gives existence, independence of the starting point, and `Φ(xw) = t_x(Φ(w))`.

For the residues, induct on `k`. The residue `Φ(xw) mod s^{k+1}` is `x + s·(f_x(Φ(w)) mod s^k)`.
Since `f_x` is an isometric bijection of `O`, it induces a bijection of `O/s^k`. So the residue is a
function of `x` and of `Φ(w) mod s^k`, and hence of the first `k+1` letters. Distinct prefixes of
length `k+1` give distinct residues. ∎

## 2. The intertwining identities

Define `A_{a_0} = σ`, `A_{a_1} = −σ`, `A_{a_2} = N` with `N(z) = −z`, and

    A_τ = T,   T(z) = (u − z)/(1 − s·u·z),   u = 1/(1 − s).

`T` has `α = −1`, `δ = 1` and `γ = −su ∈ sO`, so it is an isometric bijection of `O`. Its matrix
`(−1, u; −su, 1)` has trace 0, so `T^2 = 1`.

**Lemma 2.** For every state `g` and letter `x`,
`A_g ∘ t_x = t_{out_g(x)} ∘ A_{g|_x}` as maps `O → O`.

*Proof.* For the states `a_0, a_1, a_2` this uses only `σ^2 = 1`, `σ(s) = −s` and `σ∘C = C∘σ`.

| pair | left side | right side |
|---|---|---|
| `a_0, 0` | `σ(sσz) = −sz` | `t_0(−σz) = sσ(−σz) = −sz` |
| `a_0, 1` | `σC(sσz) = C(−sz)` | `t_1(−σz) = C(−sz)` |
| `a_0, 2` | `σ(−C(sz)) = −C(−sσz)` | `t_2(−σz) = −C(−sσz)` |
| `a_1, 0` | `−σ(sσz) = sz` | `t_0(σz) = sz` |
| `a_1, 1` | `−σC(sσz) = −C(−sz)` | `t_2(−z) = −C(−sz)` |
| `a_1, 2` | `−σ(−C(sz)) = C(−sσz)` | `t_1(−z) = C(−sσz)` |
| `a_2, 0` | `−sσz` | `t_0(−z) = −sσz` |
| `a_2, 1` | `−C(sσz)` | `t_2(σz) = −C(sσz)` |
| `a_2, 2` | `C(sz)` | `t_1(σz) = C(sz)` |

For `τ`, the three identities are `T t_0 = t_1 T`, `T t_1 = t_0 T` and `T t_2 = t_2 T`. The second
follows from the first because `T^2 = 1`. In characteristic 3, write `T(z) = (1 − (1−s)z)/((1−s) − sz)`.

*First identity.* Put `w = σz`. Then `σ(T(z)) = T^σ(w)` with
`T^σ(w) = (1 − (1+s)w)/((1+s) + sw)`. For `y = N/D` we have `C(y) = (D − N)/(D + N)`. So:

    C(s·T^σ(w)) = (1 − sw + s²w)/(1 − s − s²w) = T(sw).

*Third identity.* Both sides equal the same expression:

    T(−C(sz)) = (−1 − s + s²z)/(1 + sz + s²z) = −C(s·T(z)).

`mobius281.py` checks all twelve identities and `T^2 = 1` exactly. A map `z ↦ R(σ^ε z)` is stored
as the pair `(ε, R)`, and composites are compared as pairs. The two pairs agree as maps on the
infinite set `O` if and only if they agree as pairs. It also runs two negative controls
(`T t_0 = t_0 T` and `A_{a_1} t_1 = t_1 A_{a_1}`), which it correctly rejects. ∎

**Proposition 3.** `Φ ∘ g = A_g ∘ Φ` on `X^ω` for each generator `g`. So
`g ↦ Φ g Φ^{-1}` is an isomorphism from `K` onto the group `⟨σ, −σ, N, T⟩` of permutations of `O`.

*Proof.* Show `Φ(g(w)) ≡ A_g(Φ(w)) mod s^k` for all `g` and `w`, by induction on `k`. The case
`k = 0` is empty.

For `w = xw'`, Lemma 2 gives

    A_g(Φ(w)) = A_g t_x(Φ(w')) = t_{out_g(x)}(A_{g|_x}(Φ(w'))).

On the other hand, `Φ(g(w)) = t_{out_g(x)}(Φ(g|_x(w')))`. By induction the arguments agree
modulo `s^k`, and `t_{out_g(x)}` is `|s|`-Lipschitz, so the two sides agree modulo `s^{k+1}`.

`Φ` is a bijection, so `g ↦ ΦgΦ^{-1} = A_g` extends to words. Two words define the same element of
`K` if and only if they act the same on `X^ω`, if and only if the `A`-words act the same on `O`. ∎

## 3. An element of infinite order

`ΦτΦ^{-1} ∘ Φa_2Φ^{-1} = T∘N`, and `T(−z) = (u + z)/(1 + suz)` has matrix `g = I + E` with
`E = (0, u; su, 0)` and `E^2 = su²·I`.

Let `π = u√s` in the quadratic extension `L = F_3((√s))`. Then `E ↦ π` gives `F_3((s))[E] ≅ L`, so
`g^n = a_n I + b_n E`, where `(1 + π)^n = a_n + b_n π` with `a_n, b_n ∈ F_3((s))`.

The Möbius map of `g^n` is the identity on `O` exactly when `g^n` is scalar, i.e. `b_n = 0`. A
Möbius map fixing three points of `P^1` is trivial, and `O` is infinite. Now `b_n = 0` means
`(1+π)^n = (1−π)^n`, i.e. `ρ^n = 1` with `ρ = (1+π)/(1−π)`.

`ρ` is a principal unit of `F_3[[√s]]` other than 1. Principal units in characteristic `p` are
torsion-free. Write `n = 3^k m` with `3 ∤ m` and `ρ = 1 + y`, `y ≠ 0`, `|y| < 1`. Then
`ρ^n = (1 + y^{3^k})^m = 1 + m y^{3^k} + (higher order)`, which is not 1.

So `T∘N` has infinite order. By Proposition 3, `τa_2` has infinite order in `K`, which proves the
Theorem. ∎

`mobius281.log` also lists the order of `τa_2` on levels 1–9: `3, 9, 9, 9, 27, 27, 27, 27, 27`. This
is the logarithmic growth predicted by `(1 + π)^{3^k} = 1 + π^{3^k}`.

## 4. Remarks (not used above)

- **`K` is not torsion.** This refutes the Gupta–Sidki reading in
  `bmw-44-sat-survivor-parity-kernels-not-left-orderable`. Sampled elements of `K''` looked like
  bounded 3-power orders because in a linear pro-3-by-`V_4` group the order of an element on level `m`
  grows only logarithmically in `m`.
- **The self-replication route is false.** `L_2` is not self-replicating at `0`. Modulo level 5,
  `φ_0(Stab_{L_2}(0))` has index 3 in `L_2`, and generators 4, 6 and 7 of `l2rep.py` are not in it
  (`l2test.log`). The section chain `G_{k+1} = φ_0(Stab_{G_k}(0))` strictly decreases
  (`chain.log`). In the model, the `G_k` sit in the congruence levels `γ ∈ s^{k+1}O`, which decrease
  to the affine group.
- **Closure.** `A_g` lies in the semilinear Iwahori Möbius group
  `M̂ = {z ↦ (αz+β)/(γz+δ) ∘ σ^ε : γ ∈ sO}`, whose image on `O/s^m` has order `4·3^{3m−2}`. The level
  orders of `K` equal this through `m = 7` (`chain.log`), and `compare.log` matches the two groups on
  every computed invariant for `m ≤ 4`. That `K` is dense in `M̂` is expected but not proved.
