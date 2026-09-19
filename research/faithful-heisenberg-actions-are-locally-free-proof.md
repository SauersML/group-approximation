---
rg: 2
id: faithful-heisenberg-actions-are-locally-free-proof
kind: route
title: Pick a point whose centre orbit is longer than the ball, then move it by a^s b^t; each short non-central element is fixed only on a line or a small congruence class of (s,t)
target: faithful-heisenberg-actions-are-locally-free-at-every-scale
requires: []
---

Notation is as in the target. `π : H → Z^2` is abelianization, with
`π(a) = (1,0)` and `π(b) = (0,1)`. Put `ω((x,y),(x',y')) = xy' − yx'`.

## 1. Facts about H

- **(N) Normal form.** Every `g ∈ H` is uniquely `a^x b^y c^z`, with
  `π(g) = (x,y)`.
- **(L) Length.** If `|g|_w ≤ R`, then `|x| + |y| ≤ R` and `|z| ≤ R^2`. The
  first holds because `π` is `1`-Lipschitz to `ℓ^1`. For the second, push a
  word of length `L` into normal form: each letter `a^{±1}` passes at most `L`
  letters `b^{±1}` and each crossing creates one central letter. This is the
  "central length" step of `heisenberg-not-in-full-groups-of-z3-actions-pansu-proof`, §3.
- **(C) Commutators.** `[u,v] = c^{ω(πu,πv)}` for all `u, v`. Since
  `[H,H] = ⟨c⟩` is central, `[·,·]` is bi-multiplicative and depends only on
  `πu` and `πv`. It is alternating and `[a,b] = c`. Hence for every `g, h`,
  `h^{-1} g h = g[g^{-1}, h^{-1}] = g c^{ω(πg, πh)}`.

## 2. Choosing the base point

Fix `R ≥ 1` and put `M = R^2 + R·|B(R)|`. Since `ρ` is injective and `c` has
infinite order, `ρ(c)^{M!} ≠ id`, so some `q ∈ Ω` has `ρ(c)^{M!} q ≠ q`.

Let `m ∈ {1, 2, …} ∪ {∞}` be the size of the `⟨ρ(c)⟩`-orbit of `q`. Then
`Stab(q) ∩ ⟨c⟩ = ⟨c^m⟩` (read `⟨c^∞⟩ = 1`). Every `k ≤ M` divides `M!`, so
`m > M`. Put `S = Stab(q)`. For `h ∈ H`, `Stab(ρ(h)q) = hSh^{-1}`.

- **Central elements.** Let `g = c^z ∈ B(R)` with `z ≠ 0`. By (L),
  `0 < |z| ≤ R^2 < m`, so `g ∉ hSh^{-1} ∩ ⟨c⟩ = ⟨c^m⟩`. Such a `g` fixes no
  point of `ρ(H)q`.

## 3. Non-central elements

Let `g = a^x b^y c^z ∈ B(R)` with `(x,y) ≠ 0`. Put
`Z_g = {w ∈ Z : a^x b^y c^w ∈ S}`. If `w, w' ∈ Z_g` then
`c^{w−w'} ∈ S ∩ ⟨c⟩`, so `Z_g` has one of three forms:

- it is empty;
- it is a coset `w_g + mZ` (when `m < ∞`);
- it is a single point `{w_g}` (when `m = ∞`).

Take `h = a^s b^t`. By (C), `h^{-1} g h = a^x b^y c^{z + xt − ys}`. So
`g` fixes `ρ(h)q`, i.e. `h^{-1}gh ∈ S`, if and only if
`z + xt − ys ∈ Z_g`. Call `(s,t)` *bad for `g`* when this holds. The form
`ℓ_g(s,t) = xt − ys` is nonzero.

- **Case `m = ∞`.** The pairs that are bad for `g` form the empty set or the
  line `ℓ_g(s,t) = w_g − z` in `Z^2`. There are finitely many `g ∈ B(R)`, and
  finitely many lines never cover `Z^2`. Take `(s,t)` on none of them.
- **Case `m < ∞`.** Badness depends only on `(s,t) mod m`. The homomorphism
  `ℓ_g : (Z/m)^2 → Z/m` has image `d(Z/m)`, where `d = gcd(x,y,m)`. So each
  fibre is empty or has `m^2/(m/d) = md` elements.
  - `d` divides a nonzero entry among `x, y`, so `d ≤ R` by (L).
  - At most `mR` classes mod `m` are bad for each `g`.
  - At most `|B(R)|·mR < m^2` classes are bad for some `g`, because
    `m > M ≥ R|B(R)|`.
  - So some class `(s,t) mod m` is bad for no `g`.

## 4. Conclusion

In both cases take `(s,t)` bad for no non-central `g ∈ B(R)`, and put
`p = ρ(a^s b^t) q`.

- No non-central `g ∈ B(R)` fixes `p` (§3).
- No nontrivial central `g ∈ B(R)` fixes `p` (§2).
- So `Stab(p) ∩ B(R) = {1}`.

If `h, h' ∈ B(R/2)` and `ρ(h)p = ρ(h')p`, then `h^{-1}h' ∈ Stab(p) ∩ B(R)`,
so `h = h'`. ∎

## 5. Trust surface

The proof is elementary and self-contained. It uses the normal form of `H`,
the quadratic bound on central length, and the bilinear commutator formula of
a class-2 nilpotent group. It uses no geometry of `Ω`.
