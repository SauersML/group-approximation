---
rg: 2
id: split-letter-lift-translation-count-proof
kind: route
title: A cofinitely translating injective transport of quiescent data bounds the defect count, and charge noncreation finishes
target: translating-transport-split-lifts-are-surjective
requires:
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof. Notation as in the target. Automata act by `Φ(y)(h) = φ((h^{-1} y)|_N)`, so the output at `h`
depends only on `y|_{hN}`.

## Theorem A

Fix a finitely supported `u` and write `E = E(u)`, `E' = E(τ u)`, `s = s_u`, `Q = Q_u` and `T = T_u`. Let `F` be a
finite set containing `F_u ∪ E`. The translation hypothesis still holds for `g ∉ F`.

1. **The far output sites are quiescent.** For `g ∉ F`, the coordinate `T(z)(gs)` exists, so `gs ∈ Z(τ u)`. Thus
   `(G \ F)s ∩ E' = ∅`, that is `E' ⊆ Fs`, and

       Z(τ u) = (G \ F)s  ⊔  (Fs \ E').

2. **A finite injection.** Fix `c ∈ Q^{G \ F}`. Let `z1 != z2` in `Q^{Z(u)}` both extend `c` (note `G \ F ⊆ Z(u)`).
   - For `g ∉ F`, the coordinates `T(z1)(gs)` and `T(z2)(gs)` are the same relabelling of `c(g)`, so they agree.
   - Since `T` is injective, `T(z1) != T(z2)`, so by step 1 they differ on `Fs \ E'`.

   Hence `z|_{F \ E} -> T(z)|_{Fs \ E'}` is injective on the extensions of `c`, and
   `|Q|^{|F| - |E|} <= |Q|^{|F| - |E'|}`.

3. **The count.** Since `|Q| >= 2`, this gives `|E(τ u)| <= |E(u)|`.

4. **Charge noncreation.** Rename `a0` as `0` and give every other symbol charge `1`, so `W(x) = |E(x)|` and `0` is
   the unique zero-charge symbol. Then:
   - `τ` fixes `0^G`;
   - `τ` is injective on finitely supported configurations;
   - by step 3, `W(τ x) <= W(x)` for every finite `x`.

   `finite-injective-charge-noncreation-forces-surjectivity` states: "Then equality holds for every finite x.
   Moreover, tau is bijective on each finite-configuration charge sector, and is surjective on A^G." This gives
   Theorem A.

5. **Addendum: the finite transports are bijective.** With equality, `|F \ E| = |Fs \ E'|`. So the injection of
   step 2 is a bijection for each `c`. Given `w ∈ Q^{Z(τ u)}`, invert the relabelling on `(G \ F)s` to recover `c`,
   then choose the preimage of `w|_{Fs \ E'}`. So `T_u` is surjective.

Locality of `T_u` is never used, only its injectivity and the cofinite translation.

## Theorem B

1. **The rest constant is fixed.** The fibre `r^{-1}(a0^G) = ({a0} × Q)^G` has more than one point, and `Φ` maps it
   injectively into the fibre over the constant `τ(a0^G) = b^G`. If `b != a0`, that fibre is a single point. So
   `τ(a0^G) = a0^G`.

2. **The memory contains `s^{-1}`.** The output `Φ((a0, z))(gs) = (a0, π(z(g)))` depends only on `z|_{gsN}`. Since `π`
   is a bijection and `|Q| >= 2`, it depends on `z(g)`. Hence `g ∈ gsN`, that is `s^{-1} ∈ N`.

3. **The transport.** Fix a finitely supported `u` with `E = E(u)`, and put `F_u = E N^{-1} s^{-1}`, which is finite.
   Identify `r^{-1}(u)` with `Q^{Z(u)}` and `r^{-1}(τ u)` with `Q^{Z(τ u)}`, and let `T_u` be the restriction of `Φ`.
   It is injective because `Φ` is.
   - Let `g ∉ F_u`. Then `gsN ∩ E = ∅`, so the restriction `y|_{gsN}` of any `y ∈ r^{-1}(u)` lies in
     `({a0} × Q)^{gsN}`.
   - Choose `z̃ ∈ Q^G` with `(a0, z̃)` equal to `y` on `gsN`. By locality and step 2,
     `Φ(y)(gs) = Φ((a0, z̃))(gs) = (a0, π(z̃(g)))`, and `z̃(g)` is the `Q`-coordinate of `y` at `g ∈ gsN`.

   So `T_u(z)(gs) = π(z(g))` for `g ∉ F_u`.

4. **`τ` is surjective.** `τ` is injective, it fixes `a0^G` by step 1, and step 3 supplies the transports with
   `s_u = s` and `Q_u = Q`. Theorem A applies.

5. **`Φ` is surjective.**
   - `τ` is bijective.
   - By the addendum, every `T_u` with `u` finitely supported is a bijection onto `r^{-1}(τ u)`.
   - So `Φ(B^G)` contains every `y` with `r(y)` finitely supported, because `r(y) = τ(u)` for a finitely supported
     `u`: `τ` preserves the count, hence maps finite configurations onto finite ones by the equality on sectors.
   - These `y` are dense in `B^G`, and `Φ(B^G)` is closed, so `Φ` is surjective.

So neither `τ` nor `Φ` is strict.
