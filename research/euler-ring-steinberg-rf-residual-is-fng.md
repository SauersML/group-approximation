---
rg: 2
id: euler-ring-steinberg-rf-residual-is-fng
kind: claim
title: For some l and N >= 5, the finite residual of St_N(D) over the Euler ring D is finitely normally generated
distinct_from:
  euler-triangular-steinberg-rf-residual-is-fng: that is the same question for St_N(T_l); by euler-triangular-steinberg-retracts-to-euler-steinberg it implies this one, so this is a necessary condition for the triangular route.
  resolvent-steinberg-rf-residual-is-finitely-normally-generated: that is the R_l version, refuted by the corner tame symbols; this concerns only the Euler ring, where the relevant symbols are the {π_0, π_q} of gq-k2-q.
---

**OPEN.** There are a prime `l` and `N >= 5` such that the finite residual `St_N(D)_rf` is finitely
normally generated.

**Why it decides the triangular route.** It is necessary for
`euler-triangular-steinberg-rf-residual-is-fng` (route `euler-ring-residual-fng-from-triangular-residual-fng`).
So if it fails, the route through `T_l` to `z-localized-embeds-in-fp-rf-group` is closed.

**The symbols at stake.** Put `π_k = u + 1 + kl`, units of `D`. gq-k2-q (29881297a) shows that the
Steinberg symbols `c_q = {π_0, π_q}`, for primes `q != l`, are independent in `K_2(D)`, detected by
`I_p(z) = Σ_k k·v_p(∂_k z)`. The question is whether some infinitely generated part of `<c_q>` dies in every
finite quotient. If so, and `K_2(N, D)` is central, this claim fails.

## Attempts

1. **Partial detection analysis (2026-09-18, lane gq-infinite-primes).** The claim is not decided. Every
   finite quotient of `St_N(D)` factors through `St_N(F)` for a finite quotient ring `F` of `D`
   (`steinberg-rf-forces-ring-rf`). In such an `F`:
   - *Periodicity.* The class of `l` has some additive order `o`. Since `π_q = π_0 + ql`, the image of `c_q`
     depends only on `q mod o`. Also `x̄` has finite order `n`, with `nl = 0`. So each finite quotient sees
     `<c_q>` through finitely many images. This is elementary.
   - *Semisimple quotients kill every `c_q`.* `K_2` of a finite semisimple ring is 0 (finite fields and Morita
     invariance; textbook, not read at source here).
   - *Split crossed products kill every `c_q` for `q` odd.* In characteristic `q^r` with `q != l`, Artin–Schreier
     quotients `GR(q^r, q) ⋊ <φ> ≅ M_q(Z/q^r)`, with `φ(π) = π + l`, factor the symbols through
     `K_2(Z/q^r) = 0` for `q` odd (Dennis–Stein, as read at source by gq-k2-q, 69ed7e51a).
   - *What could detect.* A finite quotient whose radical carries a nontrivial Dennis–Stein symbol above
     `{π̄_0, π̄_q}`. The smallest candidate is `F_(2,l) = C ⋊ <X>`, with `C = Z/l^2[y]/(y^2, ly)` and
     `X y X^(-1) = y + l`, `X^l = 1`: the image of `D` acting on `M_(2,l)` of `euler-triangular-ring-is-fp-rf`.
     Computing the image of `c_1 = {1+y, 1+y+l}` in `K_2(F_(2,l))`, and more generally for
     `F_(r, l^(r-1))`, is a finite computation. It was not done here.
   - *2-primary quotients exist for every `l`.* For `l` odd, `u -> ω` (a primitive cube root of unity in `F_4`)
     and `x -> φ` (Frobenius) give `D -> F_4 ⋊ <φ> ≅ M_2(F_2)`, because `π_0 -> ω^2`, `π_1 -> ω` and `φ(ω) = ω + 1`.
     So 2-primary detection, of the type `K_2(Z/4) = Z/2`, is not excluded a priori.
   - *Sufficient for failure.* If the images of `<c_q>` in `lim_F K_2(N, F)` form a finite group (gq-k2-q's
     formulation), `St_N(D)_rf ∩ <c_q>` has infinite rank.
2. **Design constraint (2026-09-18, lane gq-infinite-primes).** `Z_(l) ⊆ M` comes from the lamps `π_k` acting
   invertibly on `M`. Finite presentation needs these inverses as ring relations (the two-sidedness of
   `euler-base-annihilator-over-lamplighter-is-not-fg`), and that makes the `π_k` units of the ring, which
   creates the symbols `{π_0, π_q}`.
   - A repair needs the `π_k` to act invertibly on `M` without being units of the top ring, while the inverse
     relations still propagate from finitely many relators.
   - Relators that only act on `M`, such as `(x^k B x^(-k))(π_k) - 1` killing the generator, are module
     relations, and those do not propagate (same lemma).
   - This lane sees no concrete way around it.
3. **The two-step quotient and the cyclotomic orbit (2026-09-18, lane gq-k2-q).** Not decided. See
   `euler-ring-symbols-in-small-finite-quotients`.
   - *`F_(2,l)` kills every `c_q`,* already in `K_2(N, C)`.
     - For `l` odd, `c_q = z^q` with `z = {1+y, 1+l}`. The Steinberg relation `{t(1+y), 1 − t(1+y)} = 1` kills `z` for
       any `t` with `P(t) = Σ_(k<l) t^k/k != 0` in `F_l`, and such `t ∉ {0,1}` exists.
     - For `l = 2`, `c_q = {1+y, −(1+y)} = 1`.
   - *The cyclotomic point detects `c_q` on `A`, but its orbit does not.*
     - Under `u -> ζ_l − 1`, the image of `c_q` in `K_2(O_K/𝔭^n) ≅ Z/l` (`n >= l+1`) has Hilbert symbol `ζ^(-q)`.
     - The σ-orbit of that point has length `m` divisible by `l`. The induced `D -> M_m(O_K/𝔭^n)` therefore sends
       `c_q` to `ζ^(-qm) = 1`.
   - *Still open:* the folding quotients `F_(r,N)` with `r >= 3`, and `K_2` of the crossed product `ρ_m(D)` itself,
     where the commutative part still sees `c_q`.
