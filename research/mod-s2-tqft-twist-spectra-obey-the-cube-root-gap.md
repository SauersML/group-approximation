---
rg: 2
id: mod-s2-tqft-twist-spectra-obey-the-cube-root-gap
kind: claim
title: A separating twist whose spectrum is a Galois-stable set of modular twists is either an exact tenth-root scalar or at distance at least sin(pi/24) from every scalar, so TQFT-type representations of Mod(S_2) obey the cube-root gap
distinct_from:
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that asks for a uniform cube-root gap over all exact representations; this proves it with constant sin(pi/24) for the subclass whose separating-twist spectrum is a Galois-stable set of twists of a modular category, closed under sums, tensor products and characters.
  mod-s2-torelli-characters-have-a-metaplectic-maslov-line: its (ML3) handles exactly scalar separating twists, and it is used here as the endpoint; this adds the near-scalar-to-scalar step, by Galois rigidity, for twist spectra of modular categories.
  mod-s2-jones-rectangular-separating-twist-spectrum: that computes a continuous non-TQFT family whose separating twist becomes near-scalar; this shows no such thing can happen when the spectrum is a Galois-stable set of modular twists, and names Galois stability as the property the Jones deformation breaks.
---

**ESTABLISHED** (T1)--(T4) through `mod-s2-tqft-twist-spectra-cube-root-gap-proof`. Unreviewed; no novelty
claimed. The TQFT reading (T5) is conditional and is **not** part of the established statement.

## Setting

- `M = Mod(S_2)` and `t_s` is a separating Dehn twist.
- `omega = exp(2 pi i/3)`.
- `||x||` is the distance from a real `x` to `Z`.
- A *modular datum* is a modular category `A` over `C` in the sense of `dln-galois-symmetry-of-modular-twists`. It has:
  - simple labels `Pi`;
  - twists `theta_i`;
  - Galois permutations `sigma^`, one for each `sigma in Aut(Q_ab)`.
- A subset `L` of `Pi` is *Galois-stable* if `sigma^(L) = L` for every `sigma`.
- A unitary `U` on a finite-dimensional space is of *twist type* `(A, L, lambda)` if all of the following hold:
  - `L` is a nonempty Galois-stable set of labels;
  - `lambda` lies in `U(1)`;
  - the set of eigenvalues of `U` is `{ lambda theta_a : a in L }`.

  Multiplicities are arbitrary but positive.

## Statement

1. **(T1) Unit-square spread (sharp).** For `n >= 2` and `gcd(k, n) = 1`,
   ```text
   max over units j mod n of || k j^2 / n ||  >=  1/24,
   ```
   with equality for `(n, k) = (24, +-1)`. If `n` does not divide `24`, the maximum is at least `1/20`.
2. **(T2) Galois rigidity of twist spectra.** If `U` is of twist type `(A, L, lambda)`, then exactly one of the
   following holds:
   - `theta` is constant on `L`, so `U = lambda theta_a I` is scalar;
   - `U` has two eigenvalues at distance at least `2 sin(pi/24)`, so `||U - mu I||_op >= sin(pi/24) ~ 0.1305` for
     every `mu in C`.
3. **(T3) The adjoint labels are Galois-stable.** If `A` is pseudounitary with its canonical spherical structure
   (for example a unitary MTC), then `Irr(A_ad)` is Galois-stable.
4. **(T4) Cube-root gap for the TQFT-type class.** Let `T` be the class of finite-dimensional unitary
   representations `rho` of `M` such that `rho(t_s)` is of twist type for some modular datum. Let `T^` be the
   closure of `T` under tensoring with characters of `M` and under tensor products. Then:
   - every member of `T^` satisfies the dichotomy of (T2): `rho(t_s)` is scalar, or it has two eigenvalues at
     distance at least `2 sin(pi/24)`;
   - every *finite direct sum* `rho` of members of `T^` satisfies, for every `mu in U(1)`,
     ```text
     || rho(t_s) - mu I ||_op  >=  min( sin(pi/24), dist(mu, mu_10) ),
     || rho(t_s) - omega^(+-1) I ||_op  >=  sin(pi/24)  ~  0.1305,
     ```
     since `dist(omega^(+-1), mu_10) = 2 sin(pi/30) ~ 0.2091`.
5. **(T5) TQFT reading (conditional, not established).**
   - Let `C` be a unitary MTC and `rho` an honest unitary lift of its Reshetikhin--Turaev genus-two
     representation. Such lifts exist for `C box C`, because `H^2(M; U(1)) = Z/2`.
   - Then `rho(t_s)` has spectrum `lambda { theta_a : a in A_0 }`, where `A_0 = { a : a <= x tensor x* for some x }`
     is the set of channels of the separating pants decomposition `V(S_2) = sum_a V(T_(1,1); a) tensor V(T_(1,1); a*)`.
   - Hence `rho` is in `T` whenever `A_0 = Irr(C_ad)`. This holds, for example:
     - for `SU(2)_k`, where `x = k/4` or `x = (k-1)/4` reaches every integer spin up to the maximum `(k - (k mod 2))/2`;
     - for pointed `C`;
     - for Ising-type categories.

     It is preserved by `box`.
   - Two inputs are used without verbatim citation:
     - the gluing description of the Dehn twist on a colored cut circle, from the standard modular functor axioms
       (Bakalov--Kirillov, Turaev);
     - the equality `A_0 = Irr(C_ad)` in general.

## Reading

- **Class kill (type 3).**
  - *Invariant:* the squared Galois action `sigma^2` on ratios of eigenvalues of `rho(t_s)`.
  - *Where every member dies:* the step "the spectrum of `rho(t_s)` is near a single point". Galois rigidity makes it
    exactly a point. Then (ML3) of `mod-s2-torelli-characters-have-a-metaplectic-maslov-line` pins that point in `mu_10`,
    which is at distance `2 sin(pi/30)` from `omega^(+-1)`.
  - *What is killed:* every attempt to refute `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap` (and so
    the flagship `deligne-triple-cover-exact-mf-radical`) with quantum or TQFT representations, their sums, tensor
    products and character twists, whenever their twist labels are Galois-stable. The constant does not depend on the
    level or the category.
- **What a witness must do.** An exact near-cube-root representation must have a separating-twist spectrum that is not
  a Galois-stable set of modular twists. Three ways to do this:
  - *Transcendental eigenvalues.* An example is the Jones rectangular deformation at generic `x`, where
    `exp(96 i x/5)` is not a root of unity and no Galois group acts.
  - *A non-Galois-stable sub-multiset.* This can come from an irreducible summand of an RT representation that sees
    only part of the channels.
  - *Non-modular origin.*
- **Heuristic dictionary (not used in proofs).** The RT anomaly contributes `exp(2 pi i c tau/8)`. Through the Meyer
  class this suggests the parameter `theta = c/2 mod 1` for `P_op`. For example, `SU(2)_16` has `c = 8/3` and
  `theta = 1/3`. Under (T5), (T2) applied to `L = Irr(C_ad)` says that such a category puts its own separating twist
  near a scalar only when every adjoint twist is exactly `1`. Otherwise two channels sit at distance at least
  `2 sin(pi/24)` apart. So the anomaly parameter never transfers to a near-scalar separating twist inside TQFT.
- **Numerics.** `experiments/tqft-galois-gap-2026-09-17/unit_square_spread.py` computes the exact minimum in (T1) for
  `n <= 1200`. It is `1/24`, attained only at `(24, +-1)`. For `n` not dividing `24` it is `1/10`, attained at `(10, 1)`.

## What is not claimed

- Nothing is claimed for representations whose `rho(t_s)` spectrum is not of twist type. This includes irreducible
  summands of RT representations whose channel set is not Galois-stable, and representations with transcendental
  eigenvalues.
- (T5) is a reading, not a theorem here.
- No statement about asymptotic (non-exact) homomorphisms is made.
