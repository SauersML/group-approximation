---
rg: 2
id: free-shift-houghton-envelopes-local-stability-proof
kind: route
title: Relations of a free-shift envelope survive every finite-prescription perturbation of the enumeration, while the conjugation relations of rho on transpositions do not
target: free-shift-houghton-like-envelopes-are-not-fp
requires:
  - houghton-like-groups-are-strongly-shift-similar
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - regular-enumerations-can-make-near-shift-free-product
---

Lane proof, not independently reviewed. Notation as in the target. Write `X = [n] x N`. Each ray `{k} x N` is
split into its even and odd strands, and each strand is identified with `N` (source convention `N = {1,2,...}`,
transported to this graph's convention as in the citation node). In these coordinates:
- `rho^(k)_g` acts on the even strand of ray `k` by `lambda_g`, where `lambda_g(nu(h)) = nu(gh)`, and is the
  identity elsewhere.
- It is a genuine permutation, with no exceptional points.

## Germ shape of the K-letters

Every element `a` of `K = H_n(E_2)` agrees, outside a finite set `Φ_a ⊂ X`, with a **strand map**: each strand `j`
goes to one strand `j'` by `m -> m + c_(a,j)`. The reason is that `E_2` elements are eventually 2-periodic, and
`H_n` / `H_n(E_2)` elements are, on each quasi-ray, `beta ∘ g ∘ beta^-1` with `g ∈ E_2`, hence eventually strand
shifts. Fix a word `w = l_1 ... l_L` in the generators. Let `E` be the union of the `Φ_a` over the K-letters
occurring in `w`, together with the finitely many points where a strand map with `c < 0` would be undefined. Then
`E` is finite.

## Item 1 (local stability)

Put `F = P * <ŝ>`. For a point `x` and a bijection `nu'`, follow the trajectory `x_L = x`, `x_(i-1) = l_i(x_i)`.
Call the trajectory **regular** if no K-letter is applied at a point of `E`. Along a regular trajectory:
- every K-letter acts by its strand map, contributing `ŝ^(c)` and a change of strand;
- every `rho^(k)_g` contributes `lambdâ_g` if the current point is on the even strand of ray `k`, and nothing
  otherwise.

So the starting strand `j` and the word `w` determine the strand sequence and a formal element `u_j(w) ∈ F`. They
do not depend on `x` or `nu'`.

**Regular trajectories.**
- All but finitely many points have regular trajectories, so the near class of `w(nu)` on strand `j` is the image
  of `u_j(w)` under `F -> R_nu`, `lambdâ_g -> lambda_g`, `ŝ -> s`, carried to the end strand.
- Since `w(nu) = 1`, the end strand is `j`, and the image of `u_j(w)` is trivial.
- By the hypothesis that `F -> R_nu` is injective, `u_j(w) = 1` in `F`.
- `F = P * <ŝ>` has the normal form theorem, so `u_j(w)` reduces to the empty word by merging adjacent `lambdâ`
  letters through the multiplication of `P` and merging adjacent `ŝ` powers.
- Each such step is an identity of partial maps wherever defined, for every `nu'`: `lambda'_g lambda'_h = lambda'_(gh)`
  because `lambda'` is an action of `P`, and `s^a s^b = s^(a+b)` where defined.
- Every point of a regular trajectory lies in the domain of the next map. So for every `nu'` and every `x` with a
  regular trajectory, `w(nu')(x) = x`.

**Exceptional trajectories.**
- If the trajectory passes through `e ∈ E` at step `i`, it is determined by `e`, `i` and the letters, computed
  forward to `x_0` and backward to `x_L`.
- These finitely many computations, of length at most `L` from the finite set `E`, use `lambda'_g^(±1)` at finitely
  many points. The values `lambda'_g(nu'(h)) = nu'(gh)` and `lambda'_g^-1(nu'(h)) = nu'(g^-1 h)` depend only on
  `nu'` at finitely many elements of `P`.
- Let `S` be the finite set of such elements used in the computations for `nu`. If `nu'` agrees with `nu` on `S`,
  every exceptional computation gives the same points for `nu'` as for `nu`.
- So the exceptional trajectories for `nu` and `nu'` are the same trajectories. Their starting points and images
  coincide, and `w(nu)(x) = x` gives `w(nu')(x) = x`.

Hence `w(nu') = 1` for every `nu'` agreeing with `nu` on `S`.

## Item 2 (not finitely presented)

Suppose `Γ_nu` is finitely presented. A finitely presented group has a finite presentation on any finite
generating set, so take `Γ_nu = <Y | r_1, ..., r_m>` with `Y` the generating set above.

**Choice of `nu'`.**
- Let `S = S_(r_1) ∪ ... ∪ S_(r_m)` from item 1, and fix a generator `g ≠ 1` of `P`.
- Choose `h ∈ P` with `h ∉ S` and `gh ∉ S`.
- Let `nu'` agree with `nu` except that the values at `gh` and at some `h' ∉ S ∪ {h, gh}` are swapped. Then `nu'`
  agrees with `nu` on `S ∪ {h}` and `nu'(gh) ≠ nu(gh)`.
- By item 1, every `r_i` is trivial for `nu'`. So `y -> y(nu')` defines a homomorphism `φ : Γ_nu -> Sym(X)` that
  fixes each K-letter.

**The failing relation.**
- Let `x` be the point `nu(h)` on the even strand of ray 1, and `z` a point on an odd strand.
- `K ⊇ FSym(X)`, so there are K-words `t` for the transposition `(x z)` and `t'` for `(lambda_g x, z)`.
- The word `r = rho^(1)_g t (rho^(1)_g)^-1 t'^-1` is trivial in `Γ_nu`, because `rho^(1)_g` fixes `z` and sends `x`
  to `lambda_g x`.
- But `φ(r) = (lambda'_g x, z)(lambda_g x, z)`. Here `lambda'_g x = nu'(gh) ≠ nu(gh) = lambda_g x`, so this is a
  3-cycle and not 1. That contradicts `r = 1`. ∎

## Item 3 (finite determination)

Let `Γ_nu = <Y | R>` with `R` finite, and let `nu'` make every word of `R` trivial. Then `φ` as above is a
homomorphism, so every relation of `Γ_nu` holds for `nu'`.
- In particular every word `r` of the item-2 form holds, for all points `x` of the even strand of ray 1 and all
  generators `g`. So `lambda'_g = lambda_g` for all `g`.
- Put `θ = nu^-1 ∘ nu'`. Then `nu'(gh) = lambda_g(nu'(h))` gives `θ(gh) = g θ(h)`, so `θ(h) = h θ(1)`.
- Hence `nu'(h) = nu(h c)` with `c = θ(1)`. ∎

## Item 4

This is item 2 with `P = Z` and `n = 3`, together with item 3 of
`houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`. Such `nu` are supplied by
`regular-enumerations-can-make-near-shift-free-product`. ∎

## Checks

- **`n = 1`.** Item 2 reproves consequence 3 of `mz-envelope-fp-forces-two-sided-fg-near-index-kernel` for these
  enumerations.
- **The zigzag enumeration of `Z`,** whose `E_nu(Z)` is finitely presented. Its near relation
  (`lambda ~ s^2` far out) is destroyed by changing `nu` far away, so item 1 fails there, as it must.
- **Houghton groups.** No `rho` letters and nothing to perturb, so there is no conflict with `H_n` being finitely
  presented for `n >= 3`.
