---
rg: 2
id: sofically-trivial-iff-positive-permutation-cheeger-proof
kind: route
title: Restrict almost-actions to their invariant support, lift homomorphisms into the sofic ultraproduct, and correct by genuine actions
target: sofically-trivial-iff-positive-permutation-cheeger
requires:
  - elek-szabo-sofic-permanence
  - local-approximation-properties-are-marked-closed
---

The notation is that of the claim. `S_omega` is the metric ultraproduct
`prod_k Sym(n_k) / N_omega` for a nonprincipal ultrafilter `omega` on `N`
and a sequence `n_k -> infinity`, with the normalized Hamming length `e`.

## Standard inputs

- (I1) A countable group is sofic iff it embeds in `S_omega`. In particular,
  every countable subgroup of `S_omega` is sofic.
- (I2) For countable `Q`, the quotient `Q / Rad_sof(Q)` is sofic.
  - For each `g` not in `Rad_sof(Q)`, pick a homomorphism `phi_g` into a sofic
    group with `phi_g(g) != 1`.
  - For a finite `F` in `Q / Rad_sof(Q)`, finitely many `phi_g` separate
    `F u F.F`. Their product is a homomorphism into a finite direct product of
    sofic groups, which is sofic (`elek-szabo-sofic-permanence`), and it is
    injective on `F u F.F`.
  - So the table of `F` has sofic models. By locality
    (`local-approximation-properties-are-marked-closed`), `Q / Rad_sof(Q)` is
    sofic.
  - Hence `Q` is sofic iff `Rad_sof(Q) = 1`.

## Invariant-support lemma

Let `sigma : S -> Sym(n)` and let `V` be the set of points moved by at least
one `sigma(s)`.

- The complement `F = [n] \ V` is fixed pointwise by every `sigma(s)`. So `F`,
  and therefore `V`, is invariant under every `sigma(s)^{+-1}`.
- Every word acts trivially on `F`. So `e(sigma(w)) <= |V|/n = supp(sigma)`.
- If `V` is nonempty, the restriction `sigma|_V : S -> Sym(V)` has
  `supp = 1`, and `e(sigma|_V(w)) = e(sigma(w)) . n/|V|` for every word `w`.

## Linear rate from (b)

Assume `h = h(S|R) > 0` and let `sigma` be arbitrary with `V` nonempty.
Applying the definition of `h` to `sigma|_V` gives

```text
h <= delta(sigma|_V) = delta(sigma) . n/|V|,
```

so `supp(sigma) <= delta(sigma)/h`. Together with the lemma this is the
displayed rate.

## (b) => (e)

- Let `phi : Q -> S_omega` be a homomorphism, and choose lifts
  `sigma_k : S -> Sym(n_k)` of `phi` on the generators.
- Every relator is trivial in `S_omega`, so `lim_omega delta(sigma_k) = 0`.
- By the rate, `lim_omega e(sigma_k(s)) = 0` for each `s`, so `phi(s) = 1`.

## (e) => (b)

- Suppose `h = 0`. Choose `sigma_k : S -> Sym(n_k)` with `supp(sigma_k) = 1`
  and `delta(sigma_k) <= 1/k`. Replacing `sigma_k` by a disjoint union of
  copies changes neither `supp` nor `delta`, so we may assume `n_k -> infinity`.
- The `sigma_k` define a homomorphism `phi : Q -> S_omega`, since relators have
  vanishing length.
- Every point is moved by some generator, so `sum_s e(sigma_k(s)) >= 1`. Hence
  for each `k` some `s` has `e(sigma_k(s)) >= 1/|S|`.
- `S` is finite, so one `s` does this for an `omega`-large set of `k`. Then
  `phi(s) != 1`, and `phi` is nontrivial.
- Here `phi` lands in the ultraproduct over the sizes `n_k` just chosen, which
  may differ from a previously fixed `S_omega`. Its image is a nontrivial
  countable subgroup of a metric ultraproduct of symmetric groups, hence sofic
  (I1). So (a) fails, and by (a) <=> (e) below, (e) fails for every choice of
  `S_omega`. In particular condition (e) does not depend on that choice.

## (a) <=> (e)

- A nontrivial `phi : Q -> S_omega` has a countable nontrivial image. By (I1)
  the image is sofic, so it is a nontrivial sofic quotient.
- Conversely, a nontrivial sofic quotient is countable. By (I1) it embeds in
  `S_omega`, which gives a nontrivial homomorphism.

## (b) => (c)

- **Strict stability.** Given `eps > 0`, put `delta_0 = h . eps`. If
  `delta(sigma) <= delta_0`, then by the rate the trivial action `rho`
  satisfies every relator and has `e(sigma(s) rho(s)^{-1}) <= eps` for every
  `s`.
- **No finite quotients.** Let `Q -> Phi` be onto with `Phi` finite and
  nontrivial.
  - The left regular action gives `sigma : S -> Sym(Phi)` with
    `delta(sigma) = 0`.
  - Some generator maps to a nontrivial element, which moves every point of
    `Phi`. So `supp(sigma) = 1`, and hence `h = 0`.

## (c) => (d)

Strict stability is flexible stability with `Y = X`.

## (d) => (b)

- Suppose `Q` is flexibly stable and has no finite quotients, but `h = 0`.
- Fix `eps < 1/|S|` and let `delta_0` be the flexible-stability constant for
  `eps`.
- Choose `sigma` on `X` with `supp(sigma) = 1` and `delta(sigma) <= delta_0`.
  Stability gives a finite `Y ⊇ X` and a genuine action `rho` of `Q` on `Y`
  with `|{x in X : sigma(s)x != rho(s)x}| <= eps|X|` for every `s`.
- The image of `rho` is a finite quotient of `Q`, so it is trivial, and
  `rho(s) = 1`.
- Then each `sigma(s)` moves at most `eps|X|` points. So
  `supp(sigma) <= |S| eps < 1`, a contradiction.

## Presentation independence

Condition (e) does not refer to the presentation, so positivity of `h` is a
group invariant. The value of `h` is not an invariant, and no comparison of
the values across presentations is claimed or needed.

## Lemma C: `Rad_sof(G) = Res(G)` for flexibly stable finitely presented `G`

**`Rad_sof(G) ⊆ Res(G)`.** Finite groups are sofic, so every kernel into a
finite group contains `Rad_sof(G)`.

**`Res(G) ⊆ Rad_sof(G)`.** Let `g` be outside `Rad_sof(G)`, and let `w` be a
word of length `l` representing it.

1. Some `phi : G -> S_omega` has `phi(g) != 1`. Lift `phi` to `sigma_k` on
   `X_k`. Then `lim_omega delta(sigma_k) = 0` and
   `lim_omega e(sigma_k(w)) = c > 0`.
2. Fix `eps` with `2 l eps + eps < c/2`. For `omega`-many `k`, flexible
   stability gives a finite `Y_k ⊇ X_k` and a genuine action `rho_k` on `Y_k`
   with the following bounds:
   - `|Y_k \ X_k| <= eps|X_k|`;
   - for each `s`, the set `B_s = {x in X_k : sigma_k(s)x != rho_k(s)x}` has
     `|B_s| <= eps|X_k|`.
3. **Inverse letters.** Suppose `x` is in `X_k`, `y = rho_k(s)^{-1}x` is in
   `X_k`, and `y` is not in `B_s`. Then `sigma_k(s)y = x`, so
   `sigma_k(s)^{-1}x = rho_k(s)^{-1}x`. So the bad set for `s^{-1}` lies in
   `rho_k(s)(B_s u (Y_k \ X_k))` and has size at most `2 eps|X_k|`.
4. **Words.** Apply the letters of `w` one at a time. If `sigma_k(w)x` and
   `rho_k(w)x` differ, then the common current point is bad for the next
   letter at some step. Both maps are injective, so the preimage of a bad set
   is no larger than the bad set. Hence

   ```text
   |{x in X_k : sigma_k(w)x != rho_k(w)x}| <= 2 l eps |X_k|.
   ```

5. So `rho_k(g)` moves at least `(c/2 - 2 l eps)|X_k| > 0` points of the finite
   `G`-set `Y_k`. Hence `g` survives in a finite quotient, and `g` is not in
   `Res(G)`.

**Glebsky--Rivera as a corollary.** If `G` is also sofic, then
`Rad_sof(G) = 1` by (I2). So `Res(G) = 1` and `G` is residually finite.

## Calibrations, checked

- **Free group, `R` empty.** `delta = 0` always, so `h = 0`. The free group
  has sofic quotients.
- **`<s | s^2>`.** A fixed-point-free involution has `supp = 1` and
  `delta = 0`, so `h = 0`, matching the sofic quotient `Z/2`.
- **`<s | s>`.** `delta(sigma) = e(sigma(s)) = supp(sigma) = 1`, so `h = 1`.
  The group is trivial, and hence vacuously sofically trivial.
- **Simple groups.** `Rad_sof` is normal, so it is `1` or `Q`. So a simple
  group is sofically trivial iff it is nonsofic.
