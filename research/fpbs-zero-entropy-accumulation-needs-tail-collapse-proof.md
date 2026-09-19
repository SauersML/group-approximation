---
rg: 2
id: fpbs-zero-entropy-accumulation-needs-tail-collapse-proof
kind: route
title: Proof that at zero entropy tail-equivalent forward S-words with a common endpoint carry at most |Stab| past endpoints, that finite tail multiplicity gives (LF_mu) and death, that symbolic asymptotic pairs are invisible to the current, and that essential accumulation needs tail collapse with separated pasts
target: fpbs-zero-entropy-accumulation-needs-tail-collapse
requires:
  - fpbs-ray-code-deaths-depend-only-on-the-current
---

# Proof

Notation as in the claim. `[CUR]` is `fpbs-ray-code-deaths-depend-only-on-the-current` and its proof. `delta` is a
hyperbolicity constant of the Cayley graph.

## Step 0. The good set `X_1`

By `[CUR]` Proposition 4 (proof, Step 5), each past letter `a_{-k}` is `rho^#`-a.e. a Borel function of the forward
word `w`. So there is a Borel map `Psi'` from `S^N` to left-infinite words with `(a_{-k}(p))_{k>=1} = Psi'(w(p))` off
a null set `N_0`. Put `X_1 = X^# \ ∪_{n ∈ Z} (T^#)^n N_0`. This set is conull and `T^#`-invariant. On `X_1`:
- (0.a) the whole past word, and so the backward path `P_p(-t)`, is a function of `w(p)`;
- (0.b) `zeta^{-#}(p) = Psi(w(p))`, where `Psi` is the backward endpoint of the path spelled by `Psi'`;
- (0.c) `zeta^#(p) = zeta(w(p))`, the forward endpoint of the path spelled by `w(p)` from `1`. (UQ) makes it exist.

**Equivariance.** For `q ∈ X_1` and `m >= 0`, `w((T^#)^m q) = sigma^m w(q)` and `P_{(T^#)^m q}(t) =
P_q(m)^{-1} P_q(m+t)`. Hence `zeta((sigma^m w(q))) = P_q(m)^{-1} zeta(w(q))` and
`Psi(sigma^m w(q)) = P_q(m)^{-1} Psi(w(q))`. (E)

## Step 1. Theorem 1

Let `(h, w), (h', w') ∈ W_r(eta)` with `w ~ w'`, realised by `q, q' ∈ X_1`: `w = w(q)`, `w' = w(q')`, and
`sigma^m w = sigma^{m'} w' =: z`. Put `a = h P_q(m)` and `b = h' P_{q'}(m')`. The prefixes of `w` and `w'` spell
`P_q(m)` and `P_{q'}(m')`, so `a` and `b` depend only on `(h, w)` and `(h', w')`. By (E),
- `eta = h zeta(w) = a zeta(z)` and `eta = h' zeta(w') = b zeta(z)`, so `b^{-1} a ∈ Stab(zeta(z))`;
- `h Psi(w) = a Psi(z)` and `h' Psi(w') = b Psi(z)`.

Here `(T^#)^m q ∈ X_1` has forward word `z`, so `Psi(z)` and `zeta(z)` are defined.

Fix one word `z_0` of the class, realised in `X_1`. Every member `(h, w)` of the class has, for suitable `m, j`,
`sigma^m w = sigma^j z_0` (two words in one tail class have a common shift of each). Applying the computation with
`z = sigma^j z_0` and (E) for `z_0` gives `h Psi(w) = c Psi(z_0)` with `c zeta(z_0) = eta`. The set
`{c : c zeta(z_0) = eta}` is a coset `c_0 Stab(zeta(z_0))`, and `Stab(zeta(z_0)) = c_0^{-1} Stab(eta) c_0`.
So the class gives at most `|Stab(eta)|` backward endpoints.

**Finite stabilizers.** In a hyperbolic group an infinite subgroup fixing a boundary point contains a loxodromic
element. So a point with infinite stabilizer is a fixed point of one of countably many loxodromics. Since `nu` is
nonatomic and quasi-invariant, these points form a `nu`-null set. ∎

## Step 2. Corollary 1'

**2.1 Localisation.** Let `(theta, eta)` be in the support of `mu_R`, carried by a line `g P_p` with `p ∈ X_1`. This
costs nothing: by `[CUR]` Step 1, `mu_R` is the image of `(rho^# x count)|_D`, and `X_1` is conull.
- If `theta ∈ K_r(eta)`, i.e. `(theta|eta)_o <= r`, a geodesic from `theta` to `eta` passes within `r + 2 delta`
  of `o`.
- By the Morse lemma the `(lambda, c)`-quasi-geodesic line `g P_p` stays within `M = M(lambda, c, delta)` of it.
- So some refined time `m` has `h := g P_p(m) ∈ B(1, D)`, with `D = r + 2 delta + M + 1`.
- With `q = (T^#)^m p ∈ X_1` and (E), `(theta, eta) = (h Psi(w(q)), h zeta(w(q)))`. So `(h, w(q)) ∈ W_D(eta)`.

**2.2 Counting.** Hence, for `nu`-a.e. `eta`, the conditional `mu^eta` restricted to `K_r(eta)` is carried by
`{h Psi(w) : (h, w) ∈ W_D(eta)}`. This uses the disintegration in `[CUR]` Step 1: the conditionals of a measure
carried by a set are carried by its sections a.e. By Theorem 1 and (FTM) this set has at most
`tau_D(eta) |Stab(eta)| < infinity` points for `nu`-a.e. `eta`. So `mu^eta|_{K_r(eta)}` is purely atomic with
finitely many atoms, for every rational `r`. As `K_r` increases in `r`, this holds for every `r`. This is (LF_mu).

`[CUR]` Theorem 1 applies. Its other hypotheses are part of the claim's setting: (UQ), a finite invariant `rho^#`,
and a nonatomic backward class `nu^-`. It gives total dissipativity and the failure of PDR. ∎

**2.3 Countable tail classes.** A class is `{u sigma^j z_0 : u a finite S-word, j >= 0}`, a countable set.

## Step 3. Theorem 2

Let `p ∈ X_1` with forward word `w`, and let `x` be a left extension of `w` in the subshift (so `x w` is an allowed
bi-infinite word). The forward word of the extended line is still `w`. So all left extensions, and all
right-asymptotic partners after the time where they agree, lie in the tail class of `w`. Theorem 1 then gives at most
`|Stab(eta)|` backward endpoints.

Moreover, by (0.a), among positions of `X_1` with forward word `w` the past word is `Psi'(w)`, a single one. The
other left extensions are realised only on `X^# \ X_1`, a `rho^#`-null set, so they are not charged by `mu_R`.
This holds for any zero-entropy subshift, Toeplitz or not, and any (UQ) spelling. ∎

## Step 4. Theorem 3

**Essential accumulation.** By definition in `[CUR]`, essential accumulation is the failure of (LF_mu) on a
`nu`-positive set.

**Infinitely many classes and separated pasts.** By Step 2.2, for `nu`-a.e. `eta` the atoms of `mu^eta|_{K_r}` lie in
`{h Psi(w) : (h, w) ∈ W_D(eta)}`. Grouping these by tail class, each class contributes at most `|Stab(eta)|` points
(Theorem 1). So failure of (LF_mu) at `eta` (a nonatomic part, or infinitely many atoms in some `K_r`) needs
infinitely many tail classes whose representatives' pasts take infinitely many values in `K_r(eta)`.

**Fellow-travelling.** Any two of the corresponding lines are `(lambda, c)`-quasi-geodesic rays from `B(1, D)` to
`eta`. By the Morse lemma and thinness of ideal triangles they are eventually within `D' = D'(lambda, c, delta, D)`
of each other. ∎

## Remark 4 (why respelling cannot separate pasts)

Respelling (`[BLF]` Theorem 3, where `[BLF]` is `fpbs-backward-locally-finite-ray-codes-die`) changes the `S`-word
inside each letter while keeping the letter-boundary path, and hence the letter sequence of the base code. Positions
with a common letter future have a common letter past, since the base code has zero entropy and the letter past is a
function of the letter future. So they have a common backward endpoint, although their `S`-words can be
tail-inequivalent. In general: if the map `w -> Psi(w)` factors through a coarser word
(letters, or any code with finitely many tail classes per endpoint), the pasts do not separate.

So a tail-collapsing survivor needs coarse futures that are tail-inequivalent at every coarsening and still
fellow-travel. On a free group with a free basis and geodesic paths this is impossible: geodesic rays to one point
agree after a shift. So the mechanism needs relators, for example independent choices of the two sides of relator
cells along the ray, arranged so that the past depends on those choices.
