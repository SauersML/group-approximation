---
rg: 2
id: higman-virtually-solvable-edge-images-collapse-proof
kind: route
title: The top tower invariant is a non-inner Fox derivation on every derived term of the free group, so condition (ii) of the tower chain holds for every k and every virtually solvable edge image collapses
target: higman-virtually-solvable-edge-images-collapse
requires:
  - higman-bounded-derived-length-edge-images-collapse
  - virtually-metabelian-edge-images-collapse-higman-quotients
  - nilpotent-edge-images-collapse-higman-quotients
artifacts:
  - experiments/higman-magnus-nonvanishing-2026-09-18/witness.py
  - experiments/higman-magnus-nonvanishing-2026-09-18/witness-output.txt
---

Conventions: `x^y = y^-1 x y`, `[x,y] = x^-1 y^-1 x y`. We use the notation of
`higman-bounded-derived-length-tower-chain-proof` (the route of
`higman-bounded-derived-length-edge-images-collapse`): `Phi` is free on `alpha, gamma`; the flavours
`b`, `d`; kinds, heights, types `tau_r`, prefix sums `Pi_r` and invariants `S_r`; its Lemmas A, B, C
and its Proposition (Step 5), which says:

> for `k >= 3` and `m >= 1`, `T(k-1)` together with **(ii)** — some `w_0 in Phi^(k) ∩ P_(>=0)` has
> `S^d_(k-2)(iota_b(w_0)) != 0` at `P = 2^m` — gives `T(k)`.

That route proves (ii) only for `k <= 11`, by computer. Here we prove (ii) for **every** `k` and every
`m`, by hand. The whole argument below (Steps 1–5) is about the free group `Phi` alone.

Throughout Steps 1–5 we fix one flavour. It is convenient to put `S_(-1)(u)` = the exponent sum of the
kind-1 letters of `u`, times the symbol `[*]`; then the level-0 type of a kind-0 letter (its height) is
`Pi_(-1)` read as an integer, and the recursion `tau_r = (tau_(r-2), Pi_(r-1))` holds for all `r >= 0`
with `tau_(-2)` empty. Write `triv_(-1) = *`, `triv_0 = 0` (height 0), `triv_j = (triv_(j-2), 0)`.

## Step 1 (concatenation)

For a word `p` define a map `Theta_p` on types, level by level:

```text
Theta_p(*) = *,     Theta_p(h) = h + S_(-1)(p)       (heights),
Theta_p((tau, Pi)) = ( Theta_p(tau), S_(j-1)(p) + (Theta_p)_*(Pi) )     (level j >= 1),
```

where `(Theta_p)_*` pushes a formal sum forward. `Theta_p` is injective on each level (induction: it is
built from a translation and injective push-forwards).

**Lemma 1.** For words `p, q`, every letter `x` of `q` has, in `pq`, the type `Theta_p(tau^q(x))` at each
level. Hence `S_j(pq) = S_j(p) + (Theta_p)_* S_j(q)` for all `j >= -1`.

*Proof.* Induction on the level. The height of a kind-0 letter of `q` in `pq` is the kind-1 exponent sum
of `p` plus its height in `q`. At level `j >= 1`, `Pi_(j-1)(x)` in `pq` is the sum over all kind-`(j-1)`
letters of `p`, which is `S_(j-1)(p)`, plus the sum over the earlier letters of `q`, whose types in `pq`
are `Theta_p` of their types in `q` by induction. ∎

## Step 2 (the filtration and the derivation)

Let `N_r = { u in Phi : S_j(u) = 0 for all -1 <= j <= r-2 }` (so `N_0 = N_(-1) = Phi`).

For `u in N_r`, `Theta_u` is the identity on levels `<= r-1`, and on level `r` it is the translation
`(tau, Pi) -> (tau, Pi + S_(r-1)(u))` (read off the definition: every `S_j(u)` entering levels `<= r-1`
vanishes). So Lemma 1 gives, for `u in N_r` and any word `v`,

```text
S_j(uv) = S_j(u) + S_j(v)                  (j <= r-1),
S_r(uv) = S_r(u) + t^(S_(r-1)(u)) S_r(v),                                          (1)
```

where `t^c` translates the `Pi`-component of a level-`r` type by `c`.

- **`N_r` is a subgroup,** and `S_(r-1)` is a homomorphism on it: by (1) with `j <= r-2`, and
  `S_j(u^-1) = -S_j(u)` from `S_j(u u^-1) = 0`.
- **`N_(r+1) = ker(S_(r-1)|N_r) ⊇ [N_r, N_r]`,** since `S_(r-1)` takes values in an abelian group.
- **Hence `Phi^(r) <= N_r` for all `r >= 1`:** `Phi' <= N_1` (kind-1 exponent sum), and
  `Phi^(r+1) = [Phi^(r), Phi^(r)] <= [N_r, N_r] <= N_(r+1)`.

**Module structure.** Let `A_(r-1)` be the free abelian group on the level-`(r-1)` types; it contains every
`Pi_(r-1)` and every `S_(r-1)(u)`. A level-`r` type is a pair `(tau, Pi)` with `tau` a level-`(r-2)` type and
`Pi in A_(r-1)`. So the free abelian group `M_r` on level-`r` types is the **free `Z[A_(r-1)]`-module with
basis the level-`(r-2)` types**, with `[(tau, Pi)] = t^Pi [tau]`. `Z[A_(r-1)]` is a Laurent polynomial ring
over `Z` in the variables `t_y` (`y` a level-`(r-1)` type); it is a domain with fraction field
`K_(r-1) = Q(t_y)`.

Put `pi = S_(r-1)` and `delta = S_r` on `N_r`. By (1), `pi : N_r -> A_(r-1)` is a homomorphism and
`delta : N_r -> M_r` is a **derivation** over it: `delta(uv) = delta(u) + t^(pi(u)) delta(v)`. (This is
the Fox/Magnus shape the previous route anticipated.)

## Step 3 (commutators)

For `u, v in N_r` with `a = pi(u)`, `b = pi(v)`, `X = delta(u)`, `Y = delta(v)`: from (1),
`delta(u^-1) = -t^(-a) X`, and expanding `u^-1 v^-1 u v`,

```text
delta([u, v]) = -t^(-a) X - t^(-a-b) Y + t^(-a-b) X + t^(-b) Y
              = t^(-a-b) [ (1 - t^b) X - (1 - t^a) Y ].                            (2)
```

So `delta([u,v]) = 0` iff `(1 - t^b) X = (1 - t^a) Y` in `M_r`.

## Step 4 (conjugating by a power of one letter)

Fix `r >= 1`, let `x` be the letter (`alpha` or `gamma`) of **kind `kappa = r mod 2`**, let `n >= 1`,
`p = x^n`, and let `u in Phi^(r)` with `a = pi(u)`, `X = delta(u)`. Put `v = p u p^-1`. Then
`v in Phi^(r) <= N_r`, since `Phi^(r)` is normal in `Phi`. We compute `S_j(v)` from Lemma 1 as
`S_j(p) + Theta_p*(S_j(u)) + Theta_(pu)*(S_j(p^-1))`.

- **The prefix.** No letter of `x^n` has a letter of the other kind before it, so every letter of `p` has
  type `triv_j` at each level `j ≡ kappa`. Hence `S_j(p) = n [triv_j]` for `j ≡ kappa (mod 2)` and
  `S_j(p) = 0` otherwise; likewise `S_j(p^-1) = -n [triv_j]` or `0`.
- **`Theta = Theta_p`.** Since `S_(r-1)(p) = S_(r-3)(p) = ... = 0` (wrong parity), `Theta` fixes `triv_(r-2)`
  (induction down to `*`, or to height `0` when `kappa = 0`, where `S_(-1)(p) = 0`), and on level `r` it
  is `(tau, Pi) -> (Theta tau, theta(Pi))`, where `theta = Theta_*` on `A_(r-1)`. So `Theta_*` is
  `theta`-**semilinear** on `M_r`: `Theta_*(f m) = theta(f) Theta_*(m)`, where `theta` is the ring
  endomorphism of `Z[A_(r-1)]` with `theta(t_y) = t_(Theta y)`. It is injective, because `Theta` is
  injective on level-`(r-1)` types.
- **The suffix.** In `v = (pu) p^-1` the letters of `p^-1` get the types `e_j = Theta_(pu)(triv_j)`
  (`j ≡ kappa`). By the definition, `e_j = (e_(j-2), S_(j-1)(pu))`, and
  `S_(j-1)(pu) = S_(j-1)(p) + Theta_* S_(j-1)(u) = Theta_* S_(j-1)(u)` (parity). For `j <= r-1` this is 0
  since `u in N_r`, and the base is `e_(-1) = *` or `e_0 = S_(-1)(p) + S_(-1)(u) = 0`. So
  `e_(r-2) = triv_(r-2)` and `e_r = (triv_(r-2), theta(a))`.
- **Result.** By Lemma 1, with `E = [triv_(r-2)]` (so `[triv_r] = E` and `[e_r] = t^(theta(a)) E`):

```text
pi(v)    = theta(a),
delta(v) = n E + Theta_*(X) - n t^(theta(a)) E  =  Theta_*(X) + n (1 - t^(theta(a))) E.      (3)
```

(At level `r-1` the prefix and suffix contribute nothing, by parity.)

## Step 5 (the field lemma and the nonvanishing theorem)

**Lemma 2.** Let `K = Q(t_y : y in Y)` be a rational function field, `Theta : Y -> Y` injective, and `theta`
the field endomorphism with `theta(t_y) = t_(Theta y)`. Then `z - theta(z) = c` has no solution
`z in K` for any rational `c != 0`.

*Proof.* Let `supp(z) = { y : dz/dt_y != 0 }`; it is finite, and `z in Q(t_y : y in supp z)`, since in
characteristic 0 a rational function with vanishing partial derivative in a variable does not involve it.
By the chain rule, `d(theta z)/dt_(Theta y) = theta(dz/dt_y)` and `d(theta z)/dt_w = 0` for `w` not in
`Theta(Y)`. As `theta` is injective, `supp(theta z) = Theta(supp z)`. Now `theta z = z - c` has the same
support as `z`, so `Theta` maps the finite set `supp z` injectively into itself, hence permutes it, and
`Theta^L` is the identity on it for some `L >= 1`. So `theta^L(z) = z`. Iterating
`z = theta(z) + c` gives `z = theta^L(z) + L c = z + L c`, so `L c = 0`, a contradiction. ∎

**Theorem (nonvanishing).** In either flavour, for every `r >= 1`, `S_(r-1)` is not identically zero on
`Phi^(r)`. Explicitly, with `x_r` the letter of kind `r mod 2` and any `n >= 1`,

```text
w_1 = [gamma, alpha]  (flavour b)  or  [alpha, gamma]  (flavour d),
w_(r+1) = [ w_r, x_r^n w_r x_r^-n ],
```

`w_r in Phi^(r)` and `S_(r-1)(w_r) != 0`.

*Proof.* Induction on `r`. In flavour `b`, `S_0([gamma, alpha]) = [-1] - [0] != 0` (the letter `gamma^-1`
is at `alpha`-height 0, then `gamma` at height `-1`); flavour `d` is the mirror.

Step: let `u = w_r in Phi^(r)` with `a = pi(u) = S_(r-1)(u) != 0`, `X = delta(u) = S_r(u)`, and
`v = x_r^n u x_r^-n`. Suppose `delta([u, v]) = 0`. By (2) and (3),

```text
(1 - t^(theta a)) X = (1 - t^a) ( Theta_*(X) + n (1 - t^(theta a)) E ).
```

Since `a != 0` and `theta` is injective, `1 - t^a` and `1 - t^(theta a)` are nonzero in the domain
`Z[A_(r-1)]`. Pass to `V = M_r ⊗ K_(r-1)`, the `K_(r-1)`-vector space with basis the level-`(r-2)` types,
and extend `Theta_*` semilinearly: `Theta_*(sum z_tau [tau]) = sum theta(z_tau) [Theta tau]`. Dividing by
`(1 - t^a)(1 - t^(theta a))` and putting `Z = X / (1 - t^a)`, so that
`Theta_*(Z) = Theta_*(X) / (1 - t^(theta a))`:

```text
Z = Theta_*(Z) + n E.
```

Compare the coefficients of `E = [triv_(r-2)]`: `Theta` is injective on level-`(r-2)` types and fixes
`triv_(r-2)`, so the only `tau` with `Theta tau = triv_(r-2)` is `triv_(r-2)` itself. Hence
`z_E = theta(z_E) + n` with `n >= 1`, contradicting Lemma 2. So `S_r(w_(r+1)) = delta([u,v]) != 0`, and
`w_(r+1) in [Phi^(r), Phi^(r)] = Phi^(r+1)`. ∎

**What the theorem says.** Step 2 gives `S_j = 0` on `Phi^(r)` for `j <= r-2`; the theorem says the next
level is never identically zero there. So the zero pattern forced by descent is exactly sharp at every
level, which is what the computer runs of the previous route saw for `k <= 11`. (Equivalently: the
derivation `S_r` on `Phi^(r)` is not "inner over the fraction field", i.e. not of the form
`u -> (1 - t^(pi u)) Z`, since that form is exactly what vanishing on `[Phi^(r), Phi^(r)]` forces.)

**Check.** `witness.py` computes the exact (unhashed) towers of `w_r` in flavour `b` for `n = 1, 2, 3`
and confirms the pattern `S_0 = ... = S_(r-2) = 0 != S_(r-1)` for all computed `r`; output in
`witness-output.txt`. This is only a consistency check; the proof above covers all `r`.

## Step 6 (condition (ii) for every `k` and every `m`)

**Proposition.** For every `k >= 2` and every `m >= 1` there is `w_0 in Phi^(k) ∩ P_(>=0)` with
`S^d_(k-2)(iota_b(w_0)) != 0` at `P = 2^m`.

*Proof.* Take the flavour-`b` witness `w = w_k` of Step 5: `w in Phi^(k)` and `S^b_(k-1)(w) != 0`. Put
`w_0 = alpha^n w alpha^-n` with `n >= 0` chosen as follows.

- **Lemma C (mirror, for `S^b` and `alpha^n`)** of the tower-chain route: `S^b_(k-1)(w_0) = 0` for at most
  one `n >= 0`. Avoid it.
- **Heights.** Every `gamma`-letter of `w_0` has `alpha`-height `>= n - c`, where `c` is the depth of the most
  negative `alpha`-height in `w`, and `|w_0| = |w| + 2n`. Since `N_(n-c) = 2^(P^(n-c))` grows doubly
  exponentially in `n`, we can take `n` so large that `N_(h_*) > 2|w_0|` with `h_* = n - c >= 0`.
- **Membership.** `w_0 in Phi^(k)` (a normal subgroup). Its `alpha`-exponent sum is 0 (it lies in `Phi'`)
  and its `gamma`-letters are at `alpha`-heights `>= 0`, so `w_0 in P_(>=0)` (Step 4 of the tower-chain
  route, i.e. Lemma 1 of the `k = 3` proof).
- **Lemma A and the Corollary of Lemma B (mirror, `iota_b` from flavour `b` to flavour `d`)**, with
  `v = w_0` and `r = k-2`: their hypotheses are exactly the two items above, and they give
  `S^d_(k-2)(iota_b(w_0)) = sigma_*(S^b_(k-1)(w_0)) != 0`. ∎

For `k = 2, 3` this is consistent with the earlier hand proofs; for `k <= 11` it replaces the hashed
computer certificate of the previous route by a proof, and for `k >= 12` it is new.

## Step 7 (the theorem)

**`T(k)` for every `k >= 2`.** `T(2)` is item 1 of `virtually-metabelian-edge-images-collapse-higman-quotients`.
For `k >= 3`, the Proposition of Step 5 of the tower-chain route, with `T(k-1)` and Step 6 here, gives
`T(k)`. By induction, `T(k)` holds for all `k`: for every quotient `Q` of `H4`, every `m >= 1` and every
`k`, if `<a^m, c^m>` is solvable in `Q` then `Q = 1`. The pair `<b^m, d^m>` follows by the automorphism
`a -> b -> c -> d -> a`.

**Normal closures.** Taking `m = 1` and `Q = H4 / ncl(F^(k))` gives `ncl_(H4)(F^(k)) = H4` for every `k`,
where `F = <a,c>`. Equivalently, `H4` has no nontrivial quotient in which the image of `<a,c>` (or
`<b,d>`) is solvable.

**Virtually solvable edge images.** If the image of `<a,c>` in `Q` has a finite-index solvable subgroup,
its normal core `A_0` (inside that image) has some finite index `m` and is solvable, of derived length
`k` say. Then `x^m in A_0` for every `x` in the image, so `<a^m, c^m> <= A_0` is solvable and `T(k)` gives
`Q = 1`. The same for `<b,d>`.

**Trees.** By the tree gate (item 2 of `nilpotent-edge-images-collapse-higman-quotients`), if `Q` acts on
a tree without inversions and fixes no vertex, some edge is fixed by `a` and `c`, or by `b` and `d`. If
every edge stabilizer is virtually solvable, that pair generates a virtually solvable subgroup, so
`Q = 1`. Hence a nontrivial quotient of `H4` never splits as an amalgam or HNN extension over virtually
solvable subgroups (no bound on the derived length, and none on the rank).

## Step 8 (calibration and scope)

- **Free group.** Steps 1–5 are statements about `Phi` only, and they are true there: `S_j` vanishes on
  `Phi^(r)` for `j <= r-2` (Step 2), and the witnesses show the next level does not. Nothing forces `Phi`
  itself to be solvable; the collapse comes only from the Higman relations through Lemmas A–C.
- **Where the old approach stopped.** The computer route needed, for each `k`, a word whose top invariant
  survives `iota_b`. Lemma B already moves nonvanishing across `iota_b` once the heights are large, and
  Lemma C lets one shift the heights. So the only real question was the free-group statement "`S_(k-1)`
  is not identically zero on `Phi^(k)`", which Step 5 proves by showing that a derivation vanishing on
  `[G, G]` must be fraction-inner, and that conjugation by `x^n` makes fraction-innerness impossible.
- **What remains for soficity.** Every amenable edge image in the glued constructions of
  `higman-group-is-sofic` must now be amenable but **not virtually solvable**, such as a locally solvable group
  of unbounded derived length, or a
  non-elementary amenable group. Virtually solvable edge groups are excluded outright.
