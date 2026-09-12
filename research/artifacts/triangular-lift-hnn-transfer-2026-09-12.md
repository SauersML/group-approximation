# HNN transfer: finite-subgroup idempotent right ideals admit no proper group shift

Lane `w4-kap-triangular`, 2026-09-12. Supports `finite-subgroup-idempotent-ideals-admit-no-proper-group-shift` and
`finite-support-triangular-two-piece-s0-lifts-do-not-exist`. Bears on `two-piece-s0-lift-with-triangular-defect-exists`
and `left-invertible-lift-of-s0-in-leavitt-group-algebra`. [TP] is
`research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md`.

## 0. The triangular condition is a shift of a right ideal

Let `G` be a group, `k` a field, and `A_n = M_n(k[G])`, with group elements acting as scalar matrices. For an
idempotent `e` of `A_n` and `g` in `G`:

    (I - e)[g]e = 0   <=>   [g] e A_n ⊆ e A_n   <=>   f A_n ⊆ e A_n,   where f = [g] e [g^(-1)].

*Proof.* `[g]eA_n ⊆ eA_n` holds exactly when `[g]e` lies in `eA_n`, that is when `e[g]e = [g]e`. Since `[g^(-1)]` is
a unit, `[g]eA_n = [g]e[g^(-1)]A_n`. QED

In [TP] Data 2.0:
- `X = E^[h]E1^ = 0` says `[h] E1^ A ⊆ E1^ A` (take `e = E1^`, `g = h`);
- `Y = E1^[h^(-1)]E^ = 0` says `[h^(-1)] E^ A ⊆ E^ A` (take `e = E^`, `g = h^(-1)`).

## 1. Theorem A (HNN transfer)

**Data.**
- `K <= G` is any subgroup and `g` is in `G`.
- `D = K ∩ gKg^(-1)` and `D' = g^(-1) D g = K ∩ g^(-1)Kg`, with `psi : D' -> D`, `psi(d') = g d' g^(-1)`.
- `H = < K, t | t d' t^(-1) = psi(d') for d' in D' >` is the HNN extension.
- `phi : H -> G` is the inclusion on `K` and sends `t` to `g`.

**Theorem A.** Let `e` in `M_n(k[K])` be an idempotent with `(I - e)[g]e = 0` in `M_n(k[G])`. If `M_n(k[H])` is
directly finite, then `e f = f` and `f e = e` for `f = [g]e[g^(-1)]`. So `[g] e M_n(k[G]) = e M_n(k[G])`.

*Proof.*
- **Step 1 (one double coset).** Let `Gamma` contain `K`, and let `gamma` in `Gamma` satisfy
  `K ∩ gamma K gamma^(-1) = D` and `gamma^(-1) d gamma = psi^(-1)(d)` for `d` in `D`. Then
  `mu_gamma : k[K] ⊗_(k[D]) k[K] -> k[Gamma]`, `x ⊗ y |-> x[gamma]y`, is well defined and injective. Here `D` acts
  on the second factor by `d . y = [psi^(-1)(d)] y`.
  - Well defined: `x[d][gamma]y = x[gamma][gamma^(-1) d gamma]y`.
  - Injective: `D` acts freely on `K x K` by `(k1, k2) . d = (k1 d, psi^(-1)(d^(-1)) k2)`, so the tensor product has
    the orbits as a basis. `mu_gamma` sends the orbit of `(k1, k2)` to `k1 gamma k2`. If `k1 gamma k2 = k1' gamma k2'`
    then `k1^(-1) k1' = gamma k2 k2'^(-1) gamma^(-1)` lies in `K ∩ gamma K gamma^(-1) = D`, so the two pairs share an
    orbit.
  - Entrywise, the same holds for matrices. This is [TP] Lemma 3.1; its proof never uses finiteness of the subgroup.
- **Step 2 (both groups qualify).**
  - In `G`, `gamma = g` qualifies by the definition of `D` and `psi`.
  - In `H`, `gamma = t` qualifies. The relations give `t^(-1) d t = psi^(-1)(d)`. If `t k t^(-1)` lies in `K`, the
    word `t k t^(-1) k'^(-1)` equals `1` and so is not reduced; by Britton's lemma `k` lies in `D'`. Hence
    `K ∩ tKt^(-1) = psi(D') = D`.
- **Step 3 (transfer).** `phi o mu_t = mu_g` on the common domain.
  - `X_G := (I - e)[g]e = mu_g((I - e) ⊗ e)` and `X_H := (I - e)[t]e = mu_t((I - e) ⊗ e)`.
  - `mu_g` is injective, so `X_G = 0` forces `(I - e) ⊗ e = 0`, hence `X_H = 0`.
- **Step 4 (direct finiteness in `H`).** Let `B = M_n(k[H])`, `x = [t]e + (I - e)` and `y = e[t^(-1)] + (I - e)`.
  - Because `(I - e)[t]e = 0`, `yx = I + N` with `N = e[t^(-1)](I - e)` and `N^2 = 0`. So `(I - N) y` is a left
    inverse of `x`.
  - `B` is directly finite, so `x` is invertible and `xB = B`.
  - `xe = [t]e` and `x(I - e) = I - e`, so `B = xB = [t]eB + (I - e)B = fB + (I - e)B`, with `f = [t]e[t^(-1)]`.
  - `X_H = 0` means `[t]e = e[t]e`, so `fB ⊆ eB`. Since `eB ∩ (I - e)B = 0`, both sums are direct:
    `B = fB (+) (I - e)B = eB (+) (I - e)B`.
  - By the modular law, `eB = eB ∩ (fB (+) (I - e)B) = fB (+) (eB ∩ (I - e)B) = fB`. So `ef = f` and `fe = e` in `B`.
- **Step 5 (push forward).** `phi` induces a ring map `B -> M_n(k[G])` that fixes `e` and sends `f` to
  `[g]e[g^(-1)]`. QED

**Remark 1.1 (why a group element).** Step 1 needs `[g]` to be a single group element. For a unit `w` of `k[G]`, the
product `(I - e) w e` spreads over many double cosets, and no transfer is available. This is the one place where
idempotents supported on finite subgroups re-enter: conjugating `E^` by a unit `u` turns `h` into the unit
`u^(-1) h u`.

## 2. Corollary B: finite supports, unconditionally

**Corollary B.** If `K` is finite, `M_n(k[H])` is directly finite for every `n` and every field `k`. So for any group
`G`, finite `F <= G`, idempotent `e` in `M_n(k[F])` and `g` in `G`:

    [g] e M_n(k[G]) ⊆ e M_n(k[G])   implies   [g] e M_n(k[G]) = e M_n(k[G]).

A finite-subgroup idempotent right ideal is never properly shifted by a group element.

*Proof that `M_n(k[H])` is directly finite.*
- **A finite quotient injective on `K`.** Let `Omega = K`, with `K` acting by left multiplication. As `D'`-sets,
  `Omega` with `d' . w = d' w` and `Omega` with `d' . w = psi(d') w` are both free with `|K|/|D'|` orbits, since
  `|D| = |D'|`. So there is a bijection `sigma` of `Omega` with `sigma(d' w) = psi(d') sigma(w)`. Sending `k` to left
  multiplication and `t` to `sigma` defines `rho : H -> Sym(Omega)`, injective on `K`.
- **A free normal subgroup of finite index.** `N = ker rho` has finite index and meets every conjugate of `K`
  trivially. The vertex stabilizers of the Bass–Serre tree of `H` are the conjugates of `K`, so `N` acts freely and
  without inversions on the tree. So `N` is free (Serre, *Trees*, I.3).
- **An embedding into matrices over a division ring.**
  - `k[H]^n` is a free right `k[N]`-module of rank `nm`, where `m = [H : N]`. Left multiplication embeds `M_n(k[H])`
    into `M_(nm)(k[N])`.
  - Free groups are bi-orderable, so `k[N]` embeds in the Malcev–Neumann division ring `Delta`.
  - `M_(nm)(Delta)` is directly finite, by dimension over `Delta`, and subrings of directly finite rings are directly
    finite. QED

The alternative route: `H` is residually finite, hence sofic, and Elek–Szabó applies. The argument above needs neither.

## 3. Corollary C: no triangular two-piece lift on a finite subgroup

**Corollary C.** In [TP] Data 2.0 over `A = F_2[R^x]`, suppose `E^` is supported on a finite subgroup `F` of `R^x`.
Then for every choice of `g1, g2` (so for every `h`), `X != 0` and `Y != 0`.

*Proof.* [TP] Remark 2.5 gives `pi(h) P_1 pi(h)^(-1) = q` with `q <= P_1` and `q != P_1`.
- **`X = 0` is impossible.**
  - By Section 0 and Corollary B, `f = [h]E1^[h^(-1)]` satisfies `f E1^ = E1^`.
  - Applying `pi` gives `q P_1 = P_1`. But `q P_1 = q`, since `q <= P_1`, so `q = P_1`. Contradiction.
- **`Y = 0` is impossible.**
  - By Corollary B with `g = h^(-1)`, `f' = [h^(-1)]E^[h]` satisfies `f' E^ = E^`.
  - `pi(h)^(-1) q pi(h) = P_1`, so `pi(f') = pi(h)^(-1) P_0 pi(h) <= pi(h)^(-1)(1 - q) pi(h) = P_0`.
  - `pi(f') != P_0`, because `P_0 = 1 - q` would force `q = P_1`.
  - Applying `pi` to `f' E^ = E^` gives `pi(f') P_0 = P_0`, while `pi(f') P_0 = pi(f')`. Contradiction. QED

**Consequences.**
- **Every finite candidate dies at once.** This covers [TP] Proposition 3.6 (the swap group), with its four-case split
  replaced by one argument. It also covers:
  - the depth-`k` constants `GL_(2^k)(F_2)` of [TP] Remark 1.3, including `GL_4(F_2)`;
  - dyadic permutation constants, Klein constants and odd cyclic constants;
  - every finite subgroup, whatever its intersection with its `h`-conjugate.
- **Rigidity for general supports.** Let `K = <supp E^>` and `D = K ∩ hKh^(-1)`. By Theorem A, a triangular witness
  makes `k[HNN_psi(K)]` not directly finite, where `psi` is conjugation by `h`. This sits beside [TP] Lemma 3.3,
  which says `<K, h>` is not sofic.
- **What survives.**
  - idempotents `E^` whose support generates an infinite subgroup with a non-directly-finite HNN extension;
  - finite-subgroup idempotents conjugated by units of `A`, where `h` becomes a unit (Remark 1.1);
  - the non-triangular unit criterion of [TP] Theorem 2.2, where `X != 0` and `Y != 0`;
  - multi-piece triangular lifts (Section 4).
