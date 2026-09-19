---
rg: 2
id: jacobson-el3-lef-from-local-mirror-lifts-proof
kind: route
title: Proof that partial mirror lifts give LEF and that spatial global mirror lifts violate the commuting-pair index
target: jacobson-el3-lef-from-local-mirror-lifts
requires:
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
  - jacobson-symbol-sequence-does-not-virtually-split
  - jacobson-symbol-sequence-does-not-split
  - cohn-elementary-group-is-not-lef
  - jacobson-el4-is-finitely-presented-steinberg-group
  - binary-jacobson-el2-is-lef
---

The notation is that of the target. Write `[X : Y] = dim X/(X∩Y) - dim Y/(X∩Y)` for commensurable subspaces.
This is additive: `[X:Z] = [X:Y] + [Y:Z]`. It is also additive over direct sums of pairs.

## (L1) Local criterion

1. Let `B ⊆ E` be finite with `1 in B`, and let `f` be a partial iota-lift on `B`.
2. Put `s(g) = (g, f(g))`. For `g in B` we have `pi_-(f(g)) = iota(pi(f(g))) = iota(iota(pi(g))) = pi(g)`, so
   `s(g) in P` by (MQ2).
3. `s(gh) = s(g)s(h)` for `g, h in B`. `s` is injective, because its first coordinate is the identity.
4. `P` is LEF (MQ2). So there are a finite group `F` and a map `t : s(B·B) -> F` that is injective and
   multiplicative on `s(B)`.
5. Then `t o s` is injective on `B·B` and multiplicative on `B`. `B` was arbitrary, so `E` is LEF.

## (L2) Rank four and up

1. **Global lifts.** If `f` is a global iota-lift, then `s : E -> P` is an injective homomorphism. Subgroups of LEF
   groups are LEF, so `E_n` would be LEF. For `n >= 4` that contradicts `cohn-elementary-group-is-not-lef`.
2. **A ball.** Let `E_4 = <X | R>` be a finite presentation (`jacobson-el4-is-finitely-presented-steinberg-group`),
   with every relator of length at most `m`. Let `B_4` be the ball of radius `m` in the word metric of `X ∪ X^(-1)`.
3. Suppose `f` is a partial iota-lift on `B_4`.
   - `f(1) = f(1)f(1)`, so `f(1) = 1`. Also `f(x^(-1)) = f(x)^(-1)` for `x in X`.
   - Define `F` on the free group by `x -> f(x)`.
   - For a relator `r = y_1 ... y_l`, every prefix lies in `B_4`. By induction along the prefixes,
     `F(y_1 ... y_j) = f(y_1 ... y_j)`. So `F(r) = f(1) = 1`.
   - Hence `F` induces a homomorphism `E_4 -> E_4`. On `X` its symbol is `iota o pi`, so it is a global
     iota-lift. That contradicts step 1.
4. **Rank three.** The argument of step 3 applies verbatim to `E_3` once `E_3` has a finite presentation. Step 1
   then applies, because `E_3` finitely presented and LEF would make it residually finite. It is not residually
   finite: every finite image kills the head `x_13(Q)` (`cohn-elementary-group-is-not-lef`, point 1).

## (L3) The commuting-pair index

Let `u = x_ij(a)` with `i != j`, `a != 0`, and let `g in SL_n(A)` commute with `u`. Let `u~`, `g~` be lifts.

1. **Commensurability.** `g~ u~ g~^(-1)` is a lift of `u`, so it equals `u~ l` with `l in L`. Hence
   `g~ W = (u~ l + 1)V`. That differs from `W = (u~+1)V` by the image of the finite-rank operator `u~(l-1)`, so
   the two are commensurable.
2. **Independence of lifts.** Replacing `u~` by `u~ l'` changes `W` commensurably, by step 1. Replacing `g~` by
   `g~ l''` changes `[g~W : W]` by `[g~ l'' W : g~ W] = [l''W : W]`. For a finitary `l''` that is `0`, because
   `l''` fixes a finite-codimension subspace of `W` pointwise. The class of `W` is `g~`-stable, so `[g~ X : X]` is
   the same for every `X` commensurable with `W`. So `I(u,g)` is well defined.
3. **The layer.** Take `u~ = x_ij(a~)` with `pi(a~) = a`. Then `W = a~ V_+`, placed in coordinate `i`. `a~` is
   Fredholm (nonzero symbol), so `W` is commensurable with `V_i`.
4. **Diagonal `g`.** Let `g = diag(z^(m_1), ..., z^(m_n))`. It commutes with `u` iff `m_i = m_j`. Then
   `I(u,g) = [g~V_i : V_i]`, and this equals the Fredholm index of the `(i,i)` entry of `g~`, whose symbol is
   `z^(m_i)`. So `I(u,g) = -m_i`. This is the relative-index step of
   `jacobson-symbol-sequence-does-not-virtually-split-proof`, which is stated there for `i = 1`. The same proof
   applies coordinatewise: the off-diagonal entries in column `i` have zero symbol, hence finite rank.
5. **Values.**
   - `I(x_12(a), h^k) = -k`.
   - `I(x_12(a), iota(h^k)) = +k`, since `iota(h^k) = diag(z^(-k), z^(-k), z^(2k), 1, ...)`.
   - `I(x_21(a), h^k) = -k`.
6. **Rank two.** In `SL_2(A)`, the centralizer of `x_12(a)` consists of the matrices `[[c,b],[0,c]]` with
   `c^2 = 1`. In characteristic two `(c+1)^2 = 0` in the domain `A`, so `c = 1` and `g = x_12(b)`. Its lift
   `x_12(b~)` fixes `V_1` pointwise, so `I = 0`.
   The index `I` is thus invisible at rank two, where the mirror lift `psi` exists.

## (L4) Global lifts, n >= 3

Let `f : E -> E` be a homomorphism with `pi o f = iota o pi`.

**(a) Injectivity.**
1. `f(L) ⊆ ker pi = L`. `L` is simple, so `f|_L` is trivial or injective.
2. Suppose `f|_L` is trivial. Then `f = s o pi` for a homomorphism `s : SL_n(A) -> E` with `pi o s = iota`, and
   `s o iota` is a section of the symbol sequence. That contradicts `jacobson-symbol-sequence-does-not-split`.
3. So `ker f ∩ L = 1`. Then `[ker f, L] ⊆ ker f ∩ L = 1`, so `ker f` centralizes `L = GL_fin(V)`.
4. An operator commuting with every transvection `1 + v (x) phi` maps each `v` into `F_2 v`, so it is the
   identity. Hence `ker f = 1`.

**(b) No spatial lift.** Assume (S), and write `X_1, ..., X_N` for the summands of the source of `Phi`. Each is a
copy of `V`, of `V^*`, or is `V_0`. Let `rho_p(l)` be the action of `l in L` on `X_p`: `l`, `l^(-t)`, or `1`.

1. **Module facts.**
   - `L` is transitive on the nonzero vectors of `V` and of `V^*`, so both are irreducible. Neither has nonzero
     `L`-fixed vectors.
   - `End_L(V) = End_L(V^*) = F_2`, by (a) step 4 and its dual.
   - `Hom_L(V, V^*) = 0`. A nonzero map `Psi` would be an isomorphism, and `b(x,y) = Psi(x)(y)` would be a
     nondegenerate `L`-invariant bilinear form. Fix `x != 0`. `Stab_L(x)` is transitive on `V` minus `F_2 x`, so
     `b(x,.)` is a constant `c` there. Take `y, y'` with `x, y, y'` independent: then `c = b(x, y+y') = 2c = 0`.
     So `b(x,.) = 0`, a contradiction. By duality `Hom_L(V^*, V) = 0` as well.
   - `Hom_L(V, 1) = Hom_L(1, V) = 0`, and the same holds for `V^*`.
2. **Block form.** Let `g in E` and `M = Phi^(-1) f(g) Phi`. From `f(g) f(l) f(g)^(-1) = f(g l g^(-1))`,
   ```text
   M_pq rho_q(l) = rho_p(g l g^(-1)) M_pq = gamma_p rho_p(l) gamma_p^(-1) M_pq,
   ```
   where `gamma_p` is `g`, `g^(-t)` or `1`. So `gamma_p^(-1) M_pq` lies in `Hom_L(X_q, X_p)`. By step 1,
   ```text
   M = (g (x) C_+(g)) (+) (g^(-t) (x) C_-(g)) (+) D(g),
   ```
   with `C_+- : E -> GL_(r_+-)(F_2)` and `D : E -> GL(V_0)` homomorphisms. Taking `g = l` and comparing with (S)
   gives `C_+-(l) = 1` and `D(l) = 1`.
3. **Choice of the pair.**
   - `E' = ker C_+ ∩ ker C_-` has finite index and contains `L`, so `E' = pi^(-1)(N)` with `N` of finite index in
     `SL_n(A)`.
   - `N ∩ {x_12(b)}` has finite index in the infinite group `(A,+)`, so it contains some `x_12(a)` with `a != 0`.
     Choose also `k >= 1` with `h^k in N`.
   - Let `u~ = x_12(a~)` and let `g~` be any lift of `h^k`. Both lie in `E'`.
4. **Index through `Phi`.** Put `W = (f(u~)+1)V` and compute `[f(g~)W : W]`. It is intrinsic, so compute it in
   the decomposition, where both operators are block diagonal.
   - Each `V`-copy contributes `I(x_12(a), h^k) = -k`.
   - Each `V^*`-copy carries `u~^(-t)` and `g~^(-t)`. Identify `V^*` with `V` by the dual basis. Then `x^(-t)`
     becomes `chi(x) = tau(x^(-1))^T`, the blockwise transpose. This lies in `E`, with symbol
     `beta(iota(pi x))`, where `beta` is transpose-inverse.
   - `beta iota(x_12(a)) = x_21(iota a)` and `beta iota(h^k) = h^k`. So each `V^*`-copy contributes
     `I(x_21(iota a), h^k) = -k`.
   - On `V_0`, `D` is trivial on `L`, so it factors through `SL_n(A)`. `u` and `h^k` commute there, so `D(g~)`
     maps `(D(u~)+1)V_0` exactly onto itself, and the contribution is `0`.
   - Total: `[f(g~)W : W] = -(r_+ + r_-)k`.
5. **Index through symbols.** `f(u~)` lifts `x_12(iota a)` and `f(g~)` lifts `iota(h^k)`, so the same number is
   `I(x_12(iota a), iota(h^k)) = +k` by (L3).
6. **Contradiction.** `-(r_+ + r_-)k = +k` with `k >= 1` and `r_+- >= 0`.

**Scope of (S).**
- If `f(g) = Y m(g) Y^(-1)`, where `m(g)` is a block sum of copies of `g` and `chi(g)` and `Y` is invertible, then
  (S) holds with `Phi = Y` composed with the dual-basis identifications.
- The rank-two `psi(g) = K chi(g) K^(-1)` is of this form with `(r_+, r_-) = (0, 1)`. There is no contradiction at
  rank two: by (L3) step 6 every admissible pair has `I = 0`, so both computations give `0`. The obstruction starts
  at rank three, with the pair `(x_12(a), h^k)`, where `h` has equal entries `z` in coordinates `1` and `2`.
- (S) fails for non-split finitary modules. For example, `M = V + F_2 w` inside `F_2^N` with `w` not finitely
  supported is a non-split extension of the trivial module by `V`. Lifts with such `V_f` are the survivor.
