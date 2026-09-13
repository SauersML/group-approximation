# Ornstein isomorphisms for shifts co-induced from finite subgroups

Date: 2026-09-12. Lane `ex-bernoulli-negative`. Handwritten proofs, no computation. Unreviewed.

**Source.** B. Seward, *Bernoulli shifts with bases of equal entropy are isomorphic*, arXiv:1805.08279v1,
read from the PDF text on MSI (`review-lit/entropy/1805.08279.txt`) on 2026-09-12. Section 3 (proof of
Theorem 3.2) is transcribed below for co-induced actions. Seward's references used there:
- [17, 18] Ornstein: Bernoulli shifts over `Z` with equal finite, resp. infinite, entropy are isomorphic.
- [6, Lem. 3.25] Jackson–Kechris–Louveau: an aperiodic countable Borel equivalence relation has an
  aperiodic element in its full group.

Nothing here decides soficity. Part 2 (`bernoulli-negative-induced-absorption-2026-09-12.md`) applies it.

## 1. Co-induced actions

Let `G` be a countable group and `F <= G` finite. An **F-space** is a standard probability space
`(Y, nu)` with a measure-preserving action of `F`. Put

    Coind(Y) = { x: G -> Y : x(tf) = f^-1 . x(t) for all t in G, f in F },   (g.x)(t) = x(g^-1 t).

For a left transversal `R` of `G/F`, `x ↦ (x(r))_(r in R)` is a bijection onto `Y^R`; give `Coind(Y)` the
product measure `nu^R`. Replacing `r` by `rf` changes the coordinate by `f^-1`, which preserves `nu`, so the
measure does not depend on `R`, and it is `G`-invariant. The value `x(t)` is the *label of the coset `tF`
rooted at `t`*; labels at different cosets are independent.

- **Bernoulli shifts.** For `Y = L^F` with `(f.y)(f') = y(f^-1 f')`, the map `x ↦ (tf ↦ x(t)(f))` is well
  defined because `x(tf)(1) = (f^-1 . x(t))(1) = x(t)(f)`. It identifies `Coind(L^F)` with `L^G`.
- **Products.** `Coind(Y × Y') = Coind(Y) × Coind(Y')` with the diagonal action.
- **Entropy.** `H(Y)` is the Shannon entropy of `nu` (infinite unless `nu` is purely atomic with finite sum).

## 2. Theorem C

**Theorem C.** Let `(Y_1, nu_1)`, `(Y_2, nu_2)` be F-spaces with `H(Y_1) = H(Y_2)`. Suppose `P` is a Borel set
contained in both, `F`-invariant for both actions, on which the two actions agree and act freely, with
`nu_1|P = nu_2|P` and `nu_1(P) > 0`. Then `G ↷ Coind(Y_1)` and `G ↷ Coind(Y_2)` are isomorphic.

For `Y_i = L_i^F` with `|F| >= 5` this is Seward's relation `R_Gamma` and his Theorem 3.2 in that case.

*Proof.* Write `rho = nu_1(P) = nu_2(P)`. If `rho = 1`, then `Y_1 = Y_2 = P` as F-spaces up to null sets,
and there is nothing to prove. Assume `0 < rho < 1`.

**Step 1: the common factor.** Let `M = P ⊔ {*}` with `F` fixing `*`, and
`mu_0 = nu_i|P + (1 - rho) delta_*`, the same for `i = 1, 2`. Define `theta_i: Coind(Y_i) -> Coind(M)` by
`theta_i(x)(t) = x(t)` if `x(t) in P`, and `*` otherwise. It respects the defining relation because `P` is
`F`-invariant, and it is equivariant. Coset by coset it pushes `nu_i` to `mu_0`, so both `theta_i` push
their measures to `mu = mu_0^R`.

**Step 2: `G` acts freely on `(Coind(M), mu)`.** Fix `s != 1`. For `t in G`, consider the condition
`z(s^-1 t) = z(t)`, which holds at every `t` if `s.z = z`.
- If `s^-1 t F = tF`, write `s^-1 t = t f'` with `f' != 1`. The condition says `f'^-1 . z(t) = z(t)`, and `F`
  acts freely on `P`, so `z(t) = *`. This has probability `1 - rho < 1`.
- Otherwise `z(s^-1 t)` and `z(t)` are labels at distinct cosets, independent with law `mu_0`. They agree
  with probability `sum over atoms of mu_0(y)² <= max_y mu_0(y) < 1`, because `mu_0` gives mass
  `1 - rho` and `rho` to the disjoint sets `{*}` and `P`.
- `G/F` is infinite, so there are `t_1, t_2, ...` whose pairs of cosets `{t_i F, s^-1 t_i F}` are pairwise
  disjoint. The events at the `t_i` are independent, each of probability `<= c < 1`, so `mu(Fix(s)) = 0`.

`G` is countable, so the action is essentially free. It is mixing, since cylinder events on disjoint finite
sets of cosets are independent, and hence ergodic.

**Step 3: distinguished roots and a copy of `Z`.** `Z_* = { z : z(1_G) = * }` is `F`-invariant with
`mu(Z_*) = 1 - rho > 0`. As `F` is finite and acts freely a.e., choose a Borel `V ⊆ Z_*` meeting every
`F`-orbit in `Z_*` exactly once. Then `Coind(M)` is partitioned by `{z : z(1) in P}` and the sets `f.V`,
`f in F`. Note `g.z in V` iff `(g.z)(1) = z(g^-1) = *` and `g^-1` is the *distinguished root* of the
`*`-coset `g^-1 F`; each `*`-coset has exactly one distinguished root.

Let `E` be the orbit relation of `G` on `Coind(M)`. By ergodicity and `mu(V) > 0`, the classes of `E ∩ V×V`
are infinite a.e. By [6, Lem. 3.25] fix an aperiodic Borel bijection `T: V -> V` with graph in `E`, and
`t(z) in G` with `t(z).z = T(z)` (unique by freeness). Lift to `V_i = theta_i^-1(V)` by
`T_i(x) = t(theta_i(x)).x`.

**Step 4: Ornstein along the rows.** Put `A_i = Y_i \ P` with the normalized restriction `alpha_i` of `nu_i`.
Expanding `H(Y_i) = H_(nu_i)({P, A_i}) + rho H(P, nu_i|P / rho) + (1 - rho) H(A_i, alpha_i)`, the first two
terms agree for `i = 1, 2`, so `H(A_1) = H(A_2)`. By [17, 18] there is a `Z`-isomorphism
`zeta: (A_1^Z, alpha_1^Z) -> (A_2^Z, alpha_2^Z)` for the shift `S(y)(n) = y(n-1)`. Define
`f_i: V_i -> A_i^Z` by `f_i(x)(n) = T_i^-n(x)(1_G)`. Then `f_i ∘ T_i = S ∘ f_i`.

**Step 5: the map.** For `x in Coind(Y_1)` and `g in G`:
- if `x(g) in P`, put `pi(x)(g) = x(g)`;
- otherwise `g^-1 . x in f.V_1` for a unique `f in F` (so `gf` is the distinguished root of `gF`), and put
  `pi(x)(g) = f . zeta(f_1(f^-1 g^-1 . x))(0)`.

This lies in `A_2`, which is `F`-invariant. It respects the defining relation: for `f'' in F`,
`(g f'')^-1 . x = f''^-1 g^-1 . x` lies in `(f''^-1 f).V_1`, so
`pi(x)(g f'') = f''^-1 f . zeta(f_1(f^-1 g^-1 . x))(0) = f''^-1 . pi(x)(g)`. It is equivariant because it is
defined through `g^-1 . x`. And `theta_2 ∘ pi = theta_1`.

Define `pi': Coind(Y_2) -> Coind(Y_1)` in the same way with `zeta^-1`.

**Step 6: `pi` is an isomorphism.** Fix `z in Coind(M)` and disintegrate `nu_i^R` over `theta_i` as
`(nu_i)_z`. Enumerate `{ g : g.z in V }` as `w^j_n` (`j in J` countable, `n in Z`) with
`T(w^j_n . z) = w^j_(n+1) . z`. Under `(nu_i)_z`:
- labels at cosets with `z(t) in P` are the fixed values `z(t)`, and `pi` does not change them;
- the labels at the distinguished roots, `(w^j_n . x)(1_G) = x((w^j_n)^-1)`, are i.i.d. with law `alpha_i`,
  since which cosets are `*`-cosets and where their roots sit depends only on `z`.

So the rows `f_1(w^j_0 . x)`, `j in J`, are i.i.d. with law `alpha_1^Z`. Since the root `(w^j_n)^-1` is
distinguished (`f = 1`) and `theta_2(pi(x)) = z` has the same `V`-points,

    (w^j_n . pi(x))(1_G) = zeta(f_1(T_1^n (w^j_0 . x)))(0) = zeta(S^n f_1(w^j_0 . x))(0) = zeta(f_1(w^j_0 . x))(-n).

So the new rows are `zeta` of the old rows, i.i.d. with law `alpha_2^Z`, and `pi` pushes `(nu_1)_z` to
`(nu_2)_z`. The display also gives `f_2(w^j_0 . pi(x)) = zeta(f_1(w^j_0 . x))`. The same display for `pi'`
with `zeta^-1` gives `pi'(pi(x)) = x` a.e., and symmetrically `pi ∘ pi' = id`. Integrating over `z`, `pi` is a
measure-preserving equivariant bijection mod null sets. QED.

## 3. What changes relative to Seward

Seward's Section 3 uses the Bernoulli structure only through: independence of labels across cosets; a
common invariant free set of labels with equal measure; entropy equality of the complements; and a Borel
choice of one root per `*`-coset. Each of these holds for co-induced F-spaces as in Steps 1–6. The only
change is that a label is a point of an arbitrary F-space `Y`, rooted at a coset representative, instead
of a function `F -> L`. Section 5 of Seward (comparison with Bowen) needs a common factor with strong
independence over it; Step 1 supplies it.
