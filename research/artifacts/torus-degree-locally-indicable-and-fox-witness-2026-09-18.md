# Torus degree over locally indicable groups, and the Fox witness (2026-09-18)

Lane: swarm-0917-w13-w13-gs-last1, paradigm/decomposition, family group-rings.
Target hole: C2 = `injective-torus-automata-have-regular-degree` on the torus route
`gottschalk-via-torus-alphabet-degree-transfer`.

## 0. Summary

Two results fix exactly how far the circle of constants reaches for C2. This data is
`epsilon(D) in GL_d(Z)`, available for every injective torus automaton over every group.

- **Theorem A (positive; ESTABLISHED).** Let `G` be locally indicable, `d >= 1`, and
  `tau: (T^d)^G -> (T^d)^G` injective, continuous and equivariant.
  - `D(tau)` is regular over `Q[G]`, so `tau` is onto: `G` is torus-surjunctive at every `d`.
  - Moreover `D(tau) in GL_d(Z[G])`.
  - More generally, over any group, C2 holds for every injective `tau` whose degree support
    `<supp D>` is locally indicable.
- **Theorem B (obstruction; ESTABLISHED).** Suppose a group `H` contains a nontrivial finitely
  generated perfect subgroup `L`. Then some `D in M_n(Z[H])`, with `n` the number of generators
  of `L`, has
  - `epsilon(D) = I_n`, and
  - a nonzero row vector `c^*` with `c^* D = 0`.
  It is the **Fox witness**, built from the Fox Jacobian of a presentation of `L`. For Higman's
  four-generator group it is written out explicitly below, with `n = 4`.

**What this changes.**
- *Correcting w9.* `torus-degree-regular-on-prime-power-residual-support` says augmentation-only
  proofs of C2 "work exactly on RPP support". That is not the exact reach. They also work on every
  locally indicable support group, and most of these are not RPP, for example `BS(2,3)`.
- *New dying class.* Augmentation-only proofs die on a second class, the groups with a nontrivial
  f.g. perfect subgroup. That class includes torsion-free groups.
- *Current map.* The map is now **succeed on RPP or locally indicable support; die on a
  non-prime-power finite subgroup (Bezout witness, w9) or on a nontrivial f.g. perfect subgroup
  (Fox witness, here)**.
- *The first test of need 7c18e718.* That test (sofic small-fibre lemma, `d = 2` over `BS(2,3)`)
  is settled by Theorem A without any approximation of `BS(2,3)`.

## 1. Conventions

These follow `torus-automata-with-regular-degree-are-surjective`:
- `H^1((T^d)^G; Z) = Z[G]^d` as row vectors;
- `tau^*(xi) = xi D(tau)` with `D(tau) in M_d(Z[G])`;
- `r_A(x) = xA`;
- `A^*` is the conjugate transpose, with `g -> g^{-1}`;
- `epsilon: Z[G] -> Z` is the augmentation, applied entrywise.

**Fact 1 (periodic-point lemma at `N = G`).** This is in
`torus-automata-over-rf-or-domain-groups-are-surjunctive`, and is valid over every group.
- The constants `Fix(G) = T^d` are preserved by `tau`.
- Invariance of domain on the closed manifold `T^d` makes `tau|` a homeomorphism.
- `H^1` of the inclusion is `epsilon`.
- Hence `epsilon(D(tau)) in GL_d(Z)`.

**Fact 2 (support reduction).** This is Lemma 1 of
`torus-degree-regular-on-prime-power-residual-support`. Let `H = <supp D>`. If `r_D` is injective
on `Q[H]^d`, it is injective on `Q[G]^d`.

**Fact 3 (C1).** `torus-automata-with-regular-degree-are-surjective`: if `r_D` is injective on
`Q[G]^d`, then `tau` is onto.

## 2. Theorem A: locally indicable groups

**Import (Strebel; Howie–Schneebeli).** The statement is quoted verbatim, second hand, from
T. D. Cochran and S. Harvey, *Homology and derived series of groups*, Geom. Topol. 9 (2005),
2159–2191 (arXiv math/0407203v2), pp. 2174–2175. It is quoted in
`strebel-class-dz-is-locally-indicable-citation`.

> Lemma 4.4 Suppose f̃ : M → N is a homomorphism between free ZΓ–modules with Γ PTFA and let
> f = f̃ ⊗ id be the induced homomorphism of abelian groups M ⊗_{ZΓ} Z → N ⊗_{ZΓ} Z. [...]
> In [27, page 305], Strebel shows that, under the hypotheses of Lemma 4.4, if f is injective
> then f̃ is injective. There he shows that the class, D(Z), of groups Γ for which this property
> is satisfied includes torsion-free abelian groups and is closed under various natural
> operations such as extensions. Consequently, any PTFA group is in this class. This class of
> groups was previously called conservative and was later shown by J Howie and H Schneebli to
> coincide with the class of locally indicable groups [14].

Here [27] is R. Strebel, Comment. Math. Helv. 49 (1974) 302–332, and [14] is J. Howie and
H. R. Schneebeli, Manuscripta Math. 44 (1983) 71–93.

The property defining `D(Z)` is a statement about homomorphisms of free modules. It does not use
the PTFA hypothesis of Lemma 4.4, which only places PTFA groups inside `D(Z)`. The class `D(Z)`
is defined with the side on which the free modules are modules. The anti-automorphism
`g -> g^{-1}` of `Z[G]` commutes with `epsilon` and exchanges left and right modules, so it does
not matter which side is used.

**Independent in-graph route.** `flat-weak-bass-holds-exactly-for-locally-indicable-groups`,
item 1(ii), which is ESTABLISHED in the graph, says that for locally indicable `G`,
`rank_Q epsilon(A) <= rk_U(A)` for every matrix `A` over `Z[G]`. That node uses the same
row-vector convention `r_A(x) = xA`.

**Proof of Theorem A.**
1. By Fact 1, `epsilon(D) in GL_d(Z)`, so `Q (x) r_D = r_{epsilon(D)}` is injective on
   `Z^d = Z[G]^d (x)_{Z[G]} Z`.
2. **Route (i), Strebel.** `G` is in `D(Z)`, and `r_D` is a homomorphism of free `Z[G]`-modules
   whose augmentation is injective, so `r_D` is injective on `Z[G]^d`. If `xi in Q[G]^d` has
   `xi D = 0`, then clearing denominators gives `m xi in Z[G]^d` with `(m xi) D = 0`, so `xi = 0`.
   Hence `r_D` is injective on `Q[G]^d`.
3. **Route (ii), Cohn specialization.**
   - `rk_U(D) >= rank_Q epsilon(D) = d`, so the image of `r_D: U^d -> U^d` has `U`-dimension `d`,
     and its kernel has dimension 0.
   - `U = U(G)` is von Neumann regular, so the kernel is a direct summand of `U^d`. It is
     finitely generated projective of dimension 0, hence zero, because `dim_U` is faithful on
     f.g. projectives.
   - So `r_D` is injective on `U^d`, which contains `Q[G]^d`.
4. By Fact 3, `tau` is onto. So `tau` is a continuous equivariant bijection of a compact space, a
   homeomorphism, with continuous equivariant inverse `tau^{-1}`.
5. `(tau^{-1} tau)^* = tau^* (tau^{-1})^*` gives `D(tau^{-1}) D(tau) = I`, and symmetrically
   `D(tau) D(tau^{-1}) = I`. So `D(tau) in GL_d(Z[G])`.
6. **Support version.** Over any `G`, if `H = <supp D>` is locally indicable, apply steps 1–3 over
   `Q[H]` (note `epsilon(D)` is the same computed in `Z[H]`), then Fact 2 and Fact 3.

**New hosts.** `BS(2,3) = <x, y | y^{-1} x^2 y = x^3>` is a torsion-free one-relator group, and
such groups are locally indicable (Brodskii; Howie, recalled). It is not covered by any earlier
node:
- it is not residually finite, because it is finitely generated and non-Hopfian (Malcev);
- so it is not RPP;
- being finitely presented and not residually finite, it is not LEF;
- it is nonabelian;
- the domain case of `torus-automata-over-rf-or-domain-groups-are-surjunctive` covers only
  `d = 1`.

So Theorem A gives C2 and TS over `BS(2,3)` at every `d`. This is the first test named in need
7c18e718. It needs no soficity, and holds verbatim for every locally indicable group, including
any whose soficity is unknown.

Other locally indicable families (recalled, not needed for the claim):
- torsion-free one-relator groups;
- bi-orderable groups (e.g. Thompson's `F`);
- knot groups;
- one-relator products of locally indicable groups with non-proper-power relator (Howie).

**Remark (recalled, not claimed).** For `d = 1`, Theorem A gives `D(tau) in Z[G]^x`. The units of
`Z[G]` for locally indicable `G` are trivial (Higman 1940), so `D(tau) = +- g`. Then
`g^{-1} tau` has degree `+-1` in every coordinate.

## 3. Theorem B: the Fox witness

**Construction.**
- Let `L = <x_1, ..., x_n | r_j (j in J)>` be a nontrivial, finitely generated, perfect group.
  Choose all `x_i != 1`.
- Let `J_{ji} in Z[L]` be the image of the left Fox derivative `d r_j / d x_i`.
- **Fundamental formula.** `sum_i (d r / d x_i)(x_i - 1) = r - 1` holds in `Z[F]`. Proof: induct on
  word length using `d(uv) = du + u dv`. After mapping to `Z[L]`, where `r_j = 1`, this gives
  `J c = 0` for the column `c = (x_1 - 1, ..., x_n - 1)^T`.
- `epsilon(J_{ji})` is the exponent sum of `x_i` in `r_j`.
- `H_1(L; Z)` is `Z^n` modulo the span of the exponent-sum vectors, so perfection means these
  vectors span `Z^n` over `Z`. Since `Z^n` is noetherian, finitely many relators `r_1..r_k`
  already span, even if `L` is not finitely presented.
- So there is `P in M_{n x k}(Z)` with `P epsilon(J) = I_n`.
- Put `D_0 = P J in M_n(Z[L])`. Then `epsilon(D_0) = I_n` and `D_0 c = P (J c) = 0`.
- Put `D = D_0^*`. Then `epsilon(D) = I_n` and `c^* D = (D_0 c)^* = 0`, where
  `c^* = (x_1^{-1} - 1, ..., x_n^{-1} - 1) != 0`.
- If `L <= H`, the same `D` lies in `M_n(Z[H])`.

So `r_D` has a nonzero kernel on `Z[H]^n`, although its augmentation is the identity. Every
argument that deduces regularity from `epsilon(D) in GL_d(Z)` plus ring theory of `Z[H]` fails at
this `D`. The failing step is the passage from injectivity mod the augmentation ideal to
injectivity. This is Strebel's `D(Z)` property, and the Fox witness is the standard reason
`D(Z)` excludes groups with perfect f.g. subgroups.

**Higman's group.** `H = <a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2>`, with the
repository's convention: relator `a^{-1} b a b^{-2}` and cyclic. The exponent-sum matrix is `-I`
up to a cyclic shift, so `P` is a signed permutation. The experiment prints
`D_0 = P J`. Reduced in `H`, using `d^{-1} a d = a^2` and so on, row `i` of `D_0` has
- `1 + x_i - x_{i-1}^{-1}` in column `i`, and
- `x_{i-1}^{-1} (1 - x_i)` in column `i-1`,
with `(x_0, ..., x_3) = (a, b, c, d)` and indices mod 4. The relator for row `i` is
`x_{i-1}^{-1} x_i x_{i-1} = x_i^2`.

Check for row 0 (`x_0 = a`, `x_{-1} = d`):
- `(1 + a - d^{-1})(a - 1) + d^{-1}(1 - a)(d - 1) = a^2 - 1 - d^{-1} a d + 1 = a^2 - a^2 = 0`.
- Augmentation: `(1, 0, 0, 0)`.

All four generators of `H` are nontrivial. If `a = 1`, the relations successively force
`b = c = d = 1`, while `H` is infinite (Higman). So `c^* != 0`, and `D = D_0^*` is a
`4 x 4` augmentation-identity zero divisor over `Z[H]`.

**Calibration on a finite perfect group.** `A_5 = <x, y | x^2, y^3, (xy)^5>`. The exponent-sum
lattice is spanned by `(2,0), (0,3), (5,5)`, which is `Z^2`, and `P = [[23, 15, -9], [-5, -3, 2]]`.
In the right regular representation of `Q[A_5]` (a `120 x 120` matrix), the experiment verifies:
- `c^* D = 0` exactly;
- `epsilon(D) = I_2`;
- `rank D = 61 < 120`.

(`A_5` also carries the w9 Bezout witness. The point here is that the Fox construction is
correct.)

**Contrast.** For `BS(2,3)` the exponent-sum lattice is `Z (1, 0)` up to sign, of rank `1 < 2`.
So no `P` exists, as Theorem A requires.

## 4. The reach of augmentation-only proofs of C2, updated

Let `H = <supp D>`, finitely generated.

| `H` | augmentation-only C2 | witness / proof |
|---|---|---|
| RPP (torsion allowed, `p`-power) | succeeds, all `d` | w9, nilpotent augmentation ideal mod `p` |
| locally indicable | succeeds, all `d` | Theorem A (Strebel; Cohn specialization) |
| contains a finite subgroup of non-prime-power order | dies at `d = 1` | Bezout witness (w9) |
| contains a nontrivial f.g. perfect subgroup | dies at `d = n(L)` | Fox witness (Theorem B) |
| otherwise | open | e.g. torsion-free, not RPP, not locally indicable, every f.g. subgroup with nonzero abelianization, some with finite abelianization |

For a torsion-free `H`, being locally indicable means every nontrivial f.g. subgroup `L` has
`H_1(L; Q) != 0`. The two torsion-free rows differ exactly by the f.g. subgroups with `H_1(L; Z)`
finite and nonzero. For such `L`, the Fox construction gives `epsilon(P J)` of determinant
`+- |H_1(L)|` at best, not a unit.

**Correction to w9.** Consequence 1 of `torus-degree-prime-power-support-2026-09-17.md` says "a
counterexample to C2 must have `H(D)` non-RPP". This strengthens to non-RPP **and** not locally
indicable. The node text "works exactly on RPP support" should read "works on RPP and on locally
indicable support".

## 5. Consequences for the torus route and the needs

- **C2 open region.** A counterexample to C2 (equivalently to TS, given C1) needs a degree support
  group that is neither RPP, nor locally indicable, nor LEF (w10), nor abelian (w10).
  - By Theorems A and B together, where augmentation data is silent the obstruction is torsion
    (w9) or a perfect f.g. subgroup (here).
  - The torsion-free open hosts for C2 therefore contain f.g. subgroups with finite
    abelianization, and in particular include every group with a f.g. perfect subgroup that is
    not LEF.
- **Sharp kill-test on Higman's group `H`.**
  - Construct, or rule out, an injective continuous equivariant `tau` on `(T^4)^H` with
    `D(tau) = D_0^*` from §3. By C1 and Theorem B it would not be onto, which would refute TS at
    `H`.
  - Nothing in the graph excludes it. `H` has no nontrivial finite quotients (Higman), so the
    periodic tori give only `epsilon`, which the witness passes. LEF, abelian and RPP do not
    apply. Local indicability fails, since `H` is perfect.
  - `Q[H]` embedding in a division ring (`higman-group-algebras-embed-in-division-rings`, not
    re-derived) does not help: `D_0^*` is singular over `Q[H]` and hence over any division ring
    containing it.
  - Higman's group is also a standard candidate host for Gottschalk, since its soficity is open.
    So this test sits exactly where the flagship lives.
- **Need 7c18e718** (local sofic small-fibre lemma, first test `d = 2` over `BS(2,3)`). The named
  first test is answered positively by Theorem A. The need is still meaningful only for sofic
  support groups that are neither RPP nor locally indicable nor LEF, for example groups with f.g.
  perfect subgroups (`SL_3(Z)` is RF, so this means non-RF sofic perfect groups).
- **C3 (`torus-surjunctivity-implies-finite-alphabet-surjunctivity`)** is untouched. Theorem A
  makes TS known on locally indicable groups, where finite-alphabet Gottschalk is still open for
  non-sofic members, if any exist. So C3 cannot be tested against a counterexample there.

## 6. Checks

- `experiments/torus-fox-witness-2026-09-17/check_fox_witness.py`:
  - Part A verifies the Fox fundamental formula exactly in `Z[F]` for Higman's group, `A_5` and
    `BS(2,3)`, and verifies `epsilon(D_0) = I` for the two perfect ones.
  - Part B verifies the `A_5` witness in the regular representation: exact kernel row, and rank 61
    of 120 both mod `p = 1000003` and in floating point.
  - Part C shows that `BS(2,3)` admits no `P`.
  - Runtime is under a minute.
