# Zaremsky Problem 3.2: do braid groups embed in GL_n(Z)? Landscape, 2026-09-13

Lane z3-02-braid-glnz. Root: `zaremsky-3-02-braid-groups-embed-in-glnz`.
Nothing here is reviewed. Statuses:

- **established**: a complete proof is on main as a `-proof` route;
- **verified**: the statement was read in the source (PDF text extracted on
  MSI);
- **cited**: from memory or an abstract, not yet read in the source.

## 1. The question and its monotone shape

A group is *Z-linear* if it has an injective homomorphism into some `GL_m(Z)`.
Problem 3.2 asks whether every braid group `B_n` is Z-linear. Since
`B_n <= B_(n+1)`, the answer is a threshold `N*`: `B_n` is Z-linear iff
`n < N*`. Established: `N* >= 4`.

## 2. Established results (on main)

| claim | content |
|---|---|
| `torsion-free-virtually-z-linear-groups-are-z-linear` | the induced representation embeds a torsion-free `G` in `GL_(m[G:H])(Z)` once a finite-index `H` embeds in `GL_m(Z)` |
| `braid-group-z-linear-iff-pure-braid-mod-center-z-linear` | `P_n = U_n × <Delta^2>` with `U_n = ker(P_n -> P_2)`; `B_n` Z-linear ⟺ `P_n` ⟺ `P_n/<Delta^2>`; for `n = 4` this is `F_3 ⋊ F_2` |
| `braid-groups-on-at-most-three-strands-embed-in-glnz` | `B_3 <= GL_24(Z)` through `P_3 = F_2 × Z` |
| `faithful-unit-specialization-gives-z-linearity` | a faithful specialization of a Laurent-polynomial representation at algebraic units gives Z-linearity (restriction of scalars) |
| `braid-groups-embed-in-gl-over-integer-laurent-polynomials` | `B_n <= GL_(n(n-1))(Z[t^{±1}])`: Cohen–Wales Thm 1.2 at the unit `r_0 = (3 - sqrt 5)/2`, then restriction of scalars from `Z[phi]` |
| `number-field-linear-groups-act-properly-on-cat0-spaces` | a finitely generated subgroup of `GL_m(F)`, `F` a number field, acts properly on a proper CAT(0) space (symmetric spaces × Bruhat–Tits buildings × R) |

## 3. Routes into the answer claims

Affirmative, `every-braid-group-embeds-in-some-glnz`:

- `braid-z-linearity-via-lkb-unit-specialization` (open premise:
  `lawrence-krammer-has-a-faithful-algebraic-unit-specialization`).

Negative, `some-braid-group-embeds-in-no-glnz`:

- `braid-not-z-linear-from-no-proper-cat0-action` (open premise
  `some-braid-group-has-no-proper-cat0-action`, owned by z3-06-braid-cat0).

Cross-link: `every-braid-group-is-linear-over-a-number-field` (open) follows
from a yes for 3.2. It implies `every-braid-group-acts-properly-on-a-proper-cat0-space`,
the non-cocompact reading of Problem 3.6, which the list calls unknown.

## 4. What does not obstruct Z-linearity

Every standard necessary condition for a finitely generated subgroup of
`GL_m(Z)` holds for `B_n`:

- residually finite, with the Tits alternative, since `B_n` is linear in
  characteristic 0;
- virtually residually `p` for every prime `p`: `P_n` is residually
  torsion-free nilpotent (Falk–Randell, cited);
- solvable subgroups virtually abelian (Birman–Lubotzky–McCarthy, cited);
- torsion-free with a finite classifying space; no `BS(1, k)` with `|k| >= 2`;
  no abelian subgroups of infinite rank;
- cyclic subgroups undistorted (Garside groups are biautomatic, cited). So the
  "distorted elements become unipotent over a number field" argument, which
  the graph uses for `el3-of-infinite-rank-rings-not-linear-over-number-fields`,
  has nothing to act on.

An obstruction must use something that holds for `GL_m(Z)` and fails for
`GL_m(Z[t^{±1}])`. Discreteness in `GL_m(R)`, equivalently a proper action on
`SL_m(R)/SO(m)`, is the obvious candidate; see §3.

## 5. Why the known faithful representations do not specialize

- **Verified** (Cohen–Wales, arXiv:math/0010204v2, Thm 1.2): coefficients in
  `Z[r, t, r^-1, t^-1]`; faithful over `R[t, t^-1]` after `r -> r_0` for every
  real `0 < r_0 < 1`. So one parameter can be a real algebraic unit, and `t`
  stays formal.
- **Verified** (Bigelow, arXiv:math/0005038, Thm 1.1): "The Lawrence-Krammer
  representation of Bn is faithful for all n", with `φ: π_1(C) -> <q> × <t>`
  the two-variable monodromy.
- **The countability gap.** Each nontrivial braid dies at finitely many values
  of the formal parameter. The union of these sets is countable, as is the set
  of algebraic numbers, so counting gives nothing.
- **The positivity mechanism needs reduction modulo t** (verified in
  Cohen–Wales §4). "0 < r_0 < 1 implies that the constant term of each of the
  entries of the matrices σ_i is a nonnegative real number", so the positive
  monoid preserves `U = ⊕ (R_≥0 ⊕ tR[t]) x_β`, and the cells `U_A` are cut out
  by support modulo `t`.
  - A specialization `t -> t_0` keeps this structure only through a quotient
    `O_F -> O_F/𝔭` with `t_0 ∈ 𝔭`. Then `t_0` is not a unit and the residue
    field is finite, with no cancellation-free positive cone.
  - Archimedean small `t_0` works only below a braid-dependent bound.
  - So the method reaches neither Z-linearity nor number-field linearity.
- **Bigelow's extremal-monomial argument** (from memory, not re-read): a
  nonzero integer extremal coefficient `m` survives `q -> p` only when `p` does
  not divide `m`. Not uniform.

## 6. Candidate positive mechanisms not yet recorded as routes

- **Virtual RAAG embedding of `P_n`.**
  - RAAGs are Z-linear (Humphries 1994; Hsu–Wise 1999; Davis–Januszkiewicz
    commensurability with right-angled Coxeter groups, whose Tits
    representation is integral; all cited).
  - `B_n` is not virtually cocompactly cubulated for `n >= 4` (Haettel,
    arXiv:1509.08711, as quoted in the 3.6 root).
  - Nothing found so far excludes a non-cocompact embedding of a finite-index
    subgroup into a RAAG. Two tests do not help: root-closed centralizers hold
    in pure mapping class groups, and Koberda's high-power theorem defeats
    two-generator tests.
- **n = 4 through `Aut(F_2)`.** `B_4/Z(B_4)` is a finite-index subgroup of
  `Aut(F_2)` (Dyer–Formanek–Grossman, cited; consistent with Barré–Pichot,
  arXiv:0809.0645, abstract). So `B_4` is Z-linear iff `Aut(F_2)` has a
  finite-index Z-linear subgroup.
- **Homology of finite covers.** Koberda's asymptotic linearity (cited) gives
  residual Z-linearity only. For `Aut(F_2)`-type groups any finite collection
  of covers has an infinite kernel: inner automorphisms by elements of the
  covering subgroup act trivially on its homology.
