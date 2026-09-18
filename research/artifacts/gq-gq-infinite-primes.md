# GL_n(Z[1/P]) for infinite sets of primes P (lane gq-infinite-primes, 2026-09-17)

Assignment: is some infinite `P` easier than all primes; is the general-`P` statement equivalent to the root
`gl-n-q-embeds-in-fp-simple-group` (G); which obstructions depend on `P`. Lane proofs are not independently
reviewed; imports are marked.

## 1. Answers

1. **Is some P easier?** Yes, every `P` that misses a prime. For `l ∉ P`,
   `GL_n(Z[1/P]) <= GL_n(Z_(l)) <= Aff_n(Z_(l))`, and that group is residually finite. It also acts faithfully,
   self-similarly and by finite-state automorphisms on the `l^n`-ary tree
   (`aff-n-over-z-localized-at-ell-is-rf-and-self-similar`). So the root's obstruction O1 holds exactly for
   `P` = all primes. Within the residually finite range the hardest case is `P` = all primes but one, the claim
   `gl-n-z-localized-at-ell-embeds-in-fp-simple-group` (OPEN). It settles every `P ∌ l` at once.
2. **Is the general-P statement equivalent to G?** G implies it (routes `gl-n-z-localized-via-gl-n-q`,
   `sl-2-q-via-gl-n-q`). No converse by linear or residually finite means:
   - `z-localizations-embed-in-gl-n-only-along-inclusion`: `GL_n(Z[1/P])` embeds in `GL_N(Z[1/P'])` iff
     `P ⊆ P'`. So `GL_n(Q)`, and even `(Q,+)`, is in no `GL_N(Z[1/P'])` with `P'` missing a prime.
   - O1: `GL_n(Q)` is in no residually finite group, while every `GL_n(Z[1/P'])`, `P'` co-nonempty, is residually
     finite.
   The one structural bridge back is non-residually-finite. For every prime `l`,
   `SL_2(Q) = SL_2(Z_(l)) *_{Γ_0(l)} SL_2(Z_(l))^{diag(1,l)}` (Ihara;
   `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell`), and `PSL_2(Q)` acts faithfully and cocompactly on the
   `(l+1)`-regular tree. So `SL_2(Q)` is assembled from the residually finite group of the case "all primes but
   `l`" by one locally finite amalgam. The `l`-divisibility comes from the tree:
   `infinitely-q-divisible-dvr-matrices-are-torsion` shows the vertex groups have none.
3. **Which obstructions depend on P?** See the table in §2.

## 2. Obstructions against P

| Obstruction | P finite | P infinite, missing a prime | P = all primes |
|---|---|---|---|
| O1: no residually finite overgroup (divisible subgroup) | no | **no** (residually finite, self-similar) | yes |
| No finitely generated linear overgroup (`infinite-prime-localizations-embed-in-no-fg-linear-group`; also `fg-linear-groups-have-roots-at-finitely-many-primes`) | no (itself f.g. linear) | **yes** | yes |
| Not finitely generated | no | yes | yes |
| O2: `SL_3(Z) <= GL_n`, `n >= 3` (V, VA excluded) | yes | yes | yes |
| O3: `Z[1/P] ⊄ V` (Higman: infinite-order elements of `V` have roots of finitely many orders; non-cyclic subgroups of `Q` do not embed) | yes, P nonempty | yes | yes |
| O4: distorted unipotents (`BS(1,p^2) <= SL_2(Z[1/p])`) | yes, P nonempty | yes | yes |
| Affine self-similar hosts over `Z[1/m]` reach it | yes (Zaremsky Thm 1.2) | no: f.g. subgroups of `Aff_n(Z_(l))` see finitely many primes | no (O1) |

So the only obstruction that separates co-nonempty infinite `P` from all primes is O1.
Separating infinite `P` from finite `P` are non-finite-generation and the no-finitely-generated-linear-overgroup
statement.

## 3. Routes landed

- `gl-n-z-localized-via-fp-self-similar-overgroup`: `aff-n-z-localized-lies-in-fp-self-similar-group` (OPEN)
  plus Zaremsky Thm 1.1 gives `GL_n(Z_(l))` in a finitely presented simple group. Any witness is a non-linear,
  non-affine automaton group.
- `sl-2-q-via-hecke-overgroup-and-bliw`: `sl-2-z-localized-has-fp-hecke-overgroup` (OPEN) plus Ihara plus
  Bux--Llosa Isenrich--Wu Theorem C gives `sl-2-q-embeds-in-fp-simple-group`.
  - The hypothesis asks for a finitely presented group `Λ ⊇ SL_2(Z_(l))` with the Hecke partial isomorphism
    `Γ^0(l) -> Γ_0(l)` (conjugation by `diag(1,l)`) extended to an isomorphism of finite-index subgroups.
  - `Λ` must be residually finite and non-linear. Serre's `SL_2(Z[1/p]) = SL_2(Z) *_{Γ_0(p)} SL_2(Z)^α` is the
    finite-prime analogue, with `Λ = SL_2(Z)`.
  - This reaches `SL_2(Q)` with its centre, which the Möbius route
    (`psl2-q-fp-simple-via-rational-iwahori-rn-host`) cannot; that route reaches `PSL_2(Q)`.

## 4. Where this stops, and sparks

- **n >= 3.** The analogous one-prime presentation of `SL_n(Q)` is a finite simplex of groups over the building
  of `SL_n(Q_l)`, with vertex groups conjugate to `SL_n(Z_(l))`. It inherits imports I2, I3 of
  `sl-n-q-is-colimit-of-lattice-stabilizers`. BLIW is a tree theorem.
  - **Spark:** a BLIW-type theorem for groups acting faithfully and cocompactly on locally finite Euclidean
    buildings with finitely presented cell stabilizers would carry the §3 reduction to `SL_m(Q)`, `m` odd, and so
    to the root through `sl-odd-q-simple-inputs-for-gl-n-q-root`.
- **Spark:** the Hecke partial map `α = diag(1,l)` on `Z_l^2` is `(x,y) -> (x, l y)`, a prefix insertion on the
  second coordinate. That is a Brin--Thompson `2V_l`-type partial map. Groups generated by `2V_l` and
  `Aff_2(Z_(l))` carry both the vertex group and the Hecke map; possible input for germ/Brin--Thompson lanes.
- **Dead:** finitely generated affine self-similar hosts for infinite `P` (part 4 of the self-similar node), and
  every finitely generated linear host for infinite `P`.
