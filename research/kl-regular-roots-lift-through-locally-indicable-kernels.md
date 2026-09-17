---
rg: 2
id: kl-regular-roots-lift-through-locally-indicable-kernels
kind: claim
title: A root of the quotient equation whose Fox derivative has no left annihilator injects every locally indicable extension, and at the universal root this is relative asphericity
distinct_from:
  kl-p-power-index-reduces-to-p-nonsingular-square-systems: that roots the quotient equation inside Q = G/H itself, needs Q to be a p-group so the matrix is invertible mod p, and stops at an open systems problem over torsion-free H; this allows a root in any overgroup of Q, finite or not, asks only that the Fox derivative have no left annihilator, and solves the system with Howie's theorem because H is locally indicable.
  howie-locally-indicable-nonsingular-equations-are-solvable: that needs the whole coefficient group to be locally indicable, so torsion-free; this needs only a locally indicable normal subgroup, and G may carry arbitrary torsion from G/H, including non-solvable finite quotients.
  krstic-p-nonsingular-equations-inject-locally-p-indicable-groups: that covers extensions of locally indicable groups by finite p-groups at degrees prime to p; this covers extensions by finite groups that are not p-groups, such as C_6 or A_5, where G is locally p-indicable for no prime.
  kl-pivot-letter-words-inject-over-torsion-free-by-finite: that cuts one cyclic chain of equations by Tietze elimination at degree one over a torsion-free H; this solves the whole square system at once over a locally indicable H, at every degree, whenever the root is regular.
  kl-relative-weight-test-gives-injectivity: that certifies asphericity of the presentation over G itself by curvature; item 3 here asks for asphericity of the presentation over the quotient G/H, a different hypothesis that is then used for every extension at once, and item 2 needs no asphericity at all.
artifacts:
  - research/artifacts/hl-howie-systems-2026-09-13.md
  - experiments/kl-regular-roots-2026-09-17/regroots.py
  - experiments/kl-regular-roots-2026-09-17/certify.py
  - experiments/kl-regular-roots-2026-09-17/driver5.py
  - experiments/kl-regular-roots-2026-09-17/driver5.out
---

Let `H <| G`, `F = G/H`, `w = s_1 ... s_k in G * <t>` with letters in
`G ∪ {t, t^(-1)}` and `m = deg_t(w) != 0`. Write `w-` for the image of `w` in
`F * <t>`.

**Regular roots.** A *root* of `w-` is a pair `(Gamma, tau)`: a group
`Gamma >= F` and `tau in Gamma` with `w-(tau) = 1`. Let `pi_j in Gamma` be the
image of `s_1 ... s_j` after `t -> tau`, and put

    D  =  sum over s_j = t of pi_(j-1)  -  sum over s_j = t^(-1) of pi_(j-1) tau^(-1)   in  Z[Gamma],

the Fox derivative `dw-/dt` at `tau`. The root is *regular over a ring* `R`
(`R = Z` or `F_p`) if `mu D = 0` with `mu in R[Gamma]` forces `mu = 0`.

1. **Lifting.** If `H` is locally indicable and `w-` has a root regular over
   `Z`, then `G -> (G * <t>)/<<w>>` is injective. If `H` is locally
   `p`-indicable and the root is regular over `F_p`, the same conclusion holds.
2. **Explicit class.** Let `H` be locally indicable, `V in H * <t>` of degree
   `m`, and `g in G` with `gH` of finite order `d` in `G/H`, `gcd(m, d) = 1`.
   Then `w = V g` injects `G`. (Only `g` may lie outside `H`, the `t`-shape of
   `V` is arbitrary, and `G/H` is arbitrary.)
3. **Universal root = asphericity.** Let `Gamma_F = (F * <t>)/<<w->>` with
   `tau = t` and suppose `F -> Gamma_F` is injective (automatic for finite `F`).
   Let `X = K(F,1) ∪ e^1_t ∪ e^2_(w-)`. Then
   `{mu in Z[Gamma_F] : mu D = 0}  ≅  pi_2(X)`.
   So the universal root is regular over `Z` iff `X` is aspherical, and then it
   is regular over every `F_p`. Hence: **if the relative presentation
   `<F, t | w->` is aspherical with `F` injecting, then `w` injects every
   locally indicable, and every locally `p`-indicable, extension of `F`, for
   every lift `w` of `w-`**, whatever `m` is.
4. **Where the certificate is blind.** If `w-` is conjugate in `F * <t>` to
   `t^m c` with `c in F` of order `d` and `gcd(m, d) > 1`, then no root of `w-`
   in any group is regular over `Z`. So item 1 never applies to such words,
   although every such word, e.g. `t^2 a` with `a^2 = 1`, is trivially
   injective. Item 1 is a sufficient certificate, not a characterization.

## Why it is new here

- The regular root in item 2 lies in `F` itself, but the universal root there
  is `C_(md)`, where `D = 1 + tau + ... + tau^(m-1)` is a zero divisor. So
  item 1 at finite non-universal roots is strictly stronger than item 3.
- For `F = C_6`, `m = 5` in item 2, `G` contains `C_2` and `C_3` and is
  locally `p`-indicable for no prime. It is torsion-bearing, so Klyachko and
  Howie do not apply. When `H` is an arbitrary locally indicable group (for
  example a torsion-free one-relator group not known to be sofic) permuted
  by `C_6`, neither hyperlinearity nor a finite-by-locally-indicable
  structure is known.
- Item 3 says the relative asphericity of the quotient presentation
  is exactly the invariant the coinduced square system sees at the universal
  root. It is a hypothesis on `G/H` alone, and one verification serves every
  locally indicable extension of `G/H` and every lift `w` at once.

## Status

**ESTABLISHED** (proposed) through
`kl-regular-roots-coinduced-square-system-proof`. The proof uses the
Kaloujnine--Krasner embedding, coinduction to `Gamma`, the systems theorems of
Howie [How81] and Krstic [Kr85] (quoted from arXiv:2309.09096 l.264--274 in the
artifact), and the cellular chain complex of the universal cover. Not
independently reviewed. No novelty claimed; the literature beyond the pins was
not searched. The reverse mating, GR-by-locally-indicable, is the Main theorem
of Klyachko--Mikheenko arXiv:2204.01122 (pinned in
`research/artifacts/hl-kl-howie-overlap-2026-09-14.md`); a nontrivial finite
quotient is not locally indicable, so it does not cover the extensions here.

## Where regular roots can live

`kl-amenable-regular-roots-lie-in-the-coefficient-group` settles the search
question that was left open here. For finite `F`, a root `tau` with
`<F, tau>` amenable and different from `F` is never regular over `Z`, and a
finite one is never regular over any field. So item 1 with an amenable root
group says exactly: some `c in F` has `w-(c) = 1` and `D(c)` a unit of
`Q[F]` (of `F_p[F]` for the `p`-version). The regular roots of item 2 are of
this kind.

The `C_6` word `c^2 t^(-1) c^5 t c^5 t^(-1) c` (degree `-1`) has the single
root `c` in `C_6`, where `D = -c + 1 - c^5` vanishes at the character
`c -> e^(i pi/3)`. Every root group `<C_6, tau>` is a quotient of
`Gamma_F ≅ B_3/<<sigma_1^6>>`, which is amenable. So this word has no regular
root in any group, and it is not of the form `t^m c` of item 4. The exact
computation `driver5.py` agrees: every one of its 30 roots in `S_8` (with
`C_6` acting as a 6-cycle) has a singular Fox derivative in the permutation
representation on points or on ordered pairs (`driver5.out`, 1.3 s).
