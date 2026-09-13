# MF of C*_r(SL_4(Z)): source, status, obstructions, and a corona reduction (part 1)

Lane `ex3-sl4z-mf`, 2026-09-13.  UNREVIEWED.

Every quotation from [MdlS] below was read from the arXiv PDF (arXiv:2312.03220v2,
pages 1--6) on 2026-09-13.  Other literature is marked "standard, not re-read" wherever
this lane relies on a textbook statement without checking the source.

## 1. The question, verbatim, and the notions it uses

[MdlS] M. Magee, M. de la Salle, *SL_4(Z) is not purely matricial field*,
arXiv:2312.03220v2 (30 Jan 2024), C. R. Math. 362 (2024) 903--910.  From p. 2:

> "It does not seem to be known whether C*_r(SL3(Z)) or C*_r(SL4(Z)) is MF in the
> sense of Blackadar and Kirchberg."

The notions, pinned down:

- **Which algebra.**  The *reduced* algebra `C*_r(SL_4(Z))`, not the full `C*(SL_4(Z))`.
- **MF (Blackadar--Kirchberg).**  `A` admits an injective *-homomorphism into a norm
  matrix corona `Q_k = prod_n M_(k_n) / sum_n M_(k_n)`.
  - An embedding into an ultraproduct `prod_U M_(N_i)` gives one into `Q_k` along a
    subsequence (a diagonal argument on a countable dense set of `C[Gamma]`), and
    conversely.  Either reading gives the same question.
  - Lifting `iota(lambda(g))` to unitaries gives `phi_n : Gamma -> U(k_n)`.  The defect
    `||phi_n(gh) - phi_n(g) phi_n(h)||` tends to `0` for each fixed pair only, not
    uniformly (`corona-defect-is-not-uniform`), and
    `limsup_n ||phi_n(x)|| = ||lambda(x)||` for `x in C[Gamma]`.
- **PMF [MdlS, Def. 1.2 and p. 1].**  A sequence of *genuine* finite-dimensional
  unitary representations `rho_i` with `lim ||rho_i(z)|| = ||lambda_Gamma(z)||` for every
  `z in C[Gamma]` ("strong convergence").  PMF implies MF [MdlS p. 1].

## 2. What is proved and what is open

**Proved** [MdlS]:

> "Theorem 1.1. Every finite dimensional unitary representation of SL4(Z) contains a
> non-zero SL2(Z)-invariant vector."

Here `SL_2(Z)` is the block `[[*,*,0,0],[*,*,0,0],[0,0,1,0],[0,0,0,1]]` (p. 1).

> "Corollary 1.3. SL4(Z) is not purely matricial field."

Its proof (p. 2) gives `||rho(S+S^-1+T+T^-1)|| = 4` for every finite-dimensional `rho`,
while `||lambda_SL4(Z)(S+S^-1+T+T^-1)|| = ||lambda_SL2(Z)(S+S^-1+T+T^-1)|| < 4`.  The
abstract says exactly what this excludes: "there is no sequence of finite-dimensional
representations of SL4(Z) that gives rise to an embedding of its reduced C*-algebra into
an ultraproduct of matrix algebras."

**Open.**  MF of `C*_r(SL_4(Z))`, by the status sentence above.

- **Why the proof stops at genuine representations.**  It starts (p. 3): "It is an
  elementary consequence of work of Bass-Milnor-Serre on the congruence subgroup property
  [BMS67] (e.g. [Bek07, §5]) that every finite dimensional unitary representation of
  SL4(Z) arises from a composition of homomorphisms SL4(Z) -> SL4(Z/NZ) -> U(M)".  An
  asymptotic homomorphism factors through no finite quotient.
- **Later literature.**  The 2025--26 surveys found by lane `ex-mf-kazhdan-cstar`
  (Magee arXiv:2503.21619, van Handel arXiv:2510.12520) report no progress; see
  `research/artifacts/mf-kazhdan-cstar-literature-status-2026-09-12.md`.  This lane ran
  no new literature search.

## 3. Obstructions and routes: what each gives, and where it stops

**1. Quasidiagonality (Tikuisis--White--Winter, Schafhauser).**  Gives nothing here.
- These theorems derive QD from faithful *amenable* traces.
- `C*_r(Gamma)` is QD only if `Gamma` is amenable (Rosenberg; standard, not re-read).
  The canonical trace of a nonamenable group is not amenable.
- So an MF embedding of `C*_r(SL_4(Z))` admits no ucp lift, since a ucp lift would make
  it QD.  The same holds for `C*_r(F_2)`.

*Firewall.*  `C*_r(F_2)` is MF: it is PMF (Haagerup--Thorbjørnsen, [HT05] in MdlS p. 2).
So no property that `F_2` shares can decide the question: not nonamenability, non-QD,
exactness, trace uniqueness, or failure of ucp liftability.  A decision has to use
(T)-type rigidity or the arithmetic of `SL_4(Z)`.

**2. Kazhdan projections.**  Gives nothing in the reduced algebra.
- For infinite `Gamma` with (T), the Kazhdan projection `p in C*(Gamma)` maps under
  `lambda` to the projection onto the invariant vectors of `l^2(Gamma)`, which is `0`.
  No projection-based rigidity survives in `C*_r`.
- MdlS, p. 2: "as far as we know there is no direct relation" between property (T) and
  PMF.
- An obstruction from (T) alone would refute `infinite-kazhdan-group-with-mf-reduced-cstar`
  for every infinite Kazhdan group at once.

**3. Traces.**  No obstruction.  (Standard, not re-read: the amenable radical of
`SL_4(Z)` is `{+-I}` by Margulis's normal subgroup theorem, and by
Breuillard--Kalantar--Kennedy--Ozawa traces on `C*_r` vanish off the amenable radical.)
- The trace pulled back from `Q_k` is therefore determined on `{+-I}`, and the lifts
  converge in trace to the regular character.
- Genuine sequences with this property exist, namely congruence quotients, since
  `SL_4(Z)` is residually finite.  So traces cannot obstruct.

**4. Matricial stability (existing route).**  Live, but conditional:
`sl4z-reduced-not-mf-from-matricial-stability`.
- Dadarlat's cohomological obstruction needs `H^(2k)(SL_4(Z); Q) != 0`.  Its absence is
  recorded as unverified in `sl4z-matricially-stable`.
- A consequence derived here: if a matricially stable group has MF full algebra, then
  that algebra is RFD (lift a faithful `C*(Gamma) -> Q_k` and correct it to genuine
  representations).
- Bekka (Forum Math. 1999; not re-read) states that `C*(SL_n(Z))`, `n >= 3`, is not RFD.
  If so, stability of `SL_4(Z)` also makes `C*(SL_4(Z))` non-MF, so this route demands
  two non-MF theorems at once.

**5. The corona reduction (this lane, Section 4 below and part 2).**  Live.  It asks
only that the block `SL_2(Z)` Laplacian have norm four in every *corona*
representation.  This is weaker than stability and is a robust form of MdlS Theorem 1.1.

**6. Leverage already in the repo.**
- `matricially-stable-overgroups-of-sl4z-are-not-reduced-mf`: lift, correct, meet the
  fixed vector.
- `mdls-obstruction-is-affine-mechanism-plus-level-matching`: which steps of MdlS live in
  the affine group.
- `sl3z-pmf-iff-affine-kazhdan-group-pmf`, `sl3z-has-no-invariant-vector-witnesses`: the
  `d = 3` side.
- `countable-group-mf-conventions`, `corona-defect-is-not-uniform`: MF conventions and
  pointwise defect.
- `amenable-rep-of-kazhdan-has-fd-subrep`: Bekka--Valette.

None of these produces a non-genuine asymptotic homomorphism of `SL_4(Z)`, or an
approximate invariant vector for one.

## 4. The corona reduction

Notation: `z = S + S^-1 + T + T^-1` for the block `SL_2(Z)` of `SL_4(Z)`, and
`Q_k = prod_n M_(k_n) / sum_n M_(k_n)`.

**(C) `sl4z-corona-representations-have-block-sl2-norm-four`.**  Every unital
*-homomorphism `pi : C*(SL_4(Z)) -> Q_k` has `||pi(z)|| = 4`.

**Theorem 1: (C) implies the root, for every overgroup.**  Let `Gamma >= SL_4(Z)`, and
suppose `iota : C*_r(Gamma) -> Q_k` is an injective *-homomorphism.
1. *Make `iota` unital.*  `iota(1)` is a projection.  Lift it to projections `P_n` of rank
   `r_n` (lift to a self-adjoint element and apply functional calculus).  Then
   `iota(1) Q_k iota(1) = Q_r`, so we may take `iota` unital into `Q_r`.  `Q_r != 0`
   because `iota` is injective.
2. *Apply (C).*  `pi = iota o lambda_Gamma o (C*(SL_4(Z)) -> C*(Gamma))` is a unital
   *-homomorphism into `Q_r`, so `||pi(z)|| = 4`.
3. *Contradiction.*  `iota` is isometric, so `||pi(z)|| = ||lambda_Gamma(z)||`.
   `lambda_Gamma` restricted to `SL_2(Z)` is a multiple of `lambda_SL2(Z)`, so this norm
   is `< 4` by Kesten, since `SL_2(Z)` is nonamenable.

**Theorem 2: (C) is a robust form of MdlS.**  (C) holds iff for every `eta > 0` there are
a finite `F subset SL_4(Z)` and `delta > 0` such that every `phi : SL_4(Z) -> U(k)`,
`k >= 1`, with `||phi(gh) - phi(g) phi(h)|| < delta` for `g, h in F`, satisfies
`||phi(S) + phi(S)^* + phi(T) + phi(T)^*|| >= 4 - eta`.
- *Robust form implies (C).*  Take a corona representation, and unitary lifts
  `phi_n(g)` of `pi(g)`.  The defect on any fixed finite set vanishes eventually, and
  `phi_n(S^-1) - phi_n(S)^* -> 0`.  So `limsup_n` of the coordinate norms is `>= 4 - eta`
  for every `eta`, and this `limsup` is the corona norm.
- *(C) implies robust form.*  Suppose it fails at some `eta`.  Choose counterexamples
  `phi_n` for finite sets `F_n` increasing to `SL_4(Z)` and `delta_n -> 0`.  They define
  a homomorphism `SL_4(Z) -> U(Q_k)`: the defect of each fixed pair vanishes eventually,
  and `phi_n(e) -> 1` because `phi_n(e)^2 - phi_n(e) -> 0` for a unitary.  This extends
  to `C*(SL_4(Z))`, with `||pi(z)|| <= limsup ||phi_n(z)|| <= 4 - eta`, contradicting (C).

**Theorem 3: matricial stability implies (C).**  Correct the lifts to genuine
representations `rho_n` with `||phi_n(g) - rho_n(g)|| -> 0` pointwise.  Then
`pi(z) = [(rho_n(z))]`, and `||rho_n(z)|| = 4` whenever `k_n >= 1` by MdlS Theorem 1.1.
So (C) is at most as strong as the old crux `sl4z-matricially-stable`, and it still
implies the root.

**Every corona representation is a genuine representation.**  Represent `Q_k`
faithfully on a Hilbert space `H`.  Then `pi` becomes a genuine unitary representation
`sigma` of `SL_4(Z)` with `||sigma(x)|| = ||pi(x)||`.  So statements about arbitrary
unitary representations apply to corona representations.  Part 2 uses this twice:
- the torus dichotomy (norm four whenever the column unipotent spectrum is not all of
  `T^3`);
- the firewall on MdlS Step 3 at non-torsion characters.
