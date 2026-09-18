---
rg: 2
id: full-mf-radical-abelianized-cover-is-not-mf
kind: claim
title: The free abelianized cover of a nontrivial full-MF-radical group is not MF
distinct_from:
  free-abelianized-cover-reflects-mf: that is descent (D) for every presentation of every group; this is only its contrapositive for bases with FULL MF radical, where every corona homomorphism of the base is trivial and not merely non-injective.
  free-abelianized-cover-fd-radical-is-commutator: that computes the exact finite-dimensional radical of the same cover, a larger radical whose total collapse is compatible with MF; this asks for the operator-norm corona radical.
  abelianized-cover-commutator-is-finitely-generated-perfect: that is group theory of the commutator core; this is the analytic non-MF statement.
artifacts:
  - research/abelianized-cover-injective-corona-model-carries-nonzero-twist.md
  - research/implemented-corona-actions-of-countable-groups-are-unconstrained.md
  - research/dummy-abelianized-cover-df-splits-regular-trace-and-shadow.md
  - research/relation-lamp-wreath-is-mf-with-nontrivial-fd-radical.md
  - research/stable-abelianized-cover-is-subgroup-monotone.md
  - research/abelianized-cover-df-forces-cofinite-congruence-df.md
  - research/abelianized-cover-mf-radical-is-union-of-local-cover-radicals.md
  - research/local-commutator-cover-derived-series-stops-at-one.md
  - research/local-commutator-cover-bounded-degree-linear-images-are-abelian.md
---

**OPEN.**  Let `F` be free of finite rank, `R` normal in `F`, and suppose
`G = F/R != 1` has `Rad_MF(G) = G`.  Set `E = F/[R,R]` and `M = R/[R,R]`.
The claim is that `E` is not MF:

```text
every homomorphism rho : E -> U(prod M_(k_n) / (+) M_(k_n)) has nontrivial kernel.   (DF)
```

The route `property-t-free-seed-via-leavitt-abelianized-cover` uses only one
instance: the finite presentation that
`full-mf-radical-has-fp-cover-same-generators` gives over
`St_20(L_(F_2)(1,2))`.

`free-abelianized-cover-reflects-mf` implies `(DF)`.  The converse is not
claimed.

**Known structure.**

- A nontrivial full-MF-radical group is infinite, because finite groups are MF.
- For infinite `G`, the relation module `M` is a nontrivial `G`-module with no
  fixed vectors.  It embeds in `ZG^n` by the Lyndon sequence, and
  `(ZG^n)^G = 0`.  Moreover `M != 0`, since otherwise `R` is perfect, hence
  trivial, and then `G` is free, hence MF.
- So `[E,M]`, which is the image of `I_G M`, is a nontrivial normal subgroup
  of `E`.

## Attempts

- **Untwisting dichotomy (2026-09-18).**
  `abelianized-cover-injective-corona-model-carries-nonzero-twist` proves:
  - if a model `rho` has zero pushed class
    `rho_* xi in H^2(G; U(C*(rho(M))))`, then `rho` kills `[E,M] != 1`;
  - so an injective model of `E` must act nontrivially on the spectrum of
    `C*(rho(M))`, and it must carry a nonzero abelian twist class there.

  This does not close `(DF)`.  Nothing shows that a nonzero class cannot occur,
  and the nonabelian-coefficient form of the dichotomy is a tautological
  restatement of `rho([E,M]) = 1`.
- **Rigidity of the induced action is false as a principle (2026-09-18).**
  `implemented-corona-actions-of-countable-groups-are-unconstrained` realizes
  every nontrivial countable group, full MF radical or not, by a nontrivial
  action on a commutative subalgebra `C(X)` of a matrix corona.  The action is
  implemented by unitaries whose cocycle lies in the relative commutant.
  - Any proof of `(DF)` must therefore use the finer data of an actual model:
    the cocycle takes values in `U(C*(rho(M)))` itself, and it is the image of
    the relation module.
  - A counterexample must realize such a cocycle exactly with commuting
    conjugates.  The Bernoulli construction does not: its permutation
    holonomy lies only in the commutant.
- **Regular-trace / shadow split for the dummy presentation (2026-09-18).**
  `dummy-abelianized-cover-df-splits-regular-trace-and-shadow` proves the
  following for the dummy cover `E_z`, where `C(M_z) = M_z`.
  - Every nontrivial normal subgroup of `E_z` meets `M_z`.
  - `delta_e` is an operator-norm MF character of `E_z` iff the shadow
    residual `S(E_z)` is trivial, iff every nonzero `m in M_z` has some
    operator-norm MF character with `tau(m) != 1`.  The proof averages the
    witnesses, Diracizes the average, and uses the self-centralizing kernel
    to force the scalar kernel to be trivial.
  - So DF for `E_z` is equivalent to `(REG)` and `(SH)`:
    - `(REG)`: no operator-norm microstates of `delta_e`.  These would come
      with `C(hat M_z)` at Haar trace, full spectrum, and a mixing,
      essentially free dual action.
    - `(SH)`: `S(E_z) != 1` implies `Rad_MF(E_z) != 1`.
  - DF for `E` implies DF for `E_z`, because `E` is a retract of `E_z`.

  **Where it dies.**
  - The attempt to get more than this from a surviving `[E,M]` element fails
    at the renormalized trace `tr(y_n)/tr(a_n)`.  When `tr(a_n) -> 0` it is
    not a corona invariant: lift changes and operator-norm defects are
    `o(1)`, not `o(tr a_n)`.  So tracially blind models such as
    `rho (+) 1_(N_n)` cannot be handled by trace renormalization.
  - Handling those models is exactly `(SH)`.
  - `mf-vs-tracial-radical-strict-gap` shows `(SH)` is not formal for
    abelian-by-`G` lamp extensions.
  - Neither `(REG)` nor `(SH)` is proved.
- **Dummy lamp calibration: every argument that ignores `[R,R] = 1` dies at an
  MF group (2026-09-18).**
  `relation-lamp-wreath-is-mf-with-nontrivial-fd-radical` works with the
  dummy presentation `<X, z | R, z>`.
  - Its cover is `E' = ZG x| E`.  It contains `E`, it is torsion free, and it
    suffices for the route.
  - `E'` is the quotient `W/[R,R]` of the lamp group `W = ZG x| F`.
  - `W` is MF, using Hall-separable windows `H_L = <R cap S_L>` and the
    permutation models on `F/K_L`.
  - Yet every nonzero element of `I_G ZG`, for example `[w,z]` with
    `w notin R`, lies in the finite-dimensional radical of `W`, over every
    field.  In the models, `||[w,z] - 1|| = 2`.

  So any proof of `(DF)` for `E'` has to use `rho([r,r']) = 1` among the
  relator images.  Their exact commutation with the lamps, the module
  structure, the finite-dimensional radical and the absence of finite
  quotients of `G` all hold in the MF group `W` and cannot suffice.

  Side results for this lane, not written as separate nodes:
  - **Linear images are abelian.**  Every image of `E` or `E'` in `GL_d(K)`,
    over any field, is abelian.  Its finite quotients are abelian, because
    `G` has none, and Malcev applies.
  - **Exact permutation models reduce to finite quotients.**  An exact
    permutation (LEF-type) corona model of `E` amounts, once the windows are
    reindexed, to a sequence of finite quotients `P_L` of `Gamma_L = F/<<[r,r'] : r,r' in R cap S_L>>`.
    For a finitely presented `G`, `P_L` is the normal closure of the images of
    the defining relators.
  - **Diameter lemma.**  If `L >= 2 diam(P_L) + max|r_j|`, then `P_L` is
    generated by images of `R cap S_L`, which pairwise commute, so `P_L` is
    abelian and the model kills `[E,E]`.  A surviving exact permutation model
    therefore needs `diam(P_L) >= (L - max|r_j|)/2`.

  Open need: finite quotients of `Gamma_L` with `diam(P_L)` growing linearly
  in `L`, in which `[w, r_1]` survives, or a proof that none exist.  For the
  St_20 presentation that would decide `(DF)` within exact permutation models.
- **Presentation-free reduction and subgroup monotonicity (2026-09-18).**
  `stable-abelianized-cover-is-subgroup-monotone` (ESTABLISHED, pure group
  theory) proves the following.
  - `E_(G,X,k) = ZG^k x| E_(G,X)`.
  - Tietze invariance: `E_(G,X,|Y|) = E_(G,Y,|X|)`.  So "stably DF", meaning
    some dummy cover is not MF, does not depend on the presentation.
  - For a finitely generated `H <= G` of infinite index, `P^(-1)(H)` is `H`
    plus `aleph_0` dummies after a basis slide.  So every dummy cover of `H`
    embeds in `E_(G,X)` for EVERY `X`.
  - Stable DF is a commensurability invariant.
  - `E` splits over `H <= G` iff `H` is free.  This uses the Fox projection
    and Stallings--Swan.
  - Amenable and free `H` are never stably DF.

  What the route uses from `(DF)` is exactly "the finitely presented cover
  `G~` of `St_20(L)` is stably DF".  That now follows from stable DF of any
  one finitely generated subgroup of `G~`, of any index, which need not have
  full radical.  If the index is infinite, it gives `(DF)` for every
  presentation with no dummies.

  **Dead as a class.**  Approaches that lift a non-MF subgroup of `G` into
  `E` die at Step 5: nothing non-free lifts.

  **Remaining gap between the invariant and a fixed presentation.**  Can one
  dummy lamp destroy MF?  That is, is `ZG x| E` non-MF while `E` is MF?

  **Not done.**  Stable DF is not proved for any group.  The contrapositive
  says a DF counterexample at `G` makes the stable cover of every finitely
  generated infinite-index subgroup of `G` MF.
- **Congruence gate: DF forces the torsion quotients to be non-MF
  (2026-09-18).**
  `abelianized-cover-df-forces-cofinite-congruence-df` (ESTABLISHED) proves
  the following, with `H_N = E/NM = F/[R,R]R^N`.
  - The Lyndon embedding is pure: `M cap N ZG^n = NM`, so `M/NM` embeds in
    `(Z/N)[G]^n`.  A nonzero `m` lies in `NM` iff `N` divides its content
    `c(m)`, the gcd of its integer coefficients.
  - If `H_N` is MF, then `Rad_MF(E) <= NM`.  If `H_N` is MF for infinitely
    many `N`, then `E` is residually MF, hence MF, and DF fails.
  - The set of `N` with `H_N` MF is closed under `lcm`.
  - Under DF there is some `c >= 1` such that `H_N` is non-MF for every `N`
    not dividing `c`.  In particular `F/[R,R]R^p` is non-MF for all but
    finitely many primes `p`.

  **What this changes.**
  - A counterexample search may restrict to models whose kernel image has
    exponent `N`, for infinitely many `N`.  There the joint spectrum of the
    kernel image is totally disconnected, and ranks of lifted projections
    are exact corona invariants.  The renormalization death recorded above
    does not occur in that setting.
  - Non-MF-ness of `H_p` for all large `p` is a necessary condition for DF
    that can fail on its own.  It is a statement about groups whose kernel
    has exponent `p`.

  **Where it stops.**
  - The converse is open.  "Congruence lifting", meaning that an MF cover
    has infinitely many MF congruence quotients, would make DF equivalent to
    finiteness of the MF set.
  - Rounding the kernel spectrum to `N`-th roots of unity is not
    multiplicative.  This is the `K_1` / Bott obstruction for almost-commuting
    unitaries.  So it does not prove congruence lifting.
  - The rank-ratio measures on invariant clopen subsets of the spectrum of an
    `H_N` model are genuine invariants, but they do not obstruct.  The dual
    action is a factor of the shift on `((Z/N)^n)^G`, which carries Bernoulli
    measures.

  **Dead in this lane, not written as nodes.**
  - **Near-fixed spectral filtration.**  The idea is to cut `C*(rho(M))` at
    distance levels from the trivial character and force a `G`-invariant
    level.  It dies at the pigeonhole.  Excluding a collapse needs about
    `k_n` levels, but uniform stability of `G` supplies only `O(log 1/delta)`
    geometric thresholds.  In the exponent-`N` case the thresholds are
    linear, but the number of levels is still not controlled.
  - **Virtual extraction.**  Passing to a finite-index torsion-free or
    residually finite piece is impossible.  A nontrivial full-radical group
    has no proper finite-index subgroup, because finite groups are MF.
- **Finitary form of DF via local-commutator covers (2026-09-18).**
  `abelianized-cover-mf-radical-is-union-of-local-cover-radicals`
  (ESTABLISHED) proves a continuity theorem.  For `F` free of finite rank,
  normal subgroups `K_L` increasing to `K`, and `H_L = F/K_L ->> H = F/K`,
  it gives `Rad_MF(H) = U_L pi_L(Rad_MF(H_L))` as an increasing union.
  - The proof amplifies to `||sigma(g) - 1|| >= sqrt 3` using tensor powers.
    Then it chooses corona models of the `H_L` diagonally, so that they
    assemble into a single model of `H`.
  - If each `K_L` is finitely normally generated, it also gives
    `H` LEF iff `U_L pi_L(fr(H_L)) = 1`.

  Applied to `N_L = <<[u,v] : u,v in R cap S_L>>`, with `U N_L = [R,R]`:
  - `(DF)` is equivalent to `(DF_L)` for ONE finite `L`.  `(DF_L)` says that
    the finitely presented group `Gamma_L = F/N_L` has an MF-radical word
    `w in [F,F] \ [R,R]`.
  - `(DF_L)` is monotone in `L`.  Its certificate involves only finitely
    many commutation relations.
  - `E` is LEF iff no word outside `[R,R]` lies in the finite residual of
    any `Gamma_L`.

  **What this changes.**
  - `(DF)` is now a statement about a single finitely presented group with
    `Gamma_L^ab = Z^|X|`, which is therefore not Kazhdan.  Previously it was
    a statement about the infinitely related group `E`.
  - Each `(DF_L)` is a prerequisite that can fail on its own.
  - The exact-permutation obstruction recorded above becomes a question
    about residual finiteness of finitely presented groups.  Non-abelian
    finite quotients of `Gamma_L` have diameter `>= (L-c+1)/2`, and their
    commutator subgroup is `phi([R,R])`.
  - Explicit cofinal presentations avoid the word problem of `G`.  Take
    `Gamma'_k = <X | [v r_i v^-1, v' r_j v'^-1] : |v|,|v'| <= k>`.  Here
    `U N'_k = [R,R]`, and `Gamma_(2k+c) ->> Gamma'_k`.
  - Spark: if `(DF_L)` holds, then `Gamma_L / Rad_MF` is a quotient to aim
    for.  If `Rad_MF(Gamma_L)` itself is nontrivial, `Gamma_L` is a
    finitely presented, non-Kazhdan, non-MF group written down directly from
    the presentation of `G`.

  **Where it stops.**  No `(DF_L)` is proved, and no `Gamma_L` is shown to be
  residually finite on `[F,F] \ [R,R]`.  The finitary form moves the
  difficulty but does not remove it.  The analytic content of `(DF)` is
  unchanged.

- **Solvable models of the local covers are blind, plus four analytic dead
  ends (2026-09-18).**
  - **Established.**  `local-commutator-cover-derived-series-stops-at-one`.
    - There is one threshold `L_1` such that, for all `L >= L_1`,
      `Gamma_L'` is generated by `d <= r+s+r^2` words and is perfect.
    - The proof lifts the finitely many identities of `E` that say
      `T = E'` is finitely generated, normal and perfect.  The correcting
      words lie in `[R,R] = U N_L`, so they all lie in a single `N_(L_1)`.
    - Consequently, every homomorphism from `Gamma_L` to a solvable group
      factors through `Z^r`.  Nonabelian finite quotients have nonabelian
      simple sections.
    - This kills, in both directions, every solvable test object for
      `(DF_L)` or its LEF shadow.  That includes metabelian Fox-calculus
      models, wreath and lamplighter models over abelian bases, and nilpotent
      and `p`-group quotients.
  - **Dead: saturation extraction of an M-fixed corner.**
    - Countable saturation of `Q` gives a nonzero projection `p` with
      `rho(m) p = p` for all `m in M`, provided the trivial character lies
      in the spectrum of `rho|_M`.
    - `D = {a : rho(m)a = a = a rho(m)^*}` is hereditary, and `G` acts on it
      by a multiplier representation.
    - It dies at the step "find a `G`-invariant projection in `D`".  Nothing
      provides one.  The model `rho (+) 1` shows that the M-fixed part can be
      exactly the E-fixed part, which gives no contradiction.
  - **Dead: `rho (x) conj(rho)`.**  Its M-fixed part is the Koopman
    representation on `C(X)` only in normalized 2-norm, not in operator
    norm.  This is the tracial versus operator-norm gap already recorded as
    (SH).
  - **Dead: the (REG) branch through reduced algebras.**
    - A `delta_e`-model forces `X` to be the full dual with Haar measure.
      Then `C*(rho(E))` maps onto `C*_r(E)`, which maps onto `C*_r(G)` at the
      trivial character.
    - There is no contradiction, because quotients of MF algebras are
      unconstrained and `C*_r(G)` is itself not MF.
  - **Dead: the twist class on the full dual.**  Evaluation at points splits
    `H^2(G; M) -> H^2(G; C(dual M, T))`, so that map is injective and the
    twist is not killed there.  An obstruction must use a proper closed
    invariant `X`.
  - **Still open: whether `E` is LEF.**
    - `G` LEF implies `E` LEF, via Magnus into `(Z/N)^n wr Q_L`.  This is
      vacuous here, because `G` has no finite quotients.
    - By the established item, any finite witness is a non-solvable quotient
      of some `Gamma_L` with `L >= L_1`.

  **Where it stops.**  No corona statement about `Gamma_L` follows from the
  group theory.  `(DF)` remains OPEN.  The remaining finite-side question is
  residual finiteness of `Gamma_L` on `[F,F] \ [R,R]` through quotients with
  nonabelian simple sections.
- **Bounded-degree linear models of the local covers are blind
  (2026-09-18).**
  - **Established.**  `local-commutator-cover-bounded-degree-linear-images-are-abelian`.
    - For each degree `n` there is a threshold `L(n) >= L_1` with the
      following property.  For `L >= L(n)`, every homomorphism
      `Gamma_L' -> GL_n(A)`, over every commutative ring `A`, is trivial.
      So every `n`-dimensional representation of `Gamma_L` has abelian
      image.
    - The proof starts with the universal degree-`n` representation of `T`
      over `O/I_inf`.  Malcev kills it: finitely generated commutative rings
      are residually finite, and `T` has no finite quotient.  So the
      `n^2 d` generic-matrix entries `y - delta` lie in `I_inf`.  These
      finitely many elements already lie in one `I_L`.
  - **Consequence for finite quotients.**  Every nonabelian finite quotient
    of `Gamma_L` maps onto a minimal one, `P <= Aut(S) wr Sym(k)`, with:
    - `P' = S^k` the unique minimal normal subgroup;
    - `C_P(P') = 1`;
    - an abelian regular action on the factors;
    - `m(S) > n`.
  - **Dead as a class, in both directions.**  None of the following can
    witness or refute LEF of `E`:
    - finite quotients of bounded linear degree, such as `SL_k(Z/N)` with
      `k` bounded, `PSL_2(q)`-families, groups of Lie type of bounded
      rank, and `Alt(k)` with `k` bounded;
    - bounded-dimensional unitary or projective models;
    - fixed-alphabet wreath and cellular-automaton models `A_0 wr_X B` over
      abelian `B` of any size.
  - **Dead sub-idea, not written as a node.**  One could try to exclude
    fixed-alphabet wreath models through periodic points of a `Z^r`
    subshift of finite type.  That is subsumed, because item 5 of the claim
    kills them directly.  Unrestricted limits `A_0^(Z^r) x| Z^r` of such
    models kill `T`, since `T` has no finite quotient, so no aperiodic
    limit can survive either.
  - **Dead sub-idea: E' finitely presented, hence not LEF.**  If `T` were
    finitely presented, then so would be `E`, as an extension of `T` by
    `Z^r`.  For infinite `G` this contradicts Baumslag--Strebel--Thomson,
    by which `F/R'` finitely presented forces `F/R` finite.  That theorem
    is imported from memory, without a verbatim citation.
  - **Dead sub-idea: stabilizing the chain of relator subgroups.**  Let
    `A_l = <phi(R cap S_l)>` in a finite quotient `P`.  Each `A_l` is
    abelian for `l <= L`.  If `A_l` stabilizes, it is normal, so `P` is
    abelian.  So the chain must strictly increase, which bounds `|P|` below
    only polynomially in `L`.  This is not a contradiction, because `|P|` is
    not bounded in terms of `L`.

  **Where it stops.**  The surviving finite witnesses are exactly the
  quotients whose minimal nonabelian quotients have socle factor `S` with
  `m(S) -> infinity`.  By the classification of finite simple groups
  (imported, not verified here), these are alternating groups of unbounded
  degree or classical groups of unbounded rank.

  Open need: either a nonabelian quotient of `Gamma_L` with `Alt(m)`-socle,
  `m` growing with `L`, in which a word of `[F,F] \ [R,R]` survives, or an
  argument that controls permutation-type quotients of unbounded degree.
  `(DF)` remains OPEN.

- **Fixed-point localization of the kernel spectrum is blind (2026-09-18,
  swarm-0917-w10-w10-ptm-last1, stability-approximation).**  ESTABLISHED
  class kill and stripping lemma:
  `abelianized-cover-isolated-fixed-spectral-point-is-scalar`.

  **Result.**  In any corona model `W` of `E`, let `chi` be an isolated,
  `G`-fixed point of the kernel spectrum `X` that factors through the
  exponent-sum map.  Then its indicator `p in C*(W(M))` commutes with
  `W(E)`, and `W(e) p = lambda(e) p` for one character `lambda` of
  `E^ab = Z^n`.

  **Proof.**  Untwist by a character of the free group; the corner is then
  a model of `G`, and the full radical kills it.

  **Consequences.**  Scalar padding at such points (for example `1_N` with
  isolated trivial character) can be stripped without changing what the
  model detects on `E'`.  For superperfect `G` every fixed point is
  liftable.

  **Where it dies.**  `M` is free abelian, so `hat M` is connected.  The
  regular models that `(REG)` must defeat have `X = hat M`, which has no
  isolated points and no nontrivial clopen invariant sets.  Fixed-point
  localization in the norm algebra is therefore vacuous against `(REG)`,
  and wherever it succeeds it yields only a character, which is consistent
  with MF.  Making it work at a non-isolated point needs a norm-level
  invariant neighborhood projection, which is the spectral-gap step of
  `commutant-projection-extraction`.

  **Residual.**  Isolated fixed points that are not liftable give
  projective corona models of `G` with cocycle class `chi|H_2(G)`.  These
  are not decided.
