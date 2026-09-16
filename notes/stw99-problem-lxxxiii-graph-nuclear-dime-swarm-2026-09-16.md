# STW Problem LXXXIII (graph C*-algebras, nuclear dimension one): swarm log 2026-09-16

This log covers the root `stw99-problem-lxxxiii-graph-nuclear-dimension`, which
was locked by `swarm-stw99-problem-lxxxiii-graph-nu`.  The outcome is partial
progress.  The problem stays open.

## Setup

The stw99 ledger root had no incoming routes, while the substantive work lives
under the older root `stw83-problem-lxxxiii-graph-nuclear-dimension`, which
states the same proposition.  The established claim
`stw83-two-non-k-extension-directions-remain-open` locates the frontier at the
two "?" entries of the Evington--Ng--Sims--White table (arXiv:2409.12872v2,
remark after Prop. 5.1).  Both have a single nontrivial gauge-invariant ideal
that is a circle field `C(T) tensor K`:

* (i) a Kirchberg quotient;
* (ii) a circle quotient.

The repository already had `1 <= dim_nuc <= 2` for the canonical family of
(ii).  It had nothing explicit for (i).

## Literature gate (arXiv API queries and e-print sources, 2026-09-16)

No resolution of LXXXIII, or of either ENSW "?" entry, was found.

* ENSW, arXiv:2409.12872v2.  I read the TeX source: the table, the pictures,
  the convention at the graph-algebra definition, and Prop. 5.1.
* S. Evington, arXiv:2012.03650v3.  I read the TeX source: Theorem 1 verbatim,
  the fullness remark, the lifting lemma, and the proof outline.
* Brake--Winter, arXiv:1808.09647 (Toeplitz algebra has nuclear dimension
  one).  Listing only.
* Ruiz--Sims--Tomforde, arXiv:1312.0507.  Listing only.
* Faurot--Schafhauser, arXiv:2310.15073.  Per the abstract, countable graphs
  with Condition (K) have `dim_nuc <= 2`, with a sufficient condition for
  `dim_nuc <= 1`.  (Referee correction: the log first said "`<= 1`" for all
  finite Condition (K) graphs.)  The models `F_(n,k)` below fail Condition (K),
  because `v` has a single loop.  Listing and abstract.
* an Huef--Williams, arXiv:2412.10241.  Stably finite graph algebras, not
  applicable.  Abstract.
* D. Pask, arXiv:2607.27691 (30 Jul 2026).  Purely infinite k-graph algebras,
  not applicable.  Abstract.
* Easo et al., arXiv:2003.06314 (Cuntz--Toeplitz algebras).  Abstract.
* Schafhauser--Tikuisis--White, arXiv:2506.10902.  The problem text could not
  be extracted (no pdftotext), so the wording of Problem LXXXIII is taken from
  the existing root node and is **unverified here**.
* Bosa--Gabe--Sims--White, arXiv:1906.02066, Theorem A (`O_infinity`-stable
  algebras have nuclear dimension one).  Used only as cited inside Evington's
  source; not fetched, **unverified**.
* Winter--Zacharias (2010) permanence properties and Winter (2009)
  order-zero lifting.  Numbers checked only against citations in the
  Evington and ENSW sources.

## What was proved

Everything is in `research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md`.

1. **Theorem 1**, the claim `stw83-constant-symbol-pullback-one-extra-colour`.
   * *Statement.*  Let `K subseteq D subseteq B(H)` be separable with
     `d = dim_nuc(D/K)` finite, and let `X` be compact metrizable of dimension
     `n`.  Then `A_X(D) = C(X,K) + D tensor 1` satisfies
     `max(n,d) <= dim_nuc <= max(n,d)+1`.
   * *Proof, first half.*  It is a Brake--Winter three-piece decomposition.
     The nested finite-rank quasicentral units are built with Mazur's lemma.
     The transition band is constant, so it lies in `M_R tensor 1`.  The
     quotient colours are made exactly order zero in the orthogonal corner
     `C_i` by lifting through `prod C_i / sum C_i`.
   * *Proof, second half.*  Those quotient colours share colours with the
     inner corner `M_R(C(X))`, and the band takes one extra *-homomorphism
     colour.
   * *Comparison.*  The generic extension estimate gives `n+d+1`.  No
     `O_infinity`-stability and no fullness is needed.
2. **Models for entry (i)**, the claim `stw83-circle-ideal-cuntz-quotient-dimension-two-bound`.
   * *The graph.*  `F_(n,k)` has `n` loops at `u`, one loop at `v`, and `k`
     edges `u -> v`.
   * *The isomorphism.*  A gauge-invariant uniqueness argument, using the
     rotation-twisted action `beta_lambda(Phi)(t) = U_lambda Phi(lambda t) U_lambda^*`,
     identifies `C*(F_(n,k))` with `C(T,K) + D_0 tensor 1`, where
     `D_0/K = O_n`.
   * *The bound.*  So `1 <= dim_nuc <= 2`.  This bound also follows from
     Evington's Theorem 1, because unital extensions with simple quotient are
     full.  That second proof is recorded as a direct literature-import route,
     so the new value is the model and an `O_infinity`-free proof, not the
     bound.
3. **Splitting**, the claim `stw83-cuntz-circle-graph-splits-iff-k-equals-n-minus-1`.
   * *Index.*  The loop row `[T_1..T_n]` is Fredholm of index `n-k-1`.
   * *Criterion.*  A *-homomorphic section with complementary rank `r`
     forces `n-k-1 = (n-1)r`, so the extension splits iff `k = n-1`.
   * *The minimal model.*  For `k = n-1`, rank-one corrections give Cuntz
     isometries, so ENSW's smallest model `F_(2,1)` is a split extension
     `C(T,K) + rho(O_2) tensor 1`.
   * *K-theory.*  The six-term boundary maps vanish for every `k`.  But
     `K_0` is not blind to `k`: it records `k mod (n-1)` (referee
     correction; see the Referee section).  The index is finer than `K_0`.
4. **Alternative route for entry (ii).**  The route
   `stw83-canonical-circle-two-bound-via-constant-symbol` re-derives
   `dim_nuc(A_N) <= 2` from `A_N = A_T(T_N)` and `T_N/K = C(T)`.  It does not
   use the connector-corner claim.
5. **Connecting the roots.**  The route `stw99-lxxxiii-from-stw83-root` points
   the ledger root at the stw83 sub-graph.

Script: `experiments/stw99-constant-symbol-pullback-2026-09-16/check_fnk.py`.
It checks the relations, matrix units, gauge covariance, kernel and cokernel
counts, and the split Cuntz relations exactly on truncations, for
`2<=n<=4`, `1<=k<=3` and `L` in `{2,3}`.  All checks passed.

## The ENSW picture versus the table

The second minimal picture in ENSW v2 has two loops at `x`, one loop at `y`,
and an edge `y -> x`.  With the paper's own convention (`s_e^*s_e = p_(r(e))`,
hereditary = forward closed), `{x}` is the ideal, and this is the Kirchberg
ideal / circle quotient entry, which their Corollary settles.  The unknown
entry needs the edge `x -> y`.  The pictures match the table under the
Raeburn convention.  The first picture, a single loop at each end, is
unaffected.  Anyone attacking entry (i) should use `F_(2,1)` as defined above.

## The hinge (unchanged, but now shared by both entries)

The colour ledger is Section 8 of the artifact.

* In the constant-symbol scheme, the quotient colours merge with the inner
  corner for free.
* The band colour meets both the inner corner `E_i` and the outer corner
  `C_i`, so it merges with neither.
* When `X` is a point, the inner corner needs one colour and can be moved
  wholesale.
* When `X = T`, it needs two colours, and only one of them can be pushed off
  the band.

This looks like the same obstruction as `stw83-plateau-buffer-recolouring-hinge`.
The no-go results `stw83-circle-unitary-order-zero-plus-constants-gap` and
`stw83-commuting-cone-two-colour-firewall` are expected to transfer to the
coefficient corner of entry (i), but that transfer was not written out or
checked.  Within this scheme, the Kirchberg quotient changes only the outer
colours.  This is a heuristic colour count, not a no-go theorem.

## Dead ends and cautions

* **K_0 unit class.**  An earlier idea used a nonzero class of the unit in
  `K_0` to rule out splitting.  For `F_(2,1)`, `K_0 = Z^2/<(1,1)>` and
  `[1] = 0`, so that argument is wrong.  The extension does in fact split.
* **Splitting does not help.**
  * The section `rho(O_n) tensor 1` does not commute with `C(T,K)`, so
    centralizing-section results (compare
    `stw82-af-split-centralizer-extensions-obey-maximum`, which also needs an
    AF ideal) do not apply.
  * `C(T,K)` is stably finite, so the algebra is not `O_infinity`-stable,
    and BGSW does not apply.
* **Theorem 1 cannot give dimension one by itself.**  As the decomposition is
  set up, every term of its colour count is used.  Dropping the band colour
  would need the missing recolouring.
* **Generalization to other graphs.**  Extending the pullback model to finite
  graphs whose ideal is a union of exitless cycles and whose quotient is
  arbitrary looks routine: put the `t`-dependence on one edge of each cycle.
  It was not written out.  If it works, Theorem 1 would bound such towers by
  `max(1,dim_nuc(quotient))+1`, with no `O_infinity`-stability assumption.
  (Referee: the original text said `dim_nuc(quotient)+1`, which is wrong for
  AF quotients.  Several cycles also need a constant-symbol model over a
  disjoint union of circles, which was not checked.  Unverified.)

## Referee (2026-09-16)

**What I checked.**
* I read all twelve solver files in full, together with the committed nodes
  they touch: both LXXXIII roots, `stw83-canonical-circle-is-constant-symbol-pullback`,
  `stw83-canonical-circle-toeplitz-dimension-two-bound`,
  `stw83-two-non-k-extension-directions-remain-open` and
  `stw83-coefficient-toeplitz-three-colour-proof`.
* **Theorem 1**, the three-piece constant-symbol decomposition (artifact
  Sections 1--4).
  * I checked Lemmas 2, 2', 3 and 4 and the assembly by hand: quasicentral
    finite-rank units, the band lying in `M_R tensor 1`, exact order-zero
    lifting through `prod C_i / sum C_i`, colour merging in orthogonal
    corners, and the lower bound.
  * I found no gap.  The `requires: []` route is acceptable.
* **Model (5.1)/(5.2).**  I checked the Cuntz--Krieger relations, the matrix
  units, the range computation, and the rotation-twisted gauge action with
  GIUT.  Sound.  The GIUT theorem number is still unverified.
* **Corollary 5 via Evington.**  Theorem 1 of arXiv:2012.03650v3 and the
  fullness remark were checked in the TeX source.  Essentiality, the unital
  Busby invariant and fullness all hold.  `O_n` being `O_infinity`-stable is
  a standard import and was not re-fetched.
* **Proposition 6.**  I checked by hand the Fredholm index `n-k-1` of the loop
  row, the necessity count `n-k-1=(n-1)r`, and the rank-one Cuntz
  corrections for `k=n-1`.  Sound.  I reran `check_fnk.py`, and all checks
  passed.
* **Corollary 7 and the root-to-root route.**  Sound.
* **ENSW picture versus convention.**  The claim was confirmed in the ENSW v2
  TeX source (convention, hereditary sets, table, pictures).
* **Winter--Zacharias numbering.**  Prop. 2.3, 2.4, 2.5, Cor. 2.8, Prop. 2.9
  and Theorem 7.4 were checked in the TeX source of arXiv:0903.4914v1.
* **Citations.**  All eleven arXiv ids cited here resolve to the stated titles
  (arXiv API, 2026-09-16).
* **Cairn discipline.**  I found no duplicates, all ids are within their caps,
  and there are no placeholder direct proofs.

**What I changed.**
1. **`K`-theory overclaim.**  The artifact Section 6, the split claim and this
   log said the splitting obstruction is "invisible to `K`-theory".  That is
   false as stated.
   * `K_0(C*(F_(n,k)))=Z^2/<(n-1,k)>`, and the sequence
     `0->Z[p_v]->K_0->Z/(n-1)->0` has class `k mod (n-1)` up to sign.
   * A splitting splits it, so `K_0` already forces `k = 0 mod (n-1)`.
   * The index is finer: it separates `k=n-1` from the other multiples, and
     for `n=2` it is the only obstruction.
   * All three places were corrected.
2. **`dim_nuc(O_n)=1`.**  This was imported through unverified BGSW Theorem A
   plus `O_n tensor O_infinity = O_n`.  I added (F6') = [WZ10, Theorem 7.4],
   checked in the source, to the artifact, to Corollary 5, and to step 5 of
   `stw83-circle-ideal-cuntz-quotient-two-bound-proof`.
3. **Heuristic wording softened.**
   * Artifact Section 8 said a dimension-one proof "must therefore recolour".
   * The claim's Attempts said "all known schemes" and "never the
     obstruction".
   * This log said the no-go results "apply verbatim".
   * All of these now say they are heuristic statements about this scheme,
     not no-go theorems.
4. **Faurot--Schafhauser.**  This log misreported the abstract.  Their
   theorem gives `<= 2` for Condition (K), with a sufficient condition for
   `<= 1`.  Corrected.
5. **Generalization dead end.**  The tower bound `dim_nuc(quotient)+1` was
   corrected to `max(1,dim_nuc(quotient))+1` and marked unverified.

**Verdict: landed with fixes.**
* Established:
  * the constant-symbol pullback bound `max(n,d) <= dim_nuc <= max(n,d)+1`;
  * the explicit model and `1<=dim_nuc<=2` for the circle-ideal /
    Kirchberg-quotient ENSW entry, by two independent proofs;
  * the splitting criterion `k=n-1`;
  * an alternative derivation of the circle-by-circle two-bound.
* Open: whether either ENSW "?" entry has nuclear dimension one, and so both
  LXXXIII roots.
* The novelty of the upper bound for entry (i) is correctly disclaimed: it
  follows from Evington.
