# Simple Kazhdan LEF group: sources, novelty check, and consequences for the graph

Lane `ex-kazhdan-simple-hyperlinear`, 2026-09-12. Part 2 of 2. Part 1, with the construction and
the proof, is `simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`. Notation:
`R = LC(X,F_q) ⋊ Z` for an infinite minimal subshift `X`, `G = EL_3(R)`, `S = G/Z(G)`.
Status: review PASS by `ex-verify-groups` (0efeac410); credit notes applied in §8.1.

## 5. Sources read at source on 2026-09-12

- **Pestov**, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968. PDF p. 21 states
  "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property
  (T). Can it be hyperlinear (sofic)?" This matches the root node.
- **Ozawa [64] = N. Ozawa**, *About the QWEP conjecture*, Internat. J. Math. 15 (2004),
  arXiv:math/0306067 (LaTeX source, read 2026-09-12). This is the origin of the question.
  - After Kirchberg's theorem "a group with the properties (F) and (T) is residually finite": "It
    is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the
    above theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP."
  - Earlier: "infinite simple groups with Kazhdan's property (T) ... do not have the property (F)
    as it was shown by Kirchberg".

  Both statements are consistent with `S`: it lacks (F), and `C*(S)` fails the LLP. `S` answers
  Ozawa's question positively.
- **Ershov--Jaikin-Zapirain**, arXiv:0809.4095v2, PDF p. 1, Theorem 1.1. It is quoted verbatim in
  Part 1 §2 and already imported as `elementary-groups-over-fg-rings-have-property-t`. The same page
  2 records that property (T) for `EL_n(R)` was previously known only for commutative `R` or for
  stable range at most `n`.
- **Dadarlat**, arXiv:2007.12655v2 (LaTeX source).
  - Definition: `G` is weakly quasidiagonal if there is a ucp asymptotic homomorphism
    `C*(G) -> M_(k_n)` separating the points of `G`.
  - Example (ii): "Thom noted that infinite simple property (T) groups are not quasidiagonal, and in
    fact they are not weakly quasidiagonal, see Proposition [3.19]".
  - **Proposition 3.19 (Ozawa--Thom)**: "If an infinite property (T) group G is weakly
    quasidiagonal, then G has an infinite residually finite quotient."
- **Thom**, *Examples of hyperlinear groups without factorization property*, arXiv:0810.2180v1,
  p. 4.
  - Theorem 1.4: "There exists a finitely generated Kazhdan group G which is locally embeddable
    into finite groups ... but does not have the factorization property". The example is
    `G_0(F_p[t,t^-1])/C`, which is non-hopfian and not simple.
  - p. 3 recalls the two known sources of simple Kazhdan groups: Kac--Moody lattices and Gromov's
    Tarski-monster quotients.
- **Thom**, *Finitary approximations of groups*, arXiv:1712.01052 (LaTeX source): "every finitely
  generated simple and Fin-approximated group is PSL-approximated". This is consistent with §8.1.
- **Alekseev--Thom**, arXiv:2608.05362, abstract: a Kazhdan group with a sofic embedding whose
  centralizer acts ergodically is LEF. This is consistent: `S` is LEF.

## 6. Novelty and open-status check (bounded)

- **Web search**, three queries: "infinite simple group property (T) sofic LEF elementary matrices
  simple ring Ershov Jaikin"; `"simple" "Kazhdan" group "locally embeddable into finite groups"`;
  "Pestov open question infinite simple group Kazhdan property (T) hyperlinear sofic answered". No
  answer to Question 9.1 was found. The results describe it as open. The 2026 hits
  (Fournier-Facio arXiv:2608.02025; Alekseev--Thom 2608.05362) use `EL_n` over the binary Leavitt
  algebra, or LEF criteria, and exhibit no simple Kazhdan LEF group.
- **arXiv API** returned 14-byte empty responses. A full-text arXiv search was not possible.
- **Repository.** Every node on LEF or MF simple Kazhdan groups is an exclusion claim resting on
  "MF implies weakly quasidiagonal":
  - `simple-kazhdan-groups-have-full-mf-radical`;
  - `exact-kazhdan-radical-kernel-cannot-be-lef` (EKL2);
  - `mf-kazhdan-group-without-finite-quotients-is-trivial`.

  All three routes are invalidated by `mf-to-weak-qd-citation-has-unproved-lifting-step`.

This check is bounded. It is not a literature survey. An `ex-novelty` pass is recommended before
any credit statement.

## 7. Consequences for existing nodes

1. **`mf-kazhdan-group-without-finite-quotients-is-trivial` is false.** `G` is:
   - infinite;
   - Kazhdan (Part 1 §2);
   - LEF, hence operator-MF by `lef-implies-operator-mf`;
   - without nontrivial finite quotients (Part 1 §4.5; only 1.3 and 4.1 are needed).

   The same group refutes the general statement (EKL2) printed in
   `exact-kazhdan-radical-kernel-cannot-be-lef`: "a countable LEF property-(T) group with no
   nontrivial finite quotient is trivial". That node's mapping-torus statement (EKL1) is not
   refuted by this, but it currently has no valid proof route.
2. **The printed arrow "MF implies weakly quasidiagonal" is false for groups, granted
   Proposition 3.19.** `S` is MF (LEF) and is an infinite simple Kazhdan group. By Proposition 3.19
   and simplicity, it is not weakly quasidiagonal. `G` alone already suffices: it is MF, has (T),
   and has no finite quotient. This completes the audit
   `mf-to-weak-qd-citation-has-unproved-lifting-step`: the missing step is not merely unproved, it
   fails.
3. **`simple-kazhdan-groups-have-full-mf-radical` is false.** `S` embeds in an MF group, namely
   itself. This is held until review of Part 1 §4.
4. **Root Attempts bullet "Operator-norm microstates. Dead for every candidate".** This should be
   reversed. `S` is MF, so `kazhdan-mf-hyperlinear-fragment` (kernel-checked: simple Kazhdan MF
   groups are hyperlinear) applies to it. That gives a second, analytic route to hyperlinearity of
   `S`, independent of soficity.
5. **Downstream consumers to recheck.**
   - `kazhdan-hyperbolic-group-without-finite-quotients` says such a group "is non-MF by
     Ozawa--Thom"; that step is gone.
   - `non-mf-hyperbolic-from-kazhdan-quotientless` requires the false claim of item 1.
   - `fp-simple-full-mf-radical-via-titz-witzel` uses item 3. For finitely presented simple groups
     LEF is impossible (finitely presented plus LEF implies residually finite), but MF is not LEF,
     so that route needs its own argument.
   - `torsion-free-kazhdan-alternating-mother-limit-gate` closes that branch by (EKL2). The closure
     is unfounded: `S` is an infinite simple Kazhdan marked limit of finite groups (§8.1).

## 8. Further structure

**8.1 A limit of finite simple groups.** Replace each periodic word `w_k` of Part 1 §3.1 by its
primitive root `z_k` (`w_k = z_k^e`, `z_k` not a proper power). The bi-infinite sequence is
unchanged, so the window properties of §3.1 still hold. `N_k = |z_k|` still grows: a primitive
cyclic word of length `N` has at most `N` distinct windows, while `|L_(2k+1)(X)| >= 2k+2` for an
aperiodic subshift. Products of shifted letter indicators give diagonal functions of arbitrarily
long cyclic windows, and for a primitive cyclic word these separate the `N_k` positions. With
`P_k`, they generate all of `M_(N_k)(F_q)`. So the images of the elementary generators generate
`EL_3(M_(N_k)(F_q)) = SL_(3N_k)(F_q)`.

The partial maps `psi_k` are injective and multiplicative on balls, so the marked groups
`(SL_(3N_k)(F_q), images of generators)` converge to `G`. A scalar `λ I_(3N_k)` with `λ ∉ Λ` is
eventually not a ratio of two ball elements, since such a ratio would be `Psi(λ I_3)`. So the
marked finite simple groups `PSL_(3N_k)(F_q)` converge to `S`.

Credit (review note, 0efeac410): the periodic return-word approximation is the mechanism of
Grigorchuk--Medynets' LEF theorem for topological full groups of minimal subshifts
(arXiv:1105.0719). New here is its application to `EL_3` over the crossed-product ring, together
with the (T) input and root detection: bounded generating sets modulated by a minimal subshift
give PSL families which are uniform expanders (being quotients of the Kazhdan group `EL_3` of the
free `F_q`-algebra on `|A|+2` generators) and which converge to an infinite simple Kazhdan group.

**8.2 Not finitely presented, no factorization property.**
- `S` is not finitely presented: finitely presented plus LEF implies residually finite, and `S` is
  infinite simple.
- `S` does not have Kirchberg's factorization property: for Kazhdan groups, factorization property
  implies residual finiteness (Kirchberg 1994, as recalled in Thom 0810.2180, Theorem 1.1).
- By Becker--Lubotzky, `S` is neither P-stable nor HS-stable, being an infinite sofic Kazhdan group.
  This is consistent: its approximations are exact partial homomorphisms that come from no genuine
  finite representation.

**8.3 Generality.** The proof uses only the following. Every such `R` gives a simple Kazhdan LEF
quotient `EL_n(R)/Z`.
- `R` is finitely generated (property (T) for `EL_n`, any `n >= 3`).
- `R` is simple.
- `R` is LEF as a ring.
- Root detection. Here this came from tower subrings `M_(2m+1)(LC(U))` absorbing bounded
  propagation over bases with long return times.

Examples: any finite field, and any infinite minimal subshift. Whether different subshifts give
non-isomorphic groups is not addressed.

**8.4 Sharpest next targets.**
- **(a) A finitely presented infinite simple sofic Kazhdan group.** LEF is impossible, so the
  approximations must be genuinely Hamming-approximate. Kac--Moody lattices and the Titz Mite--Witzel
  residuals are the candidates.
- **(b) Classification of LEF simple Kazhdan groups.** Is every one of them a PSL-limit of
  `EL_n` type? By Thom's survey statement every finitely generated simple Fin-approximated group is
  PSL-approximated.
- **(c) Pestov 9.2**, hyperbolic groups, is untouched.
- **(d) MF versus weak quasidiagonality.** `G` is MF and not weakly QD. This asks what the correct
  analytic invariant is.
