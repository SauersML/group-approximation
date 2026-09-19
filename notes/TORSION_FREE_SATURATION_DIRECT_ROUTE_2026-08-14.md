# Saturating the compression defect: the direct route, and no sofic or MF quotients

Date: 2026-08-14.  Status: reviewer-facing write-up for expert sanity check,
not an announcement.  Supersedes the deleted `torsion_free_saturation_note.tex`
(same content, markdown).  Companion to
`notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` (the substitution
route, with verbatim source quotations of every Hull/Osin statement used
here) and `notes/TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md` (the Lean
certification boundary).  Externally validated in part by GitHub issue #1
(closed 2026-08-15).

**Claim.**  Combining Fournier-Facio's torsion-free non-sofic construction
(arXiv:2608.02025) with one further application of Hull's small-cancellation
theorem (arXiv:1308.4345), routed so that the embedded simple factor
normally generates the resulting quotient, yields a **2-generated, finitely
presented, torsion-free group `Q` with property (T), acylindrically
hyperbolic, such that every nontrivial quotient of `Q` --- including `Q`
itself --- is non-sofic and has full MF radical**: every homomorphism from a
nontrivial quotient of `Q` to the unitary group of a norm matrix corona is
trivial.

Throughout, *MF group* has the Carrion--Dadarlat--Eckhardt meaning: a
countable group is MF if it embeds in the unitary group of a norm matrix
corona `prod_n M_{d_n}(C) / sum_n M_{d_n}(C)` (bounded sequences modulo
operator-norm-null sequences).  `Rad_MF(G)` is the intersection of the
kernels of all homomorphisms of `G` into unitary groups of norm matrix
coronas; `Rad_MF(G) = G` says every such homomorphism is trivial.

---

## 1. Status and trust surface

Three components:

1. **Machine-checked analytic theorem**: a normal property-(T) subgroup
   contained in the compression defect lies in the MF radical (§2).
2. **Machine-checked algebraic observation**: in the Fournier-Facio
   configuration the compression defect is exactly the normal closure of the
   embedded simple factor (§3).
3. **A small-cancellation step assembled from published statements of Hull
   and Osin**: the normal closure of the simple factor can be routed onto a
   further quotient preserving finite presentation, torsion-freeness, two
   loxodromic generators, and a protected finite set (§4).

Components (1), (2), the nonsoficity criterion, and every implication
downstream of (3) are formalized in Lean (§7).  Component (3) is the only
unformalized part and is what an expert in acylindrical small cancellation
should audit; the two specific questions are at the end (§8).

## 2. The machine-checked obstructions

**Compression core.**  On a countable group `G`: a group `Gamma` with
property (T), a homomorphism `iota : Gamma -> G`, an element `t` with
`t iota(Gamma) t^{-1} <= iota(Gamma)`, and an element `c` commuting with
`iota(Gamma)`.  Its **defect** is

    D = << [t c t^{-1}, iota(gamma)] : gamma in Gamma >>_G .

If `c` still commuted with `iota(Gamma)` after transport by `t` the defect
would vanish; `D` measures the failure of one-sided Kazhdan transport to be
implementable by an honest symmetry.

**Theorem 2.1** (machine-checked, `normalKazhdan_le_normMFResidual`).
*Let `G` be countable with a compression core of defect `D`, and let
`K <| G` be normal with property (T) and `K <= D`.  Then `K <= Rad_MF(G)`.
No finiteness, centrality, or torsion hypothesis on `K` is used.*

**Nonsoficity criterion** (FF Proposition 1.2; the same mechanism as the
criterion driving the OpenAI and Kun--Thom arguments; machine-checked as
`CriterionAssembly.not_isSofic_of_not_isLEF` over `CompressionSetup`).
If `Gamma <= G` are infinite with property (T),
`G = <Gamma, t_1, ..., t_m>` with `t_i Gamma t_i^{-1} <= Gamma`, and
`J <= G` is finitely generated with `[Gamma, J] = 1`, `Gamma cap J = 1`,
`t_1 J t_1^{-1} <= Gamma`, then soficity of `G` forces `J` LEF.  A finitely
presented infinite simple `J` is never LEF (Vershik--Gordon + no nontrivial
finite quotients), which is the use made below, exactly as in FF.

## 3. The Fournier-Facio configuration and its defect

Recall the output of FF §2 (details and the convention discussion in the
companion document §1): a finitely presented torsion-free property-(T)
group `P` containing `P_1 x P_2 x S` with `P_i ~= P` and `S` finitely
presented infinite simple torsion-free (Burger--Mozes or Hyde--Lodha); the
double HNN extension `E` with `u_i P u_i^{-1} = P_i`, acylindrically
hyperbolic by Minasyan--Osin; and a common quotient `pi : E ->> G` of `E`
and a torsion-free hyperbolic Kazhdan `H` via Hull Corollary 7.4, injective
on a finite set containing some `s in S \ {1}`.  `G` is finitely presented,
torsion-free, and has (T).  Write `Gamma = pi(P)`, `t_i = pi(u_i)`,
`J = t_1^{-1} pi(S) t_1`; then `[Gamma, J] = 1`, `Gamma cap J = 1`,
`t_1 J t_1^{-1} = pi(S) <= Gamma`, and `pi|_S` is injective by simplicity.

**Remark 3.1 (acylindrical hyperbolicity of `G` — expert question 1).**
FF's paper does not record whether `G` is acylindrically hyperbolic;
nothing there needs it.  We need it, and it is available at no cost: since
`E` is finitely generated, the proof of Hull Corollary 7.4 produces the
common quotient in `AH_0` (Hull states the `AH_0` conclusion explicitly in
the finitely generated case).  Fix once and for all a `G` produced by
running FF §2 with that clause invoked, so `G` is finitely presented,
torsion-free, (T), and in `AH_0`.  This is a *reading of the cited
corollary*, not a modification of the construction.

Take the compression core on `G` with `iota` the inclusion of `Gamma`,
`t = t_1`, and any `c in J \ {1}`, so
`d := t_1 c t_1^{-1} in pi(S) \ {1}`.

**Lemma 3.2 (defect identification; the containment `>=` is
machine-checked as `simpleSubgroup_le_defectNormal`).**

    D = << pi(S) >>_G .

*Proof.*  (`<=`) Each generator `[d, iota(gamma)] = d (gamma d^{-1}
gamma^{-1})` is a product of two conjugates of `d^{+-1} in pi(S)`.
(`>=`) `D cap pi(S)` is normal in `pi(S)`; since `S` is infinite simple it
is nonabelian and centreless, so `d != 1` is not central in `pi(S)`: some
`gamma in pi(S) <= Gamma` has `[d, gamma] != 1`, so `D cap pi(S) != 1`,
hence `= pi(S)` by simplicity. ∎

No choice of ingredients makes saturation automatic: `E / <<P>>^E ~= F_2`
and `<<S>>^E <= <<P>>^E`, so saturation must be created at a quotient stage
(companion document §3).

## 4. Saturation via Hull's theorem (expert question 2)

Assembled entirely from Hull Definition 1.4, Lemma 3.5, Lemma 5.5,
Corollary 5.7, Lemma 5.8, Theorem 3.12, Theorem 7.1, and Osin
(Trans. AMS 368) Lemma 7.1 — all quoted verbatim in the companion
document §6.

**Lemma 4.1.**  *Let `G` be torsion-free acylindrically hyperbolic and
`N != 1` normal.  Fix a generating set `A` with `Gamma(G, A)` hyperbolic
and the action acylindrical and non-elementary (Hull Thm 3.12(4)).  Then
`N` is suitable with respect to `A`, and contains non-commensurable
loxodromics `h_1, h_2` with `E_G(h_i) = <h_i>` such that
`S_0 = <h_1, h_2> <= N` is again suitable.*

*Proof.*  `N` is nontrivial and torsion-free, hence infinite; being normal
it is s-normal, so it acts non-elementarily by Osin Lemma 7.1.  Suitability
condition 3 is vacuous in a torsion-free group (Hull Lemma 5.5).  Hull
Corollary 5.7 applied to the suitable `N` gives `h_1, h_2`; Hull Lemma 5.8
makes `<h_1, h_2>` suitable. ∎

**Lemma 4.2 (defect saturation).**  *Let `G` be finitely presented,
torsion-free, acylindrically hyperbolic, `N != 1` normal, `F <= G` finite.
Then there is `q : G ->> Q` with:*

1. *`Q` acylindrically hyperbolic;*
2. *`Q` finitely presented and torsion-free;*
3. *`q(N) = Q`; indeed `Q = <q(h_1), q(h_2)>` with `h_1, h_2 in N` from
   Lemma 4.1, so `Q` is 2-generated;*
4. *`q|_F` injective.*

*Proof.*  Apply Hull Theorem 7.1 to `(G, S_0)` with `{t_1, ..., t_m}` a
finite generating set of `G` and `M` with `B_A(M) >= F`.  Clauses (a), (b),
(c) give `Q in AH`, `q|_{B_A(M)}` injective, and `q(t_i) in q(S_0)`, hence

    Q = <q(t_1), ..., q(t_m)> <= q(S_0) <= q(N) <= Q ,

so `q(N) = Q = q(S_0) = <q(h_1), q(h_2)>`.  Torsion-freeness is clause (e).
Finite presentation is read off from the proof of Theorem 7.1 exactly as FF
does: the `m = 1` case quotients by the normal closure of a single relator
`W = t^{-1} h_1^{m_1} h_2^{l_1} ... h_1^{m_n} h_2^{l_n}` (cyclic shifts of
`W^{+-1}` have the same normal closure) and the general case is a finite
induction, so `Q` is `G` with `m` added relators. ∎

The alternative with the same output — re-running Hull's proof of
Corollary 7.4 with the reservoir of target words confined to a prescribed
infinite normal subgroup of one factor — is the companion document's
Theorem B.  The route above has fewer moving parts: Theorem 7.1 is used as
a black box on the already-constructed `G`.

## 5. The main theorem

**Theorem 5.1.**  *Let `G` be as in §3 (with Remark 3.1) and apply
Lemma 4.2 with `N = << pi(S) >>_G` and `F = {1, pi(s)}`, obtaining
`q : G ->> Q`.  Then:*

1. *`Q` is 2-generated, finitely presented, torsion-free, acylindrically
   hyperbolic, with property (T);*
2. *every nontrivial quotient `L` of `Q` --- including `Q` itself ---
   satisfies `Rad_MF(L) = L`; in particular no nontrivial quotient of `Q`
   is MF, and every homomorphism from `Q` to an MF group is trivial;*
3. *every nontrivial quotient of `Q` is non-sofic.*

*Proof.*  (1) is Lemma 4.2 plus (T) passing to quotients.

For (2)-(3) let `r : Q ->> L` be a nontrivial quotient and
`rho = r . q . pi : E ->> L`.  Since `q(N) = Q` and images of normal
closures are normal closures of images,

    L = r(Q) = << rho(S) >>_L .

In particular `rho(S) != 1` (else `L = 1`), so `rho|_S` is injective by
simplicity and `rho(S) ~= S`.

*The configuration descends.*  Put `Gamma_L = rho(P)`, `t_i^L = rho(u_i)`,
`J_L = (t_1^L)^{-1} rho(S) t_1^L`.  Then `L = <Gamma_L, t_1^L, t_2^L>`;
`t_i^L Gamma_L (t_i^L)^{-1} <= Gamma_L`; `[Gamma_L, J_L] = 1` and
`t_1^L J_L (t_1^L)^{-1} = rho(S) <= Gamma_L`; `Gamma_L` has (T) (quotient
of `P`) and is infinite (contains `rho(S)`); `L` has (T) (quotient of `Q`);
and `Gamma_L cap J_L = 1`: an element `x` of the intersection lies in `J_L`
and centralizes `J_L` (by `[Gamma_L, J_L] = 1`), hence lies in the centre
of `J_L ~= S`, which is trivial.  *Only centrelessness of the simple image
is used.*

(2) Take the core on `L` with `iota` the inclusion of `Gamma_L`,
`t = t_1^L`, `c in J_L \ {1}`.  Lemma 3.2 run verbatim in `L` gives defect
`= << rho(S) >>_L = L`; Theorem 2.1 with `K = L` gives `Rad_MF(L) = L`.
For the last clause of (2): the image of a homomorphism `Q -> M` with `M`
MF is a quotient `L` of `Q` embedded in `M`; subgroups of MF groups are MF;
so `L = 1`.

(3) The descended data are the hypotheses of the nonsoficity criterion for
`L` with `J_L ~= S` finitely generated; if `L` were sofic, `S` would be
LEF, contradiction. ∎

## 6. Consequences

**Corollary 6.1.**  `Q` has no nontrivial finite, amenable, residually
finite, linear, sofic, or MF quotient; `Q` is perfect; `Q` has no proper
finite-index subgroup; the profinite and Bohr compactifications of `Q` are
trivial; every finite-dimensional unitary representation of `Q` is trivial.
(Each such quotient would be sofic or MF; an abelian nontrivial quotient
would be amenable; a proper finite-index subgroup gives a nontrivial finite
quotient via the coset action.)

**Corollary 6.2 (marked groups).**  Fix a finite presentation
`Q = <x, y | R>` and a word `v != 1` in `Q`.  The 2-marked groups
satisfying the finitely many relations `R` and the single inequation
`v != 1` form a nonempty clopen set consisting entirely of groups that are
simultaneously non-sofic and non-MF, each with full MF radical.  Moreover
`F_2 ->> Q` witnesses that neither soficity nor MF passes to quotients with
a residually finite source, and two generators are optimal (1-generated
groups are abelian).

**Remark 6.3 (C-star, deliberately minimal).**  `C*_r(Q)` is stably finite
(faithful trace) and not MF, and every unital map `C*_max(Q) -> A` with `A`
an MF algebra kills the canonical unitaries (it would otherwise induce a
nontrivial group homomorphism to an MF target).  Simplicity, unique trace,
and stable rank one of `C*_r(Q)` would follow from the
acylindrical-hyperbolicity literature but are **not asserted**: their
inputs are outside both the formalization and this note's scope.

## 7. The certification boundary

Machine-checked in this repository, with no axioms and no
literature-transcription premises (modules `Sofic/NormalKazhdanMFRadical`,
`Sofic/TorsionFreeFullMFRadical`, `Sofic/TorsionFreeFullMFConsequences`,
`Criterion/CriterionAssembly`):

* Theorem 2.1 (`normalKazhdan_le_normMFResidual`, also in literal CDE
  corona form);
* the nonsoficity criterion (`not_isSofic_of_not_isLEF`);
* Lemma 3.2's saturation direction
  (`FournierFacioDefectData.simpleSubgroup_le_defectNormal`);
* all implications downstream of the saturation step: from proof-carrying
  input (`DefectRoutingData`: surjection with saturated defect, two
  generators, finite presentation, power torsion-freeness, (T), one
  protected element) Lean derives Theorem 5.1(1)-(2) including
  `cdeMFResidual = top`, failure of the CDE embedding property, heredity of
  the full radical by every quotient, triviality of every homomorphism to
  an operator-MF group — and Theorem 5.1(3) for the routed quotient via
  `NonsoficCriterionData.not_isSofic` on the descended criterion data.

**Not formalized**, asserted only on the cited literature: existence of the
input data — FF's construction (§3), acylindrical hyperbolicity and the
`AH_0` clause (Remark 3.1), Lemmas 4.1-4.2.  There is deliberately no Lean
theorem `∃ Q, ...`: Mathlib has no theory of acylindrical hyperbolicity or
Hull's suitable-subgroup small cancellation, and the boundary is
represented by structures whose fields are consumed by checked proofs, not
by axioms.  See `notes/TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md`.

## 8. The two questions for the expert reader

1. **Remark 3.1**: is it correct that running FF §2 with the
   finitely-generated clause of Hull Corollary 7.4 yields `G in AH_0` with
   all other properties of the construction unchanged?
2. **Lemma 4.2**: is the direct application of Hull Corollary 5.7 and
   Theorem 7.1 to the suitable subgroup `N = << pi(S) >>_G` (suitability
   via Osin Lemma 7.1 and torsion-freeness) correct as stated, including
   the finite-presentation and torsion-preservation readings of the proof
   of Theorem 7.1?

## References

* J. R. Carrion, M. Dadarlat, C. Eckhardt, *On groups with quasidiagonal
  C*-algebras*, J. Funct. Anal. 265 (2013), 135-152.
* F. Fournier-Facio, *A torsion-free non-sofic group*, arXiv:2608.02025.
* M. Hull, *Small cancellation in acylindrically hyperbolic groups*,
  Groups Geom. Dyn. 10 (2016), 1077-1119, arXiv:1308.4345.
* G. Kun, A. Thom, *Nonsofic wreath products of residually finite groups*,
  arXiv:2608.06222.
* A. Minasyan, D. Osin, *Acylindrical hyperbolicity of groups acting on
  trees*, Math. Ann. 362 (2015), 1055-1105.
* OpenAI, *A nonsofic group*, 2026.
* D. Osin, *Small cancellations over relatively hyperbolic groups and
  embedding theorems*, Ann. of Math. 172 (2010), 1-39, arXiv:math/0411039.
* D. Osin, *Acylindrically hyperbolic groups*, Trans. Amer. Math. Soc. 368
  (2016), 851-888, arXiv:1304.1246.
