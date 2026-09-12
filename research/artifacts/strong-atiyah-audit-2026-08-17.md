# 2026-08-17 — Strong Atiyah for torsion-free groups (ingestion audit)

Source: a user-supplied external resolution attempt, "The Strong Atiyah
Conjecture for Torsion-Free Groups: Resolution attempt, repository proof
audit, a division-ring obstruction theorem, and the exact unresolved step",
dated 2026-08-17, unrefereed, written against an upload of this repository.
This file records the ingestion audit and carries the proofs the new graph
nodes cite.

**Verdict, which this audit confirms.**  No proof or counterexample to the
Strong Atiyah Conjecture is obtained.  What the source does obtain is worth
more than most positive-looking attempts: it proves the repository's
finite-dimensional sterility theorem extends exactly as far as *weakly
locally finite* division rings, and then **refutes** the bridge that would
carry it further, using a group that satisfies Strong Atiyah and has a
nontrivial defect.  A refuted bridge is a permanent result; this is the good
kind of negative outcome.

## What the audit changes about the source

1. **The refuting group is already in this graph.**  The source presents
   `W = (⊕_{BS(1,2)/<x>} Z) ⋊ BS(1,2)` as a fresh construction.  It is an
   instance of the family in `infinite-cyclic-compression-lamp-mf` --
   integer lamps over a compressed site space, `Z^(X) ⋊ H` with `H` countable
   residually finite, `L ≤ H` finitely generated and `L_1 = tLt^{-1} < L` --
   at `H = BS(1,2)`, `L = <x>`, `t` the stable letter.  That node already
   records the same phenomenon against a *different* bridge: it observes the
   defect surviving inside a faithful MF group, refuting "the defect lies in
   the MF radical".  The source refutes "the defect dies in every division
   ring".  One witness family, two dead bridges, and neither was known to the
   other author.  The only difference is bookkeeping: the graph's node indexes
   lamps by `H/L_1`, the source by `Q/P`; nothing depends on the choice.
2. **Every repository claim in the source's audit table was re-checked
   against live `main` and all of them hold.**  Details in Section F.  In
   particular the source's reading of `HasSingleSandwichDivision` is right,
   and the file's own docstring agrees with it.
3. **The source's own Section 6.2 obstruction pairs exactly with one landed
   earlier today.**  A division ring hosts no binary Leavitt family, and
   (`augmentation-blocks-unital-leavitt-family`) neither does any `M_n(ZG)`.
   Two different reasons, same conclusion: the Leavitt `K_1` machinery has no
   target in either lane.

## Audit table

| Source | Verdict | Node |
|---|---|---|
| Sec 2 (repository audit table) | every entry re-checked against live `main`, all correct | Section F below |
| Prop 3.1 (finite-dimensional sterility) | correct; already formalized in-repo | `compression-defect-dies-in-finite-dimensions` |
| Thm 4.2 (centrally finite) | correct | `compression-defect-dies-in-centrally-finite-division-rings` |
| Thm 4.3 (weakly locally finite) | correct | `compression-defect-dies-in-weakly-locally-finite-division-rings` |
| Cor 4.4 (embedding obstruction) | correct | in that node's body |
| Constr 5.1, Lem 5.2, Lem 5.3 | correct; group is an instance of an existing node's family | `linnell-skew-field-can-be-centrally-infinite` |
| Thm 5.4, Cor 5.5, Consequence 5.6 | correct; **this is the load-bearing result** | same node |
| Sec 6.2 (no Leavitt family in a division ring) | correct | `division-ring-hosts-no-binary-leavitt-family` |
| Sec 6.1, 6.3, 6.5, 6.6, 6.7 | correct as negative analysis | root claim body |
| Sec 6.4 (property (T) is not the bridge) | correct, pending the Fisher--Ng pinpoint | root claim body |
| Sec 6.8 (Higman calibration) | see Section E -- **the group theory is solid, the division-ring input is the part to check** | root claim body |
| Sec 6.9 (prescribed L^2-Betti) | see Section E | root claim body |
| Sec 6.10 (Kervaire--Steinberg) | correct; `every_centralExtension_splits` verified at KervaireSteinberg.lean:588 | root claim body |
| Sec 7 (what a resolution needs) | correct | root claim body |

---

## A. The target

For countable `G`, let `N(G)` be the group von Neumann algebra and `U(G)` the
affiliated operators.  For a subfield `K` of `C`, let `D_K(G)` be the
**division closure** of `K[G]` in `U(G)`: the smallest subring containing
`K[G]` and closed under inverses of its elements that are invertible in
`U(G)`.

For torsion-free `G` the Strong Atiyah Conjecture over `K` says: every finite
matrix `A` over `K[G]` has `rk_{N(G)}(A)` in `Z`, equivalently
`dim_{N(G)} ker A` is an integer.  By Linnell's theorem this is equivalent to
`D_K(G)` being a **division ring**.  A positive solution for all torsion-free
groups implies the characteristic-zero Kaplansky zero-divisor conjecture.

Known for many classes -- torsion-free elementary amenable groups, locally
indicable groups, several geometric classes -- and open in general.

## B. Finite-dimensional sterility (the repository's theorem)

For `L ≤ H` put

    Comp(L)      = { s in H : s L s^{-1} ⊆ L }
    G_comp(L)    = <Comp(L)>
    𝔇(H,L)       = << [ g z g^{-1}, ℓ ] : g in G_comp(L),
                        z in C_H(L), ℓ in L >>_H

(normal closure in `H`; `[a,b] = aba^{-1}b^{-1}`).

**Proposition.**  For every field `k`, every finite-dimensional `k`-space `V`
and every `π : H → GL_k(V)`, one has `𝔇(H,L) ≤ ker π`.

*Proof.*  Let `C = { T in End_k(V) : T π(ℓ) = π(ℓ) T for all ℓ in L }`, the
commutant of `π(L)`, a finite-dimensional `k`-subspace of `End_k(V)`.  For
`s in Comp(L)`, `T in C` and `ℓ in L`,

    π(s)^{-1} T π(s) π(ℓ) = π(s)^{-1} T π(sℓs^{-1}) π(s)
                          = π(s)^{-1} π(sℓs^{-1}) T π(s)
                          = π(ℓ) π(s)^{-1} T π(s),

using `sℓs^{-1} in L`.  So `Ad(π(s)^{-1})(C) ⊆ C`; this map is injective and
`C` is finite-dimensional, hence `Ad(π(s))(C) = C`.  **Finite dimension is
used exactly here** -- injective implies surjective -- and nowhere else.
Every element of `G_comp(L)` therefore normalizes `C`.  If `z in C_H(L)` then
`π(z) in C`, so `π(gzg^{-1}) in C` commutes with every `π(ℓ)`, and each
displayed generator maps to `1`.  A kernel is normal, so it contains the
normal closure.  QED

Formalized in-repo as `compressionCentralizerDefect_le_ker` in
`GroupApproximation/Criterion/CompressionCentralizerDefect.lean`, over the
same definitions verbatim.

## C. The exact division-ring extension

**Definition.**  A division ring `D` is *centrally finite* if
`[D : Z(D)] < ∞`, and *weakly locally finite* if every division subring
generated by a finite subset is centrally finite.

**Theorem (centrally finite).**  If `D` is a centrally finite division ring
and `ρ : H → D^×` a homomorphism, then `𝔇(H,L) ≤ ker ρ`.

*Proof.*  Put `F = Z(D)`, a field, and regard `V = D` as an `F`-vector space,
finite-dimensional by hypothesis.  Left multiplication `λ_d(v) = dv` is
`F`-linear (`F` is central), and `λ : D^× → GL_F(D)` is an injective group
homomorphism.  Apply Section B to `λ ∘ ρ` and use injectivity of `λ`.  QED

**Theorem (weakly locally finite).**  If `D` is weakly locally finite and
`ρ : H → D^×`, then `𝔇(H,L) ≤ ker ρ`.

*Proof.*  It suffices to kill one generator `u = [gzg^{-1}, ℓ]`.  Write
`g = s_1^{e_1} ... s_m^{e_m}` with `s_i in Comp(L)`.  Let
`K = <z, ℓ, s_1, ..., s_m>` and `L_0 = L ∩ K`.  Each `s_i` compresses `L_0`:
for `a in L_0`, `s_i a s_i^{-1}` is in `L` by compression and in `K` because
`s_i, a in K`.  So `g in G^K_comp(L_0)`, `z` centralizes `L_0`, `ℓ in L_0`,
and `u in 𝔇(K, L_0)`.  Let `E` be the division subring of `D` generated by
`ρ(z), ρ(ℓ), ρ(s_1), ..., ρ(s_m)`; it is centrally finite by hypothesis and
`ρ(K) ⊆ E^×`.  The previous theorem applied to `K → E^×` gives `ρ(u) = 1`.
QED

**Corollary (embedding obstruction).**  If `𝔇(H,L) ≠ 1` then `H` embeds in
the multiplicative group of no weakly locally finite division ring; hence for
every field `K`, `K[H]` embeds in no such division ring.

## D. The refutation: Linnell skew fields need not be weakly locally finite

**Construction.**  Let `Q = Z[1/2] ⋊ Z` with `(r,n)(s,m) = (r + 2^n s, n+m)`,
`x = (1,0)`, `t = (0,1)`, so `txt^{-1} = x^2` and `Q ≅ BS(1,2)`.  Let
`P = <x>`, `X = Q/P`, `A = ⊕_X Z` with `Q` permuting coordinates, and

    W = A ⋊ Q,          c = δ_P in A.

**Lemma (structure).**  `W` is countable, torsion-free, solvable, elementary
amenable, and generated by `x, t, c`.

*Proof.*  `Q` is torsion-free: a finite-order element has trivial `Z`-part,
hence lies in the torsion-free group `Z[1/2]`.  `A` is free abelian.  A
finite-order element of `W` maps to `1` in `Q`, so lies in `A`, so is `1`.
`Q` is metabelian and `A` abelian, so `W` is solvable, hence elementary
amenable.  `Q = <x,t>`, and `δ_{qP} = q c q^{-1}`, so `W = <x,t,c>`.  QED

**Lemma (nontrivial defect).**  For `L = P`: `t in Comp(P)` since
`tPt^{-1} = <x^2> ⊆ P`; `c in C_W(P)` since `P` fixes the coset `P` and hence
fixes `δ_P`.  So `u = [tct^{-1}, x]` lies in `𝔇(W,P)`, and additively

    u = δ_{tP} - δ_{x t P} ≠ 0,

because `xtP = tP` would give `t^{-1}xt in P`, whereas
`t^{-1}xt = (1/2, 0) ∉ <(1,0)> = P`.  So `u ≠ 1` and has infinite order.  QED

**Theorem.**  `W` satisfies the Strong Atiyah Conjecture over `C` (torsion-free
elementary amenable), so `D = D_C(W)` is a division ring and `C[W]` is a
domain.  Yet `u ≠ 1` is killed by every finite-dimensional representation of
`W` over every field.

**Corollary.**  `C[W] → U(W)` is injective (test a finite sum of left
translations on `δ_1`), so `W ↪ D^×` faithfully and `u ≠ 1` in `D^×`.  Let
`E ≤ D` be the division subring generated by `x, t, c`; it contains the
faithful image of `W`.  If `E` were centrally finite, Section C would force
`u = 1`.  Hence **`E` is infinite-dimensional over its center**, `E` is
generated by three elements, and `D` is not weakly locally finite.

**What this kills.**  Both of these are false:

* "Every homomorphism into a division ring kills the compression defect" --
  refuted by the faithful `W ↪ D_C(W)^×`.
* "Every Linnell division ring is weakly locally finite" -- refuted by the
  corollary.

This is not an unfilled technical gap.  The intermediate statement the natural
proof needs is contradicted by a group for which Strong Atiyah is a theorem.

## E. The two calibrations, verified from source

Both of the source's stress tests rest on external theorems.  All of them were
read from source this session and all check out; the pinpoints below are what
the graph nodes cite.

### E.1 Literature record

From **Fisher--Ng, arXiv:2606.19606** (Section 1.1), verbatim:

* the equivalence -- *"For `K ⊆ C`, Linnell showed that the Strong Atiyah
  Conjecture over `K` for a torsion-free group `G` is equivalent to the
  division closure of `K[G]` in its algebra of affiliated operators being a
  division ring [41]."*
* the status -- the question *"has been reformulated into the following **open
  problem** known as the Strong Atiyah Conjecture"*, then Conjecture 1.1,
  stated for a countable group with a bound on the orders of its finite
  subgroups, with `rk_{N(G)}(A) in (1/lcm(G))Z`; for torsion-free `G`,
  `lcm(G) = 1` and the value group is `Z`.
* the known classes -- *"known for many classes of groups, including all
  locally indicable groups [30], braid groups [42], **elementary amenable
  groups** [41], virtually compact special groups [56], and 3-manifold groups
  [19, 35]"*.  **This is the input the refutation in Section D uses.**
* Kaplansky -- *"if `G` is torsion-free and satisfies the Strong Atiyah
  Conjecture over `K`, then the group algebra `K[G]` is a domain."*
* and, directly supporting the source's Section 6.9, that the known
  constructions *"yielding irrational `L^2`-Betti numbers all have torsion
  subgroups of unbounded order."*

### E.2 Higman's group -- verified, and it is a second refutation

`H = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>`.  From
**Fisher--Sanchez-Peralta, arXiv:2303.08165** (the paper the source cites;
Section 3, immediately preceding **Proposition 3.14**): `H` *"can be realised
as a square of groups with `BS(1,2)` vertex groups, `Z` edge groups, and
trivial face group"*, it *"was constructed by Higman in [Hig51], and it was
the first example of an infinite group with no non-trivial finite quotients"*;
Rivas--Triestino *"showed that Higman's group acts faithfully and continuously
on `R`, and therefore is left-orderable"* [RT19, Theorem A, Corollary B]; and
*"Here we show that `kH` has the (a priori) stronger property of embedding
into a division ring, at least when `k` is a field of characteristic zero"* --
which is Proposition 3.14.

So the calibration stands, with every input sourced:

* `H` is torsion-free (left-orderable, and an amalgam of `BS(1,2)`s over
  infinite cyclic edge groups);
* `H` has no nontrivial finite quotient, so by Mal'cev -- a finitely generated
  linear group is residually finite -- **every** finite-dimensional
  representation of `H` over **every** field is trivial.  A nontrivial image
  would be a finitely generated linear group, hence residually finite, hence
  would supply a nontrivial finite quotient of `H`;
* nevertheless `k[H]` embeds in a division ring for every characteristic-zero
  field `k`.

Therefore **complete sterility under exact finite-dimensional representations
does not by itself obstruct division-ring embeddability.**  This is
independent of the group `W` of Section D and refutes a weaker bridge than
Section D does -- one phrased in terms of the repository's *linear residual*
rather than its compression defect.

One caveat the source states correctly and this audit keeps: the division ring
supplied by Proposition 3.14 is not asserted to be the affiliated-operator
division closure, so this does **not** establish Strong Atiyah for `H`.

### E.3 Prescribed second `L^2`-Betti numbers -- verified, and it does not cross

**Fournier-Facio--Sauer, arXiv:2601.00074**, *"Kazhdan groups of dimension 16
with prescribed second `l^2`-Betti number"*.  Theorem A gives simple,
property-`(T)`, lacunary hyperbolic `G_x` with `b_2^{(2)}(G_x) = x` for every
`x` in `R_{>0}`, of cohomological dimension 16 **modulo `{p,q}`**; Theorem B
gives hyperbolic property-`(T)` groups for rational `x`, of cohomological
dimension 16 modulo the primes dividing the denominator.  Their own convention
makes the torsion explicit: dimension `n` modulo `π` means finite dimension
over every ring inverting `π`, which *"implies that `G` only contains
`π`-torsion"*.  The fractional part is manufactured by Dehn fillings in which
designated `g_i` acquire order `p^{k_i}`, contributing `1/p^{k_i}`.
Torsion-freeness is claimed only in the integral case: for `x in N` the group
has finite cohomological dimension over `Z`, hence is torsion-free.  And the
relevant question is posed as open -- whether there is a group of type
`FP_{n+1}(Q)` with irrational `n`-th `L^2`-Betti number (Gra14, Question 4) --
with their groups noted as not of type `FP_2(Q)`.

The source's reasoning is therefore right and now sourced: Strong Atiyah is
about the kernel of **one finite matrix** over `K[G]`, and a group
`L^2`-Betti number computed from an infinite resolution, or as a limiting
dimension for a group without the relevant `FP`-finiteness, is not
automatically a finite-matrix certificate even when irrational.  Combined with
Fisher--Ng's remark that all known irrational-value constructions have torsion
subgroups of unbounded order, the torsion-free finite-matrix barrier is
untouched by this line.

Neither calibration is load-bearing for the refutation in Section D, which is
self-contained apart from the elementary-amenable input quoted in E.1.

## F. Repository audit, re-checked against live `main`

Every file the source cites exists and is tracked.  Spot checks:

* `Criterion/CompressionCentralizerDefect.lean` -- `compressionSet`,
  `compressionGroup`, `compressionCentralizerDefectSet`,
  `compressionCentralizerDefect` (a normal closure, with a `Normal`
  instance), and `compressionCentralizerDefect_le_ker`.  The Lean definitions
  match the source's Section 3 verbatim, including the generator shape
  `⁅g * z * g⁻¹, ℓ⁆`.
* `Steinberg/KervaireSteinberg.lean:588` -- `every_centralExtension_splits`,
  for `5 ≤ n` and any central extension of `SteinbergGroup (Fin n) R`,
  produces a section.  The source's Section 6.10 conclusion follows: a
  section is injective, so torsion already in `St_n(R)` survives in every
  central extension, and in characteristic two `x_ij(1)^2 = x_ij(0) = 1`
  keeps an involution in the split copy.  A central cover therefore cannot
  make the full stable-rank Steinberg source torsion-free.  The source is
  appropriately careful that this bounds only the direct central-lift
  strategy for full `St_n(R)`, `n ≥ 5`.
* `PropertyTT/RingHypotheses.lean:33` --
  `HasSingleSandwichDivision R := ∀ a ≠ 0, ∃ x y, x * a * y = 1`.  The
  source's reading is exactly right, and the file's own docstring says the
  same: it is the Ara--Goodearl--Pardo characterization used for unital purely
  infinite simple rings, deliberately *not* a competing definition of a
  division ring.  Combined with Section D of this audit -- no division ring
  hosts a binary Leavitt family -- the property-`(TT)` hypotheses are
  intrinsically unavailable in a Linnell skew field.
* `Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean` -- the source's
  reading matches the reading recorded in this repository's Whitehead audit
  the same day: universal *for* finitely presented torsion-free groups, no
  claim that the product is finitely presented, and no trace-preservation
  property.
* An exact text search for "Atiyah" over the tree returned nothing at audit
  time.  (It now returns this file and the Whitehead nodes' unrelated
  "Atiyah--Hirzebruch".)

## G. No Leavitt family in a division ring

**Statement.**  A nonzero division ring `D` contains no binary Leavitt family,
i.e. no `s_0,s_1,t_0,t_1` with `t_i s_j = δ_{ij}` and `s_0t_0 + s_1t_1 = 1`.

*Proof.*  `t_i s_i = 1` in a division ring makes `s_i` and `t_i` mutually
inverse, so `s_i t_i = 1` for both `i`.  The sum relation becomes `1 + 1 = 1`,
hence `1 = 0`, contradicting `D ≠ 0`.  QED

Note the contrast with the group-ring case: there the obstruction is the
augmentation and it needs the *orthogonality* relations only
(`augmentation-blocks-unital-leavitt-family` does not use the idempotent
relation), while here the idempotent relation is what fails and the
orthogonality relations are what make the two `s_i t_i` collapse to `1`.  Two
different mechanisms, and between them they close the unital Leavitt route
into group rings and into skew fields alike.

## H. What a resolution still requires

*Positive.*  For every torsion-free `G`, that `D_K(G)` is a division ring;
equivalently that every nonzero element of the division closure has zero von
Neumann kernel.  Nothing here controls kernels of arbitrary elements of
`D_K(G)`, and Section D shows the finite-dimensional mechanism cannot be
promoted to arbitrary Linnell skew fields.

*Negative.*  Explicit torsion-free `G` and `A in M_{m,n}(K[G])` with a proof
that `dim_{N(G)} ker A ∉ Z`; or explicit nonzero `a,b in K[G]` with `ab = 0`,
which would also refute Kaplansky.  The repository produces group words
invisible to selected classes of finite models; it does not convert one into a
matrix over `K[G]` with a computed non-integer kernel dimension.

*Specifically, for any future use of this repository's machinery.*  Because
the calibration group `W` has the compression--centralizer pattern **and**
satisfies Strong Atiyah, any successful argument must use a feature `W` lacks
and must tie that feature directly to von Neumann rank.  Labels are not
enough:

* property `(T)` alone cannot do it -- torsion-free finite-index subgroups of
  `Out(F_n)`, `n ≥ 4`, have property `(T)` and satisfy Strong Atiyah
  (Fisher--Ng, cited);
* nonsoficity and non-MF cannot do it -- they are finite-approximation
  properties and output no matrix, no kernel projection, and no trace;
* a faithful reduced trace cannot do it -- faithfulness forbids proper
  isometries but does not make kernel dimensions integers, and for infinite
  `P` the Kazhdan projection maps to zero in the left regular representation,
  so the repository's proper-projection compression never reaches `N(G)` or a
  matrix over `K[G]`;
* finite-factor reconstruction is circular -- every countable `G` embeds in
  `U(N(G))` with `N(G)` finite, so any theorem reconstructing a properly
  infinite Leavitt ring from an arbitrary nontrivial homomorphism into a
  finite von Neumann algebra would contradict itself at the regular
  representation.  This is the circularity `notes/NOTEPAD.md` already records.
