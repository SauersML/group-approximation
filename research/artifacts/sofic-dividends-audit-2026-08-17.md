# 2026-08-17 — Sofic dividends for the first explicit nonsofic groups (ingestion audit)

Source: a user-supplied external audit, "Sofic dividends for the first
explicit non-sofic groups: proof audit, rigorous partial settlement, and the
exact remaining frontier", dated 2026-08-17, unrefereed, written against an
upload of this repository (`group-approximation-main (67).zip`, SHA-256
`23cdf47c1d11b1d882e9101c22df8c6b3f9cb9f996d05f74a640e5941ee731ba`).  This
file records the ingestion audit and carries the proofs the new graph nodes
cite; the canonical statements live in the graph.

**Headline of the source, which this audit confirms.**  None of the sofic
dividends — Gottschalk surjunctivity, Kaplansky stable finiteness in positive
characteristic, Lueck's determinant conjecture, the algebraic-eigenvalue
conjecture — is settled for the Leavitt unit group `R^x = L_(F_2)(1,2)^x` or
for the Kun--Thom generalized wreath products.  The source says so itself and
declines to overclaim, which is the right call.

**But the rigorous core it offers is not new, and this matters for
bookkeeping.**  Its three headline theorems are published results that this
repository already cites in its own manuscript:

| Source | Actual provenance | Where this repository already had it |
|---|---|---|
| Thm 2.1 (char `0` stable finiteness, every group) | Kaplansky; restated as Bradford--Fournier-Facio Thm 3.4 / Cor 3.5 | `official/counterexample.tex` line 109 |
| Prop 3.1 (reduce char `p` to *a* finite field) | strictly weaker than Bradford--Fournier-Facio Cor 3.15, which reduces to the **prime** field | not yet in the graph — landed by this ingestion |
| Thm 4.1 (surjunctive `=>` stably finite) | Bradford--Fournier-Facio Cor 3.25 | `official/counterexample.tex` line 109, and (contrapositive, proved in full) `stable-finiteness-failure-refutes-surjunctivity` |

The relevant sentence of `official/counterexample.tex`, verbatim:

> For every group `H`, the rings `Z[H]` and `k[H]` for fields `k` of
> characteristic zero are already stably finite [BFF24, Theorem 3.4 and
> Corollary 3.5].  Thus only positive-characteristic fields remain open for
> `R^x`.  If `R^x` were surjunctive, then `k[R^x]` would be stably finite for
> every field [BFF24, Corollary 3.25].

The source cites neither BFF24 nor that file.  Its Sections 2--4 are correct
re-derivations, and the re-derivations are readable, but they are not new
information about this repository's frontier.

---

## What this ingestion changes about the source

Four corrections, three additions.  The additions are the reason this file
exists at all.

1. **The positive-characteristic search is over the prime field, not over
   "some finite field".**  The source's Prop 3.1 produces a counterexample
   over an unspecified finite field `k` of characteristic `p`; BFF24
   Cor 3.15 gives `F[Gamma]` stably finite **iff** `F_p[Gamma]` is.  The
   difference is operational: it says the peer lane's `F_2`-only search
   (`leavitt-group-algebra-not-stably-finite`,
   `dykema-heister-juschenko-bounded-rank-direct-finiteness`) loses nothing
   at characteristic two, and that enlarging the coefficient field is never a
   way to find a witness.  Node: `stable-finiteness-reduces-to-prime-field`.
2. **Its Section 7 (property (T) blocks co-amenability) is already an
   established node here**, `no-invariant-mean-on-coset-space`, with the same
   Day's-trick proof, and it has already been used once to invalidate a route
   (`induced-charge-extension`).  Nothing new; but the source leaves a real
   gap in *applying* it, which is addition (a) below.
3. **Its Section 6 refutes a theorem this repository never cites.**  The
   source says a "surjunctivity extension theorem ... invoked in the notes"
   requires a finitely generated normal kernel, and refutes the application by
   observing that `A^(X)` is not finitely generated.  The observation is true
   and one line.  The invocation does not exist: the string `surjunctiv`
   occurs in exactly three files of this repository
   (`official/counterexample.tex`, `notes/CREDIT_AND_PRIORITY_AUDIT.md`,
   `notes/scout-2026-08-14.md`), and none of them cites an extension theorem
   for surjunctivity of semidirect products.  What `counterexample.tex` line
   95 actually says is that surjunctivity of `R^x` is *unknown*.
4. **Its Section 5 (direct finiteness does not pass to quotients) is correct,
   is the same free-algebra witness this graph landed earlier today
   (`direct-finiteness-not-inherited-by-quotients`), and again attacks an
   argument the repository does not make.**  `counterexample.tex` line 109
   already blocks the naive inference by a sharper route: `s_0` and `t_0` are
   not units at all, so `t_0s_0 = 1 != s_0t_0` is a relation in `R`, not in
   `F_2[R^x]`, and there is no surjection to argue about until one is built.
   The quotient-permanence gap is nevertheless the right thing to state, and
   the peer node states it.

Additions, proved in Sections B--D below:

- (a) **Every Kun--Thom pair has an infinite compression orbit, hence infinite
  index, with no hypothesis beyond infranormal-and-not-normal.**  The source
  assumes infinite index ("where the stabilizer is of infinite index").  It is
  not an assumption: it is forced.  Node:
  `infranormal-nonnormal-has-infinite-compression-orbit`, and the co-amenability
  corollary is `kun-thom-stabilizer-not-co-amenable`.
- (b) **The modular-radical bridge — the one repair the source's Section 8
  leaves open — is dead.**  For a `Z/p`-lamp permutational wreath product in
  characteristic `p`, `omega(k[N])k[W]` is *not* contained in `J(k[W])`, with
  an explicit non-unit.  This kills the only standard ring-theoretic way to
  lift stable finiteness from the residually finite base to the nonsofic
  extension.  Node: `modular-radical-does-not-lift-direct-finiteness`.
- (c) **Klyachko's theorem, which the source is right to invoke, points the
  other way for this programme.**  For a torsion-free target it delivers no
  dividend; it removes the unimodular half of a falsification instrument, and
  only that half.  Node: `klyachko-kl-holds-for-torsion-free`.  A separate
  Kervaire--Laudenbach ingestion landed in this graph the same day
  (`research/artifacts/kervaire-laudenbach-audit-2026-08-17.md`); its
  Klyachko citation is the *other* Klyachko paper, arXiv:math/0409146 on the
  weak conjecture, so the two nodes do not collide and the degree scope in
  Section G below is taken from its
  `weak-kervaire-transfers-only-at-unimodular-degree`.

---

## Audit table

| Source | Verdict | Node |
|---|---|---|
| Thm 2.1, Lem 2.2 (char `0`) | correct; classical, = BFF24 Thm 3.4 | `stable-finiteness-reduces-to-prime-field` |
| Prop 3.1 (reduce to a finite field) | correct but weaker than BFF24 Cor 3.15 | same node |
| Thm 4.1 (surjunctive `=>` stably finite) | correct, convention-robust; = BFF24 Cor 3.25 | `stable-finiteness-failure-refutes-surjunctivity` (contrapositive, already here) |
| Prop 5.1 (quotient permanence fails) | correct; already landed today | `direct-finiteness-not-inherited-by-quotients` |
| Lem 6.1 (`A^(X)` not f.g.) | correct and trivial; the theorem it refutes is not cited anywhere here | Section E below |
| Prop 7.1 (co-amenable + (T) `=>` finite index) | correct; already established here | `no-invariant-mean-on-coset-space` |
| Sec 7 application to Kun--Thom | incomplete: infinite index is asserted, not proved | `infranormal-nonnormal-has-infinite-compression-orbit`, `kun-thom-stabilizer-not-co-amenable` |
| Sec 8 (closure theorem points the wrong way) | correct; this is the graph's own framing | Section C below, `kun-thom-wreath-stably-finite` |
| Sec 8, the repair it does not attempt | dead, proved here | `modular-radical-does-not-lift-direct-finiteness` |
| Thm 9.1, Cor 9.2 (Klyachko) | correct; consequence for this programme is a constraint, not a dividend | `klyachko-kl-holds-for-torsion-free` |
| Sec 10--11 (status of determinant / eigenvalue) | correct, and identical to `counterexample.tex` lines 95 and 107 | root-claim bodies |
| Sec 12.1 (certificate specification) | correct, and sharpened to the prime field | `stable-finiteness-reduces-to-prime-field` |
| App. A.2--A.4, App. B | **empty**: every generated block is an error message | Section F below |

---

## A. The coefficient-field reduction, verified from the source paper

Read this session from `https://arxiv.org/html/2211.01510v2` (H. Bradford and
F. Fournier-Facio, *Hopfian wreath products and the stable finiteness
conjecture*, Math. Z. 308 (2024), art. 58, arXiv:2211.01510), transcribed:

> **Theorem 3.4.** Let `F` be a field of characteristic 0 and let `Gamma` be
> any group.  Then `F[Gamma]` is stably finite.

> **Corollary 3.5.** Let `Gamma` be a group.  Then `Z[Gamma]` is stably
> finite.

> **Corollary 3.15.** Let `p` be a prime and let `F` be a field of
> characteristic `p`.  Then `F[Gamma]` is stably finite iff `F_p[Gamma]` is
> stably finite.

> **Corollary 3.25.** Surjunctive groups satisfy Kaplansky's stable finiteness
> conjecture.  In particular, sofic groups satisfy Kaplansky's stable
> finiteness conjecture.

Their Cor 3.25 is derived through `A`-surjunctivity and `L`-surjunctivity
(their Thms 3.22, 3.24) and the Gromov--Weiss theorem, which is the same
route the source's Section 4 walks by hand.

The source's own Prop 3.1 argument is correct and worth keeping as the reason
Cor 3.15 is believable without reading its proof: the coefficients of `A, B`
generate a finitely generated `F_p`-algebra `R`, a nonzero coefficient `c` of
`BA - I_n` is inverted, a maximal ideal of `R[c^(-1)]` contracts to a maximal
ideal `m` of `R` missing `c`, and `R/m` is finite by Zariski's lemma.  That
gets a finite field; the passage from a finite field to its prime subfield is
what BFF24 add, and it is the half that matters for a search.

**Consequence, which is what the node states.**  For any group `Gamma`,
Kaplansky stable finiteness over *every* field is equivalent to stable
finiteness over the prime fields `F_p`, `p` prime, alone.

---

## B. Infranormal and not normal forces an infinite compression orbit

Let `Gamma <= G` with compression semigroup
`P_Gamma = {g in G : g Gamma g^(-1) <= Gamma}`, let `P_Gamma` generate `G`
(infranormal, Kun--Thom's definition), and let `Gamma` not be normal.

**(i) Some `g` compresses strictly.**  If every `g in P_Gamma` satisfied
`g Gamma g^(-1) = Gamma` then `P_Gamma <= N_G(Gamma)`, and since `P_Gamma`
generates `G` we would get `G = N_G(Gamma)`, i.e. `Gamma` normal.  So fix
`g in P_Gamma` with `g Gamma g^(-1) < Gamma` strictly.

**(ii) No power of `g` lies in `Gamma`.**  Conjugating the inclusion
repeatedly gives the descending chain

    Gamma >= g Gamma g^(-1) >= g^2 Gamma g^(-2) >= ... .

If `g^k in Gamma` for some `k >= 1` then `g^k Gamma g^(-k) = Gamma`, so the
chain returns to its start at step `k` and every inclusion in it is an
equality — contradicting the strictness in (i).  Hence `g^k not in Gamma` for
all `k >= 1`.

**(iii) The orbit of the base point is infinite.**  In `X = G/Gamma`, if
`g^n Gamma = g^m Gamma` then `g^(n-m) in Gamma`, so by (ii) `n = m`.  The
`<g>`-orbit of `Gamma in X` is therefore infinite, `g` has infinite order,
and `[G : Gamma] = |X| = infinity`.

Two remarks.  First, this is the infinite-index companion of
`finite-infranormal-subgroup-is-normal`, which runs the same one-line
cardinality trick on a finite *subgroup* rather than a finite *index*.
Second, (iii) is exactly the hypothesis the modular-radical witness of
Section D needs, so both of the source's Kun--Thom sections are unblocked by
the same three lines.

**Corollary (co-amenability).**  For a Kun--Thom pair — `Gamma` infranormal
but not normal in `G`, both Kazhdan — `Gamma` is not co-amenable in `G`:
`[G : Gamma]` is infinite by (iii), and
`no-invariant-mean-on-coset-space` says a Kazhdan group admits no invariant
mean on an infinite-index coset space.  So no transfer theorem whose
hypothesis is a co-amenable sofic subgroup can be applied through the
stabilizer of the Kun--Thom lamp action.  This is the source's Section 7
conclusion, now with its missing step.

---

## C. What the extension actually is, and which bridge is left

Write the Kun--Thom group as

    W = N semidirect G,    N = directSum_(G/Gamma) Z/2Z,

with `G` residually finite and Kazhdan and `Gamma` infranormal, not normal
(`kun-thom-nonsofic-wreath`).  `N` is locally finite, hence amenable; `G` is
residually finite, hence sofic; `W` is not sofic.  So the standard closure
theorem, *sofic-by-amenable is sofic*, points the wrong way, which is the
source's Section 8 and is also this graph's standing framing.  Since `G` is
residually finite, `k[G]` is stably finite for every field `k`; the dividend
question for `W` is therefore exactly whether stable finiteness *lifts along
the locally finite kernel*.

There are two standard ways to lift, and this ingestion closes both.

1. **Through the Jacobson radical.**  `k[W] / omega(k[N])k[W] = k[G]`, and
   direct finiteness descends modulo an ideal contained in `J` — this is the
   legal quotient direction that
   `direct-finiteness-not-inherited-by-quotients` singles out.  If
   `omega(k[N])k[W] <= J(k[W])`, the dividend follows at once from stable
   finiteness of `k[G]`.  Section D shows the containment is false, in the
   one characteristic where it was plausible.
2. **Through soficity of the action.**  For `char k != 2`, `k[N]` is the
   algebra of locally constant `k`-valued functions on the compact group
   `{+1,-1}^(G/Gamma)` (each `k[Z/2Z] = k x k`), so `k[W]` is the algebraic
   crossed product of that function algebra by the **generalized Bernoulli
   action** of `G` on `G/Gamma`.  Kun--Thom Corollary D says precisely that
   this action is not sofic, for every nontrivial standard probability space.
   So the approximation route to a stably finite crossed product is blocked by
   the same theorem that makes `W` interesting.

The residue is `kun-thom-wreath-stably-finite`, recorded as an open root.

---

## D. The modular-radical bridge fails

**Claim.**  Let `p` be prime, `k` a field of characteristic `p`, `X` a set
with a `G`-action, `N = (Z/pZ)^(X)` the restricted sum of lamps, and
`W = N semidirect G` the permutational wreath product.  If some `g in G` has
an infinite orbit on `X`, then

    omega(k[N]) k[W]  is not contained in  J(k[W]).

*Proof.*  For `x in X` let `a_x` be the lamp generator at `x` and put
`y_x = a_x - 1`.  In characteristic `p`, `y_x^p = a_x^p - 1 = 0`, and

    k[N] = tensor_(x in X) k[y_x]/(y_x^p)

is `N`-graded by total `y`-degree, with the monomials `y_S = prod_(x in S)
y_x^(e_x)` (`0 <= e_x < p`) as a basis.  `G` permutes the `y_x`, so it
preserves the degree, and therefore

    k[W] = directSum_(d >= 0) k[W]_d,     k[W]_0 = k[G],

is a graded algebra: `deg(y_S h) = deg(y_S)` for `h in G`, and
`(y_S h)(y_T h') = y_S (h . y_T) hh'` has degree `deg y_S + deg y_T` or is
zero.  The augmentation ideal `omega(k[N])` is spanned by the `y_S` with
`S` nonempty, is `G`-invariant, and `omega(k[N])k[W]` is the two-sided ideal
it generates; the quotient by it is `k[G]`.

Pick `x` with infinite `<g>`-orbit and set `u = y_x g`, an element of
`omega(k[N])k[W]` of degree `1`.  Then

    u^d = y_x (g . y_x) (g^2 . y_x) ... (g^(d-1) . y_x) g^d
        = y_x y_(gx) y_(g^2 x) ... y_(g^(d-1) x) g^d,

which is a nonzero basis monomial times a group element for every `d >= 1`,
because the sites `x, gx, ..., g^(d-1)x` are pairwise distinct and each `y`
occurs to the first power only.  Now suppose `1 - u` had a right inverse
`v = sum_(d <= D) v_d`.  Comparing graded components of `(1-u)v = 1` gives
`v_0 = 1` and `v_d = u v_(d-1)` for `d >= 1`, hence `v_d = u^d != 0` for every
`d` — so `v` has nonzero components in infinitely many degrees, which no
element of `k[W]` has.  Thus `1 - u` is not invertible, and an element of the
Jacobson radical always has `1 - u` invertible.  So `u not in J(k[W])`.  `[]`

The smallest instance is already decisive: `p = 2`, `X = Z`, `G = Z`,
`W = Z/2Z wr Z` the lamplighter, `k = F_2`, `u = y_0 t`.

**Where it bites.**  By Section B(iii) every Kun--Thom pair supplies a `g`
with an infinite orbit on `G/Gamma`, so the claim applies to every Kun--Thom
nonsofic wreath product at `char k = 2` — the lamp characteristic, and the
only characteristic in which `omega(k[N])` is even a nil ideal of `k[N]`.

**What it does not say.**  It does not say `k[W]` fails to be stably finite,
nor that `J(k[W]) = 0`, nor that no lifting argument exists.  It says the
ideal one would lift along is not radical, so the one-line argument is
unavailable and any replacement must control `1 + M_n(omega(k[N])k[W])`
directly.  It is a dead bridge, not a refutation.

---

## E. The two sections that refute nothing here

Lemma 6.1 of the source — `A^(X)` is not finitely generated when `X` is
infinite and `A != 1`, because a finite set of finitely supported lamp
configurations generates a subgroup supported in a fixed finite set — is
true, and it is the correct observation that the *whole* semidirect product
being finitely generated says nothing about the kernel.  It refutes a
citation this repository does not contain (item 3 of the corrections above).

Likewise Section 5's quotient-permanence fact is correct and useful, and was
landed today by the peer ingestion from a different source document
(`direct-finiteness-not-inherited-by-quotients`, same `k<X,Y>/(XY-1)`
witness).  Neither section is a finding *about this repository*; both are
findings about arguments the source projected onto it.

---

## F. The source's reproducibility appendix is empty

Its Appendix A advertises an archive checksum, a file inventory, a keyword
audit, and a test run; its Appendix B advertises a dated primary-source search
index.  Verbatim, the four generated blocks are:

    find: '/mnt/data/group_approx': No such file or directory

    rg: /mnt/data/group_approx: IO error for operation on
    /mnt/data/group_approx: No such file or directory (os error 2)

    cat: /mnt/data/repo_audit_raw.txt: No such file or directory
    [No test log was produced.]

    No parseable arXiv API response was available in the runtime.

So the checksum in A.1 is of an archive that no listed command ever opened,
and every sentence in the document about what "the notes", "the repository's
finite-search code", or "the repository's attempted implication" contain rests
on no recorded inspection.  That is consistent with what Sections E and 3--4
above found independently: the three characterizations of repository content
that could be checked (a cited surjunctivity extension theorem, a co-amenable
transfer proposal, an attempted "weakly sofic `=>` Kervaire--Laudenbach"
implication) are not in the repository.  The mathematics of the source is
sound; its claims about its subject are not evidence.

This is not a reason to discard the document — Sections 2--5, 7 and 9 are
correct mathematics, and Section 9 is a genuine addition.  It is a reason to
treat every one of its statements about *this repository* as unsourced.

---

## G. Klyachko, and why it is a constraint rather than a dividend

A. A. Klyachko, *A funny property of a sphere and equations over groups*,
Comm. Algebra 21 (1993), 2555--2575, proves that a unimodular equation over a
torsion-free group is solvable over that group; equivalently, for `G`
torsion-free and `w in G * <t>` with total `t`-exponent `+-1`, the natural map
`G -> <G, t | w>` is injective.  Verified this session from secondary
literature only (the survey/statement records around Fenn--Rourke,
*Klyachko's methods and the solution of equations over torsion-free groups*,
and the adjunction-problem literature); the 1993 original was not read, so
this node's trust surface is one classical, universally cited theorem taken
at second hand.

**Its consequence for this programme is negative, and narrower than it first
looks.**  The graph carries a falsification instrument: an equation with no
solution over a candidate group refutes hyperlinearity of that group
(`kervaire-laudenbach-holds-for-hyperlinear`,
`kl-violating-equation-over-leavitt-unit-group`,
`kl-violation-refutes-hyperlinearity-route`).  Klyachko's hypothesis is
`deg_t(w) = ±1`, so over a torsion-free group he removes exactly the
unimodular slice of that instrument.  He does not remove the rest: the
hyperlinear theorem is the nonsingular form, and per the peer node
`weak-kervaire-transfers-only-at-unimodular-degree` a counterexample at any
nonzero degree suffices for the refutation, so over a torsion-free candidate
the instrument survives at `|m| >= 2` and only there.  The source states its
Section 9 in the unimodular form throughout and is right to; a reader who
drops the qualifier gets a strictly false closure claim.

**It does not weaken the existing route.**  `R^x` contains a copy of
Thompson's group `V` (`openai-leavitt-unit-nonsofic`, and
`counterexample.tex` line 95 names the copy), and `V` has torsion, so `R^x`
is not torsion-free and Klyachko does not apply to it.  The Kun--Thom groups
contain their `Z/2Z` lamps and are not torsion-free either.  The source's
own Corollary 9.2 is therefore vacuous over both of this repository's
families: it applies only to torsion-free variants, and the graph has none
whose nonsoficity is established.

---

## Citation records opened by this ingestion

* **Bradford--Fournier-Facio, arXiv:2211.01510v2**, Math. Z. 308 (2024),
  art. 58.  Thms 3.4, Cors 3.5, 3.15, 3.25 read from the arXiv HTML render on
  2026-08-17 and transcribed in Section A.  The repository already cited
  Thm 3.4 / Cor 3.5 / Cor 3.25 in `official/counterexample.tex`; Cor 3.15 is
  new to the graph.  Their Thms 4.2 and 4.4 (Hopfian wreath products
  `<-> ` direct finiteness of matrix rings) concern the *regular* wreath
  product `A wr Gamma` and do not apply to the permutational `A wr_(G/Gamma) G`
  of the Kun--Thom family; that was checked and is why no node claims them.
* **Klyachko, Comm. Algebra 21 (1993), 2555--2575.**  Statement only, at
  second hand; see Section G.
