# Swarm lane: `kun-thom-clifford-crossed-product-ce` (2026-09-16)

Agent label `swarm-kun-thom-clifford-crossed-prod`.  The hole was locked with
`bin/cairn lock kun-thom-clifford-crossed-product-ce --ttl 180m` and released
at the end.  Nothing was committed.

**Outcome: partial progress, with a localization.**  Two new claims are
established by proof, and the target stays OPEN.

- `separable-stabilizer-clifford-crossed-products-are-ce`, with the complete
  route `separable-stabilizer-clifford-ce-proof` (`requires: []`).
- `kt-amenable-compressor-clifford-crossed-products-are-ce`, with the route
  `kt-amenable-compressor-clifford-ce-proof`, which requires the first claim.

All proofs are in
`research/artifacts/kt-amenable-compressor-clifford-ce-2026-09-16.md`.

## 1. Setup

**Target.**  Let `k = F_2` and `r = d = 3`, and put

```text
Gamma = EL_3(F_2[x_1,x_2,x_3]),
G = EL_3(F_2[x^(+-1)]) rtimes SL_3(Z),
```

The claim asks for a trace-preserving embedding of
`M = Cl(G/Gamma) rtimes G` into `R^omega`, with the anticommutation relations
and the canonical trace.  Write `E = EL_3(F_2[x^(+-1)])`,
`L_+ = SL_3(Z) intersect M_3(N)`, and, for `H <= G`,
`M_H = (Cl(G/Gamma) union u_H)''`.

**Orientation: nodes read or cross-checked.**

- The target body itself.  The dead-ends list contains
  `infranormal-compact-closure-normal` (compact Bogoliubov models of `G`),
  the Gaussian model, chart models, AF filtrations and weak-MF certificates.
- `clifford-ce-targets-are-equivalent` and
  `finitary-extension-ce-iff-action-lifts-to-normalizer`.
- `clifford-compressor-site-growth`: infinite Pimsner--Popa index at strict
  compressors.
- Permutation- and relative-level one-compressor results:
  - `kt-one-compressor-full-coset-action-is-sofic`
  - `kun-thom-single-compressor-sofic-joint-nonsofic`
  - `one-kun-thom-compressor-is-relatively-embeddable`
  - `commuting-kun-thom-compressors-are-relatively-embeddable`
  - `heisenberg-kun-thom-slice-is-relatively-embeddable`
  - `amenable-multi-compressors-have-a-joint-hs-telescope`
  - `kt-one-compressor-normalizer-cocycle-splits`
  - `one-kt-compressor-has-pauli-microstates-with-low-band-leakage`
- `kt-pointed-clifford-energy-one-compressor-no-go`.
- `monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable`.
- `kt-two-positive-compressors-generate-full-obstruction`.
- `positive-core-bernoulli-ce`, `profinitely-saturated-clifford-covers-are-surjunctive`
  and `gkp-sofic-action-toolkit`, for `distinct_from`.

**State before this lane.**  At the level of the one-compressor ascending HNN
subgroup `<Gamma,t>`, the graph had several results:

- soficity of the coset action;
- relative embeddability of `L(Gamma)` in `L(<Gamma,t>)`;
- Pauli microstates;
- a pointed-energy no-go that omits anticommutation.

The commuting and Heisenberg slices had analogous results.  **No node proved
Connes embeddability of any Clifford crossed product `M_H` with `H`
nontrivial**, not even `H = Gamma`.

## 2. Literature gate (as of 2026-09-16)

- **Kun--Thom**, arXiv:2608.06222.  Consulted through the repo import
  `research/artifacts/kun-thom-2608-06222-verified.md`, for the pair, the
  nonsofic generalized Bernoulli action (Corollary D) and Theorem 4.1.  It
  was not re-fetched this session.
- **S. Popa**, arXiv:1802.09964v3, Section 6.  It was read on 2026-09-16.
  As recorded when it was read, Theorem 6.3 says that for a free action
  `Gamma action R`, the crossed product `R rtimes Gamma` has the Connes
  approximate embedding property iff an associated `U(R^omega)`-valued
  2-cocycle vanishes.  For the target this is only a reformulation.  The repo node
  `finitary-extension-ce-iff-action-lifts-to-normalizer` records the same
  equivalence.  It gives no computational leverage: to check the cocycle one
  still needs a lift of the full `G`-action, which is the original problem.
- **Suslin 1977** (`SL_r = EL_r` over polynomial rings, `r >= 3`),
  **Brown--Ozawa GSM 88** and **Capraro--Lupini LNM 2136** (microstate
  criterion).  They are used as standard and were not re-fetched.
- **Gardam--Kielak--Popa** arXiv:2401.04945 and **Elek--Szabo** (sofic
  permanence), through the repo nodes only.
- The web search budget was already exhausted in the earlier part of this
  session.  No further search was possible after that.  No source resolving
  the target, or proving Connes embeddability of any of the slices below,
  was found as of 2026-09-16.

## 3. What was proved

### Theorem A: separable stabilizers

Let `H` be residually finite and `X` a countable `H`-set in which every
stabilizer is separable.  Then `Cl(X) rtimes H` is Connes embeddable.

**Mechanism.**

- A Clifford word's trace depends only on the equality pattern of its labels
  (S4) and on whether its group part is trivial.
- For a finite window, one finite-index normal subgroup `N` preserves both.
- The finite-dimensional algebra `Cl(Y) rtimes H/N`, with its faithful trace,
  then matches every moment of bounded length **exactly**.

The hypotheses pass to subgroups.  The theorem fails for `G action G/Gamma`,
because `Gamma` is infranormal and not normal
(`infranormal-compact-closure-normal`).

### Lemma B: the base

`Gamma` is residually finite, and every stabilizer
`Gamma intersect g Gamma g^(-1)` is separable in `Gamma`.

- The ideals `I_M` spanned by monomials with max coordinate `>= M` give
  finite quotients.
- Suslin's theorem turns stabilizer membership into a vanishing condition on
  finitely many linear coefficient functionals of `e^(-1) gamma e`.

Hence `M_Gamma` is Connes embeddable.

### Lemma C and Lemma D: permanence

- **Lemma C.**  Connes embeddability of `M_{H_i}` passes to directed unions.
- **Lemma D.**  Let `N` be Connes embeddable and normalized by a unitary
  representation of an amenable `P`, with `tau(N u_p) = 0` for `p != e`.
  Then `(N union u_P)''` is Connes embeddable.
  - The model is `D(b) = sum_f e_ff tensor alpha_{f^(-1)}(b)` in
    `M_F(C) tensor N`, together with completed Folner permutations.
  - Follow the trajectory of each basis point.  A point whose trajectory
    stays in `F` reproduces the exact moment.
  - At most `n delta|F|/2` points leave `F`, so the error is at most
    `n delta`.

### Theorem B: amenable Ore slices

Let `S subset L_+` be a left Ore submonoid with `<S>` amenable.  Put
`N_S = union_{s in S} s^(-1) Gamma s`.

- `N_S` is a directed union, and `<Gamma,S> = N_S rtimes <S>`.
- Therefore `M_{<Gamma,S>}` is Connes embeddable, and so is `M_K` for every
  subgroup `K` of a conjugate of `<Gamma,S>`.

**Instances.**

- (i) One compressor `<Gamma,t>`, which is the ascending HNN group `V_T`.
- (ii) Any commuting family of compressors.
- (iii) The Heisenberg pair `I+E_12, I+E_23`.  It is left Ore because
  positive words of length `n` take at most `(nC_0+1)^4 < 2^n` values.
- (iv) Any `S` generating a group of subexponential growth.

Separately, every `K <= G` with `K intersect E = 1`, in particular
`SL_3(Z)`, acts freely on `G/Gamma`.  So `M_K` is Connes embeddable by
Theorem A.

### Localization (artifact Section 5)

- **Lemma 5.2.**  `E` lies in no conjugate of any `<Gamma,S>` with `S` left
  Ore.  The cones `t^(-1) N^d` are pointed, so `x^(-(1,1,1))` never enters
  a level of the telescope.
- **Lemma 5.3.**  Congruence quotients of `R` cannot separate `Gamma` from
  `E`, because `R_0 -> R/J` is onto whenever `R/J` is finite.

## 4. Consequences for the target node

**Correction of the parenthetical.**  The target says a refutation "must come
from flexible normalized-Hilbert--Schmidt stability of `G` (or already of the
ascending HNN subgroup `<Gamma,t>`)".  The alternative in parentheses is
closed from both sides.

- `<Gamma,t>` is not flexibly HS-stable, by
  `monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable`.
- Its Clifford crossed product is Connes embeddable, by Theorem B(i).

**Sharpening of `kt-pointed-clifford-energy-one-compressor-no-go`.**  That
node says a matrix-ultraproduct exclusion must consume one of two kinds of
data:

- the anticommutation operator relation, or
- enough further compressors to recover the nonamenable actor.

Theorem B(i) gives one-compressor microstates for **all** moments, including
the anticommutation relation.  So the first kind of data cannot suffice by
itself.

**Where a refutation would have to live.**  Any refutation must use a
subgroup of `G` contained in no conjugate of an amenable Ore slice, and in
none of the other groups covered here.  Two examples of such subgroups are
known:

- the Laurent group `E`, by Lemma 5.2;
- the explicit pair `B = I+E_12`, `A = CB` of
  `kt-two-positive-compressors-generate-full-obstruction`, which generates
  the nonamenable `SL_3(Z)`.

**Novelty audit.**  The graph already had permutation-level, Pauli-level,
relative-embeddability and HS-telescope versions of the one-compressor,
commuting and Heisenberg statements.  Connes embeddability of the actual
Clifford crossed products `M_Gamma`, `M_{<Gamma,S>}` and `M_{SL_3(Z)}` is
new in this graph.  `cairn search` before and after writing returned no
duplicate.  Theorem A and Lemma D are general permanence facts.  Lemma D is
presumably folklore, but no source was fetched, so full proofs are given.
Their novelty outside the graph was not assessed.

## 5. Approaches tried, and exactly where each dies

1. **Theorem A for `G` itself.**  It dies at separability.
   `infranormal-compact-closure-normal` says the image of `Gamma` is normal
   in every finite image `G/N`, so `Gamma N` is normal in `G`.  Hence the
   intersection of all `Gamma N` contains the normal closure of `Gamma`,
   which contains every `phi_L(Gamma)` and so all of `E`.
   - Take any `d in E minus Gamma`.  The labels `Gamma` and `d Gamma` are
     identified in every finite quotient `G/(Gamma N)`.
   - So the equality pattern is not preserved, and the exact moment matching
     of Theorem A is impossible for `G`.
2. **Theorem A for `E`, the Laurent layer, via congruence quotients.**  It
   dies at Lemma 5.3: every finite congruence image of `E` equals that of
   `Gamma`.  Whether `Gamma` is separable in `E` for the full profinite
   topology was not decided.
   - Conditionally, suppose every finite-index normal subgroup of `E`
     contained a congruence kernel `E(J)` with `R/J` finite.  Then Lemma 5.3
     gives `Gamma E(J) = E`, so `Gamma` would be dense in the profinite
     topology of `E` and not separable.
   - No congruence subgroup property for this `E` was verified here, so
     nothing is claimed.
3. **Climbing from `Gamma` to `E` by the Ore telescope.**  It dies at
   Lemma 5.2.  Every level `t^(-1) Gamma t` lives over a pointed cone
   `t^(-1) N^3`, and a directed union of pointed cones indexed by a monoid
   inside `L_+` contains no pair `z, -z`.
4. **Passing from `M_E`, even if it were Connes embeddable, to
   `M_G = M_{E rtimes SL_3(Z)}` by Lemma D.**  It dies because `SL_3(Z)` is
   not amenable.  Lemma D needs a Folner set for the whole acting group.
5. **Two non-commuting compressors generating a nonamenable group.**  The
   explicit pair generates `SL_3(Z)`, so Lemma D is unavailable.  For a left
   Ore `S` with nonamenable `<S>`, the telescope still works: Lemma 4.1 does
   not use amenability, so `M_{N_S}` is Connes embeddable.  But the extension
   step has no substitute for Lemma D.
6. **Amenable non-Ore monoids**, for example a solvable `<S>` containing a
   free submonoid of rank two.  The telescope `(s^(-1) Gamma s)` is not
   directed, and `<Gamma,S>` has no semidirect decomposition over a directed
   union.  Not treated.
7. **Popa's cocycle criterion** (arXiv:1802.09964v3, Theorem 6.3).  It is a
   reformulation only.  Deciding the cocycle needs a lift of the whole
   `G`-action to the normalizer, and that is the target.

## 6. Files

- `research/separable-stabilizer-clifford-crossed-products-are-ce.md` (claim)
- `research/separable-stabilizer-clifford-ce-proof.md` (route, `requires: []`)
- `research/kt-amenable-compressor-clifford-crossed-products-are-ce.md` (claim)
- `research/kt-amenable-compressor-clifford-ce-proof.md` (route)
- `research/artifacts/kt-amenable-compressor-clifford-ce-2026-09-16.md`
  (proofs)

**Weakest step for a referee.**  The Folner trajectory bookkeeping in
Lemma D:

- the bound on the number of bad points;
- the letter-by-letter convention for adjoint letters.

A second candidate is the reliance on the standard microstate criterion (S1)
and on Suslin's theorem, used through (0.1) in Lemma B.
