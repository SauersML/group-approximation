# Liu internality, normalization, and downstream interfaces

Audit date: 2026-09-20. This is a targeted textual mathematical audit, not formal verification or a certification of the complete paper. No canonical node or proof status is changed by this artifact.

## Result and review boundary

No concrete gap was found in the inspected arguments of Liu's Lemma 6.4, Propositions 6.5-6.6, Theorem 6.7, the normalization construction in Section 7, or the lamp and compactness arguments in Section 8. Section 6's deductions are conditional on the quotient expectation lift in Proposition 3.1 and the physical block decomposition of Theorem 5.1. Those earlier theorems were not independently re-proved in this assignment. The property-(T) statement for the polynomial/Laurent pair remains a cited Kun-Thom input. The review therefore does not justify importing Theorem 6.7 or 8.3 with an empty-premise route.

Two integration hazards are concrete:

1. Nonhyperlinearity of the one binary wreath is weaker than normalization for every model of its actor. The existing canonical normalization-failure node can produce a wreath over an intermediate subgroup, not necessarily the original stabilizer. Thus the named wreath theorem alone does not refute that node or its finitary equivalent. The stronger normalization chain does.
2. The fixed-tolerance decomposition has a gap depending on tolerance and uses a doubled list of perturbed generators. It does not supply an original-generator decomposition with one uniform gap at all tolerances, nor genuine finite-dimensional representations.

These are scope corrections, not counterexamples to Liu's statements.

## Sources and provenance

- Jihao Liu, [Nonhyperlinear groups exist](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), dated September 20, 2026; saved PDF, 56 pages. Inspected printed pp. 29-52. SHA-256: `6da1adbd94c82914457f6435426824087dd865a6af3d61d2bcd87a8bec89e71e`.
- Andreas Thom, [A conditional construction of a nonhyperlinear group and the centralizer problem](https://andreasthom.github.io/pdf/nonhyperlinear.pdf), fetched successfully with curl on the audit date after the web opener failed. Fourteen pages; PDF metadata creation/modification date September 14, 2026; HTTP Last-Modified September 16. SHA-256: `0776bde0857be69c8768f5bf1a816db68a48a36fb5c30f1e48ac474773dd39aa`. Inspected Sections 1-5, including the correction/no-drift interface and the double argument. The date information is file provenance, not a claim about first circulation.
- Repository baselines: `output/figures/liu-focused-reading-2026-09-20.md`, `research/kun-thom-lamp-wreath-is-not-hyperlinear.md`, and the individual consumer nodes named below.

Text extraction was checked against rendered Liu pp. 31, 48, and 50. In particular, equation (6.6) contains `sqrt(2/c) lambda^(1/4)`; equation (7.29) bounds both ratios; Theorem 8.3(ii) has an absolute value around the deviation from `sqrt(2)`. Extraction without those delimiters would change the statement.

## 1. Unequal-rank matching: Lemma 6.4

Fix a nonempty symmetric generating list of length `h` for a property-(T) group, a scalar gap `c>0`, and block tuples `U_n` and `V_n` of dimensions `r_n,t_n`. Every fixed group relator must tend to zero in each block's own normalized 2-norm. A bound for the ambient weighted sum of relator errors alone is not this hypothesis; Proposition 6.5 supplies the necessary block selection.

The mixed energy and stabilized distance are

```text
lambda(U,V) = min_(Z != 0) sum_j ||U_j Z-Z V_j||_HS^2 / (4h ||Z||_HS^2),
Delta(U,V)^2 = inf_(iota,jmath) sum_(j=0)^h
  ||iota U_j iota* - jmath V_j jmath*||_HS^2 / (r+t),
U_0=I_r, V_0=I_t.
```

The identity coordinate is essential: it gives `|r-t|/(r+t) <= Delta^2`. The embeddings can be taken in a space of dimension `r+t`, so the minima used are legitimate finite-dimensional compactness minima. Adjoint symmetry allows `r>=t` at each coordinate.

Choose a minimizer with `Tr(ZZ*)=r`, set `b=(ZZ*)^(1/2)` and `m=tr_r(b)`. Powers-Stormer and trace Cauchy-Schwarz give

```text
energy_U(b) <= sqrt(lambda),
1-m^2 <= sqrt(lambda)/c = delta,
m^2 <= t/r,
t/r >= 1-delta,
||b-I_r||_(2,r)^2 = 2(1-m) <= 2 delta.
```

No operator-norm bound for `Z` is asserted or used to place it in the ultraproduct. Instead its polar partial isometry is extended to an isometry `J:C^t -> C^r`. Its range contains `supp(b)`, and

```text
||Z-J||_HS^2/r <= ||b-I_r||_(2,r)^2,
[sum_j ||U_j J-J V_j||_HS^2/(4hr)]^(1/2)
  <= sqrt(lambda) + sqrt(2/c) lambda^(1/4).              (6.6)
```

The second line follows by treating the generator-error list as one Hilbert-space vector and using `||U_j(Z-J)-(Z-J)V_j||_HS <= 2||Z-J||_HS`. This checks the coefficient and the fourth-root loss.

In `prod_omega M_(r_n+t_n)`, the class `v=[J_n]` is bounded, since every `J_n` has operator norm one. Small fixed `lambda_0`, as chosen in (6.4), gives `||v||_2^2 >= 3/8` and distance at most `1/4` from the quotient commutant. Hence `w=E_D(v)` is nonzero. Bimodularity places it in `pDq`.

Both diagonal corners of `D` are scalar. The scalar gaps pass to those corners because the block traces are bounded below: at least `1/2` and `3/8`. Thus `w*w=beta q`, `ww*=alpha p`; nonzero `w` forces `alpha=beta>0`, and equality of traces forces `tau(p)=tau(q)`. Consequently `t_n/r_n -> 1`. The normalized partial isometry in the quotient has initial projection `q` and final projection `p`.

Clipped rectangular contraction lifts `X_n` have `X_n*X_n -> I_t`. Extending their polar parts to isometries `W_n` is possible because `r_n>=t_n`. The estimate `(1-s)^2 <= (1-s^2)^2` for `0<=s<=1` gives closeness. The final exact identity

```text
||U_j-W V_j W*||_HS^2 = ||U_j W-W V_j||_HS^2 + r-t
```

follows by splitting the domain at `WW*`; the complementary column of the unitary has squared norm `r-t`. Together with the identity coordinate this proves `Delta -> 0`.

Verdict: the previously delicate step from a possibly unbounded Hilbert-Schmidt vector to a bounded quotient element is supplied by `J`, before applying property (T). The argument does not assume internality of `D`, so there is no circular use of the theorem being proved.

## 2. Coherent multiplicities: Proposition 6.5

The hypotheses are one fixed scalar gap `c>0`, a tuple perturbation with vanishing ambient squared 2-norm, and an exceptional block of vanishing relative dimension. Block count and ranks can grow without bound.

The proof's uniformity mechanisms check as follows.

1. Enumerate all relators. A diagonal `k_n ->_omega infinity` has total error for the first `k_n` relators at most `k_n^-4`. Discard blocks with any of those normalized errors exceeding `k_n^-1`. Markov's inequality bounds their total relative rank by `k_n^-2`. Every remaining block then satisfies each fixed relator uniformly, equation (6.8). Finite presentation is unnecessary.
2. For pairs with mixed energy at most `lambda_0`, maximize `Delta` at each coordinate. If these maxima do not tend to zero, maximizing pairs contradict Lemma 6.4. Off the selected ultrafilter set the identity one-dimensional tuple is a valid completion. This is a uniform argument over all pairs, not a fixed-pair diagonalization.
3. Choose fixed `rho` with `rho^2/[2h(1-rho^2)] < lambda_0`. Lemma 6.3 makes `Delta<rho` pairs have distance at most `epsilon_n ->0`. Rank comparability and the weighted triangle inequality give `Delta(alpha,zeta)<=4 epsilon_n<rho` through a middle block. Thus closeness is an equivalence relation on the retained blocks. Different classes have mixed energy greater than `lambda_0`.
4. Select a least-dimensional representative in each class. Each member loses at most `8 theta_n^2 r` dimensions, where `theta_n=epsilon_n+1/n`. The summed generator change is at most `(16+64h)theta_n^2 r`. Summing by physical member rank, then dividing by the total dimension, prevents any factor from the number of blocks.
5. Align every member to that one representative, with isometries `W_i`. Their ranges lie in orthogonal original blocks, so `e_ij=W_i W_j*` satisfies `e_ij e_kl=delta_jk e_il` exactly. No choices of independent pairwise intertwiners, and no unproved cocycle correction, remain.

On the retained space the new tuple is `direct_sum_nu (I_(m_nu) tensor z_j^nu)`, with exact commutant

```text
D_n = direct_sum_nu (M_(m_nu) tensor C I_(t_nu)).
```

Within one class the gap off this algebra is `c`; across classes it is at least `lambda_0`. Rectangular sectors are orthogonal, so energy and squared norm add and give gap `gamma=min(c,lambda_0)`. No dimension-ratio multiplier appears after returning to ambient normalization.

With `A_n=D_n + C(1-p_n)`, lost trace `chi_n`, tuple error `eta_n`, and `e_n(x)=(sum_j ||[u_j,n,x]||_2^2)^(1/2)`, the proof obtains

```text
||x-E_(A_n)(x)||_2 <= 2 sqrt(chi_n)
                       + (e_n(x)+2 eta_n)/(2 sqrt(h gamma))     (6.15)
```

for every contraction. Conversely every contraction of `A_n` has original commutator energy bounded by `2 eta_n` in the same square-root convention. These uniform unit-ball estimates prove both inclusions of the full commutant. They do not identify `A_n` with the exact commutant of the originally supplied approximate generators.

## 3. Exhaustion and Theorem 6.7

Proposition 6.6 allows gaps `c_k` tending to zero. For every fixed `k`, retained-column error must tend to zero before `k` increases. Column error implies both off-diagonal corners vanish because, for a finite-dimensional unitary and projection, their squared Hilbert-Schmidt norms agree. Hence `p_k=[p_k,n]` belongs to the commutant `C`.

The normalized corner ultraproduct is valid because `tau(p_k)>=1-epsilon_k>0`; equation (6.16) changes squared norms by the reciprocal of `tr(p_k,n)`, which has a positive limit. Proposition 6.5 in that corner supplies `D_k,n` representing `p_k C p_k`. Adjoining scalars yields

```text
B_k = p_k C p_k + C(1-p_k) subset C.
```

Centrality of `p_k` is not required. For any contraction in `C`, deleting rows or columns meeting `1-p_k` costs at most `2 sqrt(epsilon_k)`. Therefore

```text
||E_C-E_(B_k)||_(infinity->2) <= 2 sqrt(epsilon_k).       (6.18)
```

This includes both cross-corner sectors as well as the discarded diagonal sector.

The crucial Section 3 input is a single sequence `Phi_n` inducing `E_C` on **every uniformly bounded input sequence**. For fixed `k`, coordinate expectations induce `E_(B_k)` by trace orthogonality. Coordinate contraction witnesses attaining the finite-dimensional `infinity->2` norm give

```text
lim_omega ||Phi_n-E_(B_k,n)||_(infinity->2)
  = ||E_C-E_(B_k)||_(infinity->2).                       (6.19)
```

The reverse inequality uses contraction lifts, obtained by singular-value clipping. Thus the result is uniform over all coordinate contractions, despite the nonseparability of the full ultraproduct. A mere dense list of group words would not suffice.

Diagonalizing the uniform bounds with `alpha_k=2 sqrt(epsilon_k)+1/k` gives `A_n=B_(k(n),n)` and `||Phi_n-E_(A_n)||_(infinity->2)->0`. This proves internality without nested corners or a uniform positive lower bound for `c_k`.

Theorem 6.7 uses Theorem 5.1 with `epsilon_k=2^(-k-2)` and the fixed doubled list `(s_1,s_1,...,s_h,s_h)`. Its energy normalization is `1/(8h)`, exactly that of the physical decomposition. Both copies have the same quotient image. Doubling leaves the lazy average and thus the available expectation lift unchanged. Replacing exceptional zero corners by a rank-one identity block outside an ultrafilter-large set is valid; its scalar gap is vacuous.

Unresolved input in this audit: the full proof of Proposition 3.1's all-bounded-sequences expectation lift and Theorem 5.1's decomposition. The steps above check their use, not their independent validity.

## 4. Section 7 and the comparison with Thom

### Precise normalization hypothesis

Liu Theorem 7.4 assumes:

```text
H is countable, discrete, property (T);
Lambda <= H;
H=<Lambda,t_1,...,t_s>,  t_i Lambda t_i^-1 <= Lambda;
pi:H -> U(prod_omega M_(d_n)) is any homomorphism;
D=pi(Lambda)' cap M=[A_n]_omega in those coordinates.
```

It concludes normalization of `D` by `pi(H)` and an internal realization of `Z(D) cap pi(H)'` by `B_n subset Z(A_n)`. No trace-faithfulness or injectivity is assumed. The subgroup need not be Kazhdan if its commutant is separately supplied as internal. Property (T) of the ambient group is load-bearing.

To apply this to an arbitrary infranormal Kazhdan pair `Gamma<=G`, use Theorem 6.7 on `Gamma`, and use finite generation of the discrete Kazhdan group `G` to choose finitely many elements of its compression semigroup generating `G` together with `Gamma`. Thus the universal internality theorem would supply **general** normalization, not merely the q=2 example.

### Checked normalization mechanisms

Lemma 7.1 does not silently assume an endomorphism preserves the center. For one trace-preserving endomorphism, its Cesaro average of a central `z` commutes with `alpha^m(x)`, while its fixed limit `v` obeys `alpha^m(v)=v`. Trace preservation transfers the commutator norm back to `[v,x]`. Averaging the individual fixed-space projections handles finitely many endomorphisms. This proves that expectation onto their common fixed algebra preserves the center.

In Lemma 7.2, the weighted finite-space partition argument works without lower atom-weight bounds. The randomized-sign packing bound is `sum_i mu(S_i)<=delta^2/(eta^2 beta^2)`. Small boundary sets are smoothed and thresholded; minimum mass ensures expansion on subsets of at most half each part's mass. Charging each cut at its first separation gives total boundary at most `6r`. The median estimate (7.6) then approximates all bounded fixed elements, while (7.7) puts every bounded partition element in the fixed algebra. The fixed boundary threshold depends on the quotient gap, not on `r` or atom count.

Theorem 7.4 applies this lemma to `Q_n=E_(Z(A_n)) T_(H,n)|Z(A_n)`. Lemma 7.1 identifies the fixed algebra of the limit, and property (T) supplies the gap. This constructs `B_n` **before** normalization is known. Uniform commutator witnesses and polar averaging give compressor lifts `U_l,n in B_n'`. Hence both `A_n` and `U_l,n* A_n U_l,n` contain the same `B_n`.

Lemma 7.3's near-inclusion dilation uses finite-dimensional commuting representations of source and target commutant. The averaged projection cutoff has

```text
||R-P||_HS <= 4 sqrt(2) delta sqrt(d),
|rank R-d| <= 32 delta^2 d.
```

Two polar intertwiners serve different modules: `W` intertwines the source algebra, while `Z` intertwines the target commutant and the common algebra. Both have deficiency `o(d)`. Consequently source multiplicities and target sizes change by weighted total `o(d)`, equation (7.21). The common-algebra intertwining is used when transporting median transforms; it cannot be omitted.

For source blocks `M_(a_i) tensor I_(r_i)` and target blocks `M_(b_j) tensor I_(s_j)`, exact dilation branching gives

```text
b_j^# = sum_i m_ij a_i,       r_i^# = sum_j m_ij s_j.     (7.22)
```

After deleting `o(d)` dimensions the original labels satisfy `a_i<=(1+epsilon)b_j` and `r_i>=(1+epsilon)^-1 s_j`. Size and multiplicity transforms `x/(x+m)` use the same coordinate `B_n` medians for source and target and for every compressor. They are bounded even if labels or medians diverge. Approximate order plus equal trace makes both transforms compressor invariant in the quotient; membership in `[B_n]` and their median `1/2` forces 2-norm concentration at `1/2`.

The four transformed labels commute in the dilation. Outside an `o(d)` subspace their concentration gives both ratios `a_i/b_j` and `r_i/s_j` within `chi_n` of one, with `chi_n->1`. In each surviving intersection both `a_i/b_j^#` and `s_j/r_i^#` exceed `1/2`. Since the branching multiplicities are nonnegative integers, a good source/target pair has multiplicity one, and each side has at most one good partner. This checks the integer step in (7.30).

Compressing to these matched intersections gives equal algebras. The small complementary trace and contraction-preserving block extensions yield the uniform reverse near inclusion (7.31), then equality in the original ultraproduct. No bound involving the full auxiliary Hilbert-space dimension is needed: the trace comparisons in (7.24)-(7.25) are supported on the sum of the original and retained spaces, of dimension `O(d)`.

### Thom's overlapping route and its different assumptions

Thom Theorem 1.2 assumes the universal centralizer problem, and applies it to both `Gamma` and `G`. Proposition 5.1 aligns internal algebras for both commutants, with exact coordinate inclusion and compressor lifts commuting with the ambient commutant algebra. Theorem 4.2 is then an algebraic no-drift theorem for these aligned algebras.

Thom's Proposition 3.1 gives relative correction of one-sided near inclusions with a common subalgebra. His scale is matrix-size divided by multiplicity. A conditional bounded transform has expectation exactly `1/2` in the common internal algebra. On each exact inclusion cell its target/source scale ratio is at least the square of the integer branching multiplicity. Lemma 4.1 bounds the reverse inclusion error by `sqrt(2) tr(1-R^-1)^(1/2)`. Concentration of the bounded transform makes this vanish.

Liu's Section 7 instead constructs an internal invariant **center**, and compares size and multiplicity separately to obtain a near-full partial matching. Thom's theorem independently supplies the needed normalization consequence once universal Theorem 6.7 is available; it does not, as stated, prove Liu's sharper one-model hypothesis from subgroup internality alone. The shared finite-level anchor is essential: Thom Remark 4.3 gives a proper trace-preserving inner shift of an internal algebra when the common fixed algebra has not been supplied internally. Internality alone plus one compressor is insufficient.

This audit found no contradiction between the two arguments and no reason to replace Thom's stated priority for the conditional normalization/construction. It does not certify all external facts cited in either preprint.

## 5. Section 8: group, lamp, and finite obstruction

For `q=2,r=d=3`, the shear `t=(I,I+E_12)` sends `x_2` to `x_1 x_2`. Its polynomial image is `F_2[x_1,x_1 x_2,x_3]`; all its monomials have first exponent at least second exponent. Thus `gamma_0=I+x_2 E_12` is not in `t Gamma t^-1`. This distinguishes `gamma_0 t Gamma` from `t Gamma`, so their binary lamp product `b` is nonidentity.

The 24 elementary involutions with coefficient in `{1,x_1,x_2,x_3}` generate `Gamma`. For each monomial and each root position, choose the third matrix index and use `[e_ik(f),e_kj(g)]=e_ij(fg)` inductively; root addition gives general polynomial coefficients. The six positive shears generate `SL_3(Z)` as a group by integer row reduction. Their monomial substitutions preserve the polynomial ring. Every nonzero lattice vector is `A(m e_1)` for `A in SL_3(Z)` and positive `m`; conjugating polynomial elementary matrices therefore gives all Laurent elementary matrices. This verifies `G=<Gamma,t_ij>` with the required finite compressor list. Property (T) of both groups is the imported Theorem 8.2, also used in Thom Theorem 1.3.

For every homomorphism `rho:W->U(M)` in the stated matrix ultraproduct, internality and normalization give

```text
rho(a_Gamma) in D,
rho(a_(t Gamma)) = rho(t) rho(a_Gamma) rho(t)* in D,
rho(a_(gamma_0 t Gamma)) = rho(a_(t Gamma)),
rho(b)=I.
```

No faithfulness or canonical trace is used in this collapse. Faithfulness is used only to contradict hyperlinearity. For canonical microstates, the two lamps would have distance `sqrt(2)`.

The compactness passage is sound as an existence argument. Use a countable presentation with symbols `s_g` for all group elements and relations `s_e`, `s_g s_h s_(gh)^-1`. If no finite relator packet forces `||s_b(U)-I||_2<=1`, increasingly accurate assignments in arbitrary dimensions give a homomorphism into a tracial ultraproduct with `||rho(b)-I||_2>=1`, contradicting collapse. Thus some finite packet `R_0` and `delta>0` suffice.

The finite symmetric `F` includes the images of the relevant symbols, inverse symbols, and every displayed word prefix. With

```text
eta=min(delta/12, (sqrt(2)-1)/6),
||v(U)-phi(vbar)||_2 <= 2 |v| eta,
```

all length-at-most-three relators have defect at most `6 eta<=delta/2`; separation of `b,e` gives `||s_b(U)-I||_2>sqrt(2)-3 eta>1`. The absolute separation-deviation statement on p. 50 is therefore consistent with the proof.

This supplies existence of dimension-independent finite `F,eta`; the paper does not enumerate that packet or give a computable numerical value of `delta`. It is not a ready-to-run numerical finite obstruction certificate.

## 6. Exact graph interfaces and proposed nodes

These are proposals for the canonical editor, not new graph facts in this artifact. Claim ids are within the 58-character budget. Reuse existing nodes where their statements already match; do not give an empty-premise citation route to an unreviewed whole theorem.

| Proposed/reused claim | Exact scope | Sufficient input and boundary |
|---|---|---|
| `quotient-gap-gives-large-scalar-expanding-blocks` | Theorem 5.1, fixed tolerance, original dimensions, doubled perturbed tuple, vanishing total perturbation | Earlier-section audit; keep open until that proof is independently accepted |
| `scalar-expanding-kazhdan-blocks-give-internality` | Proposition 6.5, fixed gap, asymptotic relators from an exact quotient homomorphism, negligible exceptional block | Lemma 6.4 plus uniform retained-pair matching and exact coherent multiplicities; quotient property-(T) gap |
| `internal-corners-exhaust-kazhdan-commutants` | If `C` has a single coordinate expectation lift valid on all bounded sequences and `p_k in C` tend to full trace with each `p_k C p_k` internal, then `C` is internal | Proposition 6.6 Steps 2-4; no nesting or uniform block gap |
| `kazhdan-commutants-are-internal` | Theorem 6.7 for every finitely generated discrete Kazhdan group, every homomorphism, every specified ultrafilter and dimension sequence | First three rows and the Section 3 expectation-lift input, via the doubled-list assembly |
| `internal-commutants-normalize-under-compressions` | Theorem 7.4 under its per-model hypotheses above | Weighted invariant-center construction plus relative dilation and matching; not internality alone |
| existing `kt-centralizer-normalization-hs` | All infranormal Kazhdan pairs, canonical trace-preserving models in its present statement | Universal internality plus Liu 7.4; alternatively universal internality plus Thom 1.2. Both actually give arbitrary homomorphisms |

For the exhaustion helper, either include the all-bounded-sequences expectation-lift assumption explicitly as above, or provide its proved property-(T) derivation as a prerequisite. Suppressing it would hide the main uniformity step.

A sufficient assembly route to `kazhdan-commutants-are-internal` is the following precise implication. For each tolerance apply the physical decomposition; form the retained corner; interpret the two generator copies as one fixed doubled presentation; use fixed-gap internality inside that positive-trace corner; then use exhaustion with the original common expectation lift. This route remains conditional if the physical decomposition or lift theorem remains open. Lemma 6.4 and Proposition 6.5 can be packaged in one helper; separate canonical claims for each displayed estimate are unnecessary.

### Strength-sensitive consumers

| Source actually needed | Consumer/consequence | Quantifier restriction |
|---|---|---|
| General normalization | `hyperlinear-groups-kill-rigid-compression-defects`, via the recorded dichotomy | All rigid pairs, not one actor |
| Normalization for all homomorphisms of the chosen Theorem E actor | `hs-uniform-compression-stability-at-the-theorem-e-pair` via `kazhdan-commutant-compression-stability-is-finitary` | Match all q,r parameters in that claim, not only q=2,r=3 |
| The same actor-wide normalization | Negation of `kt-canonical-hs-normalization-fails`; negation of `hs-compression-stability-fails-at-the-theorem-e-pair` | Every model, arbitrary trace; CE witnesses reduce to a separable generated witness and a matrix ultraproduct embedding |
| Normalization for the actor restriction of every wreath model | `kun-thom-lamp-wreath-is-not-hyperlinear`, then `non-hyperlinear-group` | Enough for the one specified group and lamp |
| Nonhyperlinearity of that same wreath plus recorded equivalences | Negations of hyperlinearity of its double, centralizer HNN group, free binary coset wreath, and relative embeddability; corresponding Gaussian-crossed-product nonembeddability | Use `kt-wreath-hyperlinear-iff-double-hyperlinear`; keep group and algebra predicates distinct |
| Wreath nonhyperlinearity plus existing embedding/equivalence consumers | Free-action nonhyperlinearity and A5-wreath nonhyperlinearity | Respect the exact actor parameters in each consumer |
| Double nonhyperlinearity plus its unique-trace-to-hyperlinear MF route | Negation of `kt-double-reduced-cstar-is-mf` | Reduced C*-algebra MF, not abstract group weak MF |
| General internality specialized to every canonical model of the binary Leavitt unit group | Its sequential native-heat rounding property (R), then the recorded two-use nonhyperlinearity argument | Requires the Leavitt group's Kazhdan hypotheses and the two-use argument; does not establish universal channel rounding |

The generic normalization node and its canonical instance must not be conflated. `kt-canonical-hs-normalization-fails` is existential at one family of actors with no trace condition; it is the negation of that instance, not the logical negation of a theorem quantified over every infranormal Kazhdan pair. Likewise the prose in `bare-relative-wall-exists` calling it the exact negation of the generic node is only correct after fixing the corresponding pair and compressor scope. General normalization refutes any such fixed-pair wall; the converse requires additional hypotheses.

The existing wreath claim's downstream list should be read as consequences of the **full claimed internality/normalization chain** wherever it mentions canonical normalization failure or universal compression stability. They do not follow solely from its displayed one-wreath theorem. In particular, a failure of normalization may yield a hyperlinear wreath `W_K` with `Gamma<=K<=G` and the normal closure of `Gamma` not contained in `K`; this does not assert hyperlinearity of `W_Gamma`.

For the Leavitt interface, Section 5 of `leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md` proves the useful bridge: native admissible heat maps and coordinate expectations for an internal commutant induce the same expectation on every bounded sequence. Coordinate witnesses then give `infinity->2` distance tending to zero. A bad ordinary subsequence would remain bad under a free ultrafilter, giving the sequential property (R) for every canonical model. Theorem 6.7 has the correct universal scope for this bridge. This audit checked that interface, not the complete Leavitt component-selection and central-height argument. It does not turn `bistochastic-near-idempotents-round-dimension-free` into a consequence: that claim quantifies over all channels, not native group heat maps.

### Explicit non-consequences

- Neither one-wreath nonhyperlinearity nor actor normalization refutes every possible hyperlinear nonsofic group or decides Pestov's question globally.
- Internal commutants need not arise as exact commutants of the originally supplied generator lifts. Generic tiny perturbations can still destroy their literal commutants.
- Internality does not assert flexible or same-dimensional rounding of an approximate group representation to a genuine representation.
- Theorem 6.7 alone is not the statement of the stronger original-generator scalar block decomposition in the repository.
- Positive normalized-Hilbert-Schmidt results do not contradict the established weak-MF or other-metric defect examples.

## 7. Remaining work before a full import

1. Finish independent review of the all-bounded-sequences expectation lift and of the physical decomposition, including all earlier auxiliary results. This artifact validates their downstream use only.
2. Treat Liu's Section 7 and Thom's conditional theorem as separately attributed routes. Their common consequence has matching general scope, but their minimal per-model hypotheses differ.
3. When adding negative consequences, attach a refuter with precisely the matching proposition/parameter range. Do not let a prose list expand a one-group theorem to all actor models.
4. Review the separate Leavitt two-use argument before promoting its nonhyperlinearity conclusion from the correct internality interface.

No failed estimate or counterexample to Liu's Sections 6-8 was found in this pass. The remaining certification boundary is substantive: earlier analytic inputs, external cited theorems, and independently justified downstream routes are not replaced by this audit.
