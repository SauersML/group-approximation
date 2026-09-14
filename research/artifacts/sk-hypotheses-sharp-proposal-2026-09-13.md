# sk-hypotheses-sharp: which hypotheses of the note are necessary (proposal, 2026-09-13)

Lane `sk-hypotheses-sharp`. Line numbers refer to `sk/manuscript-disk-1646.tex`, the Codex 16:46 version. Everything new here is **unreviewed** until sk-referee-1 PASSes it.

## 1. Verdict per hypothesis

| hypothesis (l.45–49) | what fails without it | argument | node (status) |
|---|---|---|---|
| minimal | simplicity | restricting to a proper closed invariant `Y` maps `R` onto `R_Y` with kernel `∋ e_U`, so `G_X → EL_3(R_Y)` has a noncentral proper kernel | `subshift-elementary-group-simple-iff-infinite-minimal` (new, unreviewed) |
| infinite | simplicity | a finite orbit of size `p` gives `R → M_p(F_2)` with kernel `∋ u^p − 1`; for `X = {a^∞}`, reduction mod `u − 1` maps `G_X` onto `SL_3(F_2)` | same node |
| subshift (expansive) | finite generation and (T) | for any zero-dimensional system: `R` f.g. ⟺ `EL_n(R)` f.g. ⟺ Kazhdan ⟺ `k` finite and `X` a subshift | `crossed-product-el-kazhdan-iff-finite-field-and-subshift` (new, unreviewed); odometer case `odometer-crossed-product-elementary-groups-not-kazhdan` (reviewed PASS) |
| finite alphabet | same as subshift | over a compact infinite alphabet every Cantor system is a "subshift", including odometers | same node |
| `F_2` | finiteness is needed, the prime is not | an infinite field makes `R` not f.g., so no (T); every `F_q` works modulo the finite centre | node above; `sk-coefficients-proposal-2026-09-13.md` |
| `n = 3` | nothing proved necessary | every `n ≥ 3` works. For `n = 2` and `X` with a finite cyclic factor, `EL_2(R_X) = EL_(2m)(R_Y)` is simple and Kazhdan. For Sturmian `X`, `n = 2` is OPEN | `cyclic-factor-subshift-el-2-is-simple-kazhdan-lef` (new, unreviewed); `el-2-over-every-minimal-subshift-algebra-is-kazhdan` (OPEN) |
| `EL_3`, not `GL_3` | simplicity and (T) | the half-orbit Fredholm index maps `GL_3(R)` onto `Z` and vanishes on `EL_3(R)`; `ind(diag(u,1,1)) = −1` | `crossed-product-gl-n-has-infinite-cyclic-index-quotient` (new, unreviewed) |
| the acting group `Z` | LEF and soficity (for other groups and actions) | for the boundary action of `F_d`, the analogous `EL_N/Z` is simple and Kazhdan but nonsofic, with no MF quotient | `boundary-action-simple-kazhdan-group-is-nonsofic` (reviewed PASS); `boundary-action-elementary-simple-kazhdan-not-mf` (reviewed PASS after scope repair) |

`E_n` and `EL_n` are the same group, only different notation.

**Summary.** No hypothesis on `X` or on the field is arbitrary:
- "infinite and minimal" is exactly simplicity;
- "subshift over a finite alphabet, finite field" is exactly finite generation and (T).

The arbitrary choices are:
- the prime 2 (any `q` works after dividing by the finite centre);
- the size 3 (any `n ≥ 3` works; `n = 2` works for some `X`, and is open for Sturmian `X`).

## 2. Firewall for the note
Do **not** write "for `n = 2` property (T) fails". It is false when `X` has a finite cyclic factor, e.g. the period-doubling or Toeplitz subshifts. There `EL_2(R_X) = EL_(2m)(R_Y)` has (T) (`cyclic-factor-subshift-el-2-is-simple-kazhdan-lef`).

## 3. Proposed text (a), (b), (c)

The current note states the hypotheses (l.45–46) and uses them at l.78 (no periodic points) and l.84–86 (generation), with no remark on necessity. There is no current text to quote for an insertion. Place the text after l.227 ("completing the proof."), before `\section{Every word-problem degree}`, or immediately after the theorem (l.53).

### Option S (recommended if any sentence is added): +5 lines
```latex
For the one-point subshift $X=\{a^\infty\}$, reduction modulo $u-1$ maps
$G_X=\EL_3(\F_2[u,u^{-1}])$ onto $\SL_3(\F_2)$ with nontrivial kernel,
so $G_X$ is not simple. For the dyadic odometer, a minimal Cantor system
that is not a subshift, the ring $\LC(X,\F_2)\rtimes\Z$ is not finitely
generated, so neither is its elementary group, which then has no property~(T).
```
Proof as it would appear. The first sentence is complete as stated: the kernel contains `e_12(u−1)`, and `EL_3(F_2) = SL_3(F_2)`.
The second sentence needs one more clause if the reader is not to trust it. Replace "is not finitely generated" by:
```latex
is not finitely generated (the coefficients of finitely many elements are
measurable for the translates of one finite clopen partition, and those
translates generate only a subshift factor)
```
That adds +2 lines, for +7 in total.

### Option M (full sharpness remark): +10 lines
```latex
If $X$ is not minimal, restriction to a proper closed invariant subset maps
$R$ onto a nonzero ring with nonzero kernel $I$. If $X=\{a^\infty\}$, take
$I=(u-1)$. In both cases the kernel of $G_X\to\EL_3(R/I)$ is a proper
nontrivial normal subgroup. If $(X,T)$ is a minimal Cantor system that is
not a subshift, such as the dyadic odometer, then $R$ and $\EL_3(R)$ are not
finitely generated, so $\EL_3(R)$ has no property~(T). The larger group
$\GL_3(R)$ maps onto $\Z$: compressing the action of $R$ on the functions on
an orbit to a half orbit gives a Fredholm index that vanishes on $G_X$ and
takes the value $-1$ on $\operatorname{diag}(u,1,1)$.
```
Every sentence is a complete argument at the level of the note, except "not finitely generated", which needs the clause from Option S. The index sentence relies on the additivity of the algebraic Fredholm index, which is standard linear algebra.

### Option 0: add nothing
The hypotheses are standard and visibly used: l.78 uses minimal and infinite, l.84–86 and l.97–99 use the subshift and EJZ.

## 4. Reader-facing trade-offs (d)
- **Option S.** In two sentences the reader learns that "infinite" and "subshift" are needed. The first is a one-line check; the second is a fact the reader must trust, or half a sentence of argument.
- **Option M.** It also shows why minimality is needed and why the group is `EL_3`, not `GL_3`. That costs +10 lines, about 3% of the note, and adds the Fredholm index, machinery the note does not otherwise use.
- **Option 0.** Nothing is lost for a specialist. A nonspecialist does not learn that the theorem is sharp.
- **My recommendation.** Option S if the note gains a short "Remarks" paragraph for other reasons, e.g. `F_q` and `n ≥ 3` from sk-coefficients and sk-arbitrary; otherwise Option 0. Never include the `n = 2` claim.

A sentence contrasting `Z` with the boundary action of `F_d` (simple Kazhdan, nonsofic) would show why the acting group matters. But it cites repository results that are not published and brings in the non-MF paper, which the user decided to keep separate. So it is not recommended for this note.

## 5. Status (e)
- New, unreviewed. Review requests appended to `sk/queue/sk-referee-1.txt`:
  - `subshift-elementary-group-simple-iff-infinite-minimal` (+ `-proof`)
  - `crossed-product-el-kazhdan-iff-finite-field-and-subshift` (+ `-proof`)
  - `crossed-product-gl-n-has-infinite-cyclic-index-quotient` (+ `-proof`)
  - `cyclic-factor-subshift-el-2-is-simple-kazhdan-lef` (+ `-proof`; requires the unreviewed `tower-subshift-elementary-group-is-el-3k-of-base` from sk-open-5)
- OPEN: `el-2-over-every-minimal-subshift-algebra-is-kazhdan`.
- Reviewed inputs used:
  - `steinberg-elementary-groups-are-simple-mod-centre`
  - `elementary-groups-over-fg-rings-have-property-t` (import)
  - `odometer-crossed-product-elementary-groups-not-kazhdan`
  - `boundary-action-simple-kazhdan-group-is-nonsofic`
- Not examined: whether the Steinberg group `St_3(R_X)` is simple, i.e. whether `K_2(3,R_X)` is nontrivial; the notion LEF under other coefficient rings.

## 6. Sharpest next target
`el-2-over-every-minimal-subshift-algebra-is-kazhdan` for a Sturmian subshift. A yes would make the note's `n = 3` arbitrary. It would also give simple Kazhdan groups `EL_2` over rings with no Morita reduction to `EL_n`, `n ≥ 3`, which looks new. The route is the A_5 grading plus Ershov–Jaikin-Zapirain–Kassabov. One or two forks could attack it; it is not needed for the note.
