# Thompson's F: tower growth of cardinality certificates, a copy of F on degree-zero generators, and linear-algebra degrees for P_(2,2)

Lane `hl-thompson-f`, 2026-09-13. The two amenability roots were edited by another session within the
last six hours, so this lane only adds nodes:
- `thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f`
- `thompson-f-cardinality-certificates-need-tower-degree`
- `thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9`

MSI work directory: `/scratch.global/sauer354/hl-thompson-f/`.

## 1. Verbatim pins

**Moore, arXiv:0905.1118v7** (e-print fetched on MSI, `tower.tex` = `main.tex`, 53650 bytes).
- *l.85–89, Følner definition:* "Recall that a finite subset $A$ of a finitely generated group $G$ is \emph{$\varepsilon$-F\o lner} (with respect to a finite generating set $\Gamma \subseteq G$) if \[ \sum_{\gamma \in \Gamma} |(A \cdot \gamma) \ \symdif A| < \varepsilon |A| \] where $\symdif$ denotes symmetric difference."
- *l.102–108, presentations:* "The standard presentation of $F$ is infinite, with generators $x_i$ $(i \in \Nbb)$ satisfying $x_i^{-1} x_n x_i = x_{n+1}$ for all $i < n$. It is well known, however, that $F$ admits the finite presentation \[ \Seq{A,B \ |\ [AB^{-1},A^{-1}BA] = [AB^{-1},A^{-2}BA^2]= \mathrm{id}} \] (see \cite{CFP})."
- *l.118–122, Theorem `tower_growth`:* "For every finite symmetric generating set $\Gamma \subseteq F$ there is a constant $C>1$ such that if $A \subseteq F$ is a $C^{-n}$-F\o lner set with respect to $\Gamma$, then $A$ contains at least $\exp_{n} (0)$ elements."
- *l.256:* "If $x_n$ is defined by $x_{n+1} = x_0^{-n} x_1 x_0^n$ for $n \geq 1$, then we obtain the generators which yield the infinite presentation of $F$ mentioned in the introduction."

**Guba, arXiv:2305.07113v4** (`jgcc-template.tex`, on MSI).
- *l.474:* "Recall that, according to~\cite{Moore13}, the size of Folner sets in $F$ (provided it is amenable) has a very fast growth: as a tower of exponents."
- A grep for "Moore", "tower" and "huge" found no statement bounding the degree of cardinality certificates for `P_(d,m)` in terms of `d`.

**Proper quotients of `F` are abelian.** Import as recorded in `thompson-f-is-lea-only-if-amenable-proof`
(Burillo–Lodha–Reeves, arXiv:1509.04586, `lm.tex` l.104). The primary source was not re-read.

## 2. A copy of F on two degree-zero elements

`experiments/thompson-f/hl/plsub.py` (md5 `4757b71d2fb96f556d00ac7cefe1070f`) uses exact rational PL
maps. Its output on MSI (Python 3.12):

```
convention L CFP relators trivial: True monoid relations x_j x_i = x_i x_(j+1): True
a = [('0', '0'), ('1/4', '1/2'), ('3/4', '3/4'), ('1', '1')]
b = [('0', '0'), ('1/4', '1/2'), ('1/2', '3/4'), ('3/4', '13/16'), ('7/8', '7/8'), ('1', '1')]
[a,b] trivial: False
max word length 1 pairs (p, q): [('b', 'a')] count 1
convention R CFP relators trivial: False monoid relations x_j x_i = x_i x_(j+1): False
```

Here `a = x_1 x_0^-1` and `b = x_2 x_0^-1`, and the pair `(p, q) = (b, a)` satisfies the two relators with
`p` in the role of `x_0`. The composition convention `f·g = f∘g` ("L") is the one in which the standard
maps satisfy both the finite relators and the monoid relations. `experiments/thompson-f/hl/plcheck2.py`
(md5 `c284fceb140e938e941bbe39570c0b93`) composes point maps without breakpoint merging:

```
R1 identity on 21025 points: True | R2: True | [p,q] moves 13143 points | monoid x2x1=x1x3: True
```

## 3. Tower growth of cardinality certificates

The proof is in `thompson-f-cardinality-certificates-need-tower-degree-proof`. The mechanism:
- `S_(m+1,m+d+1) ⊇ X_m X_(m+1) ... X_(m+d-1)`, so a certificate `|S Y| < 2|Y|` telescopes to one factor
  `X_(m+k)` with `m + k >= 2` and ratio `< 2^(1/(d-1))`;
- that factor contains `x_0, x_1, x_2`, which makes `x_0 Y'` almost invariant under `x_1 x_0^-1` and
  `x_2 x_0^-1`;
- by §2 these generate a copy of `F`, so a coset piece gives an `8/(d-1)`-Følner set for `{x_0^±1, x_1^±1}`;
- Moore's theorem bounds it below by `exp_n(0)` whenever `C^n <= (d-1)/8`, and the universe bound gives
  `|Y'| <= 2^(2D + m + 3d)`.

What it does not do: bound `P_(2,2)` (`d = 2`), give numbers (Moore's `C` is not explicit), or constrain
linear-algebra solutions.

## 4. Linear-algebra (Ore) degrees versus cardinality degrees

**Method.** For a random pair `a, b ∈ F_p[S]` (`p = 2^61 - 1`, seed 1), the map
`(u, v) -> a u - b v` on `M_(D, R_S(D))` is tested with Wiedemann on `B = C A`, where `C` is random with
4 entries per row (`experiments/thompson-f/hl/genwied2.cpp`; runs in `wied-runs.txt`).
- **Injective (certified).** The sequence minimal polynomial has degree `N = 2|U|` and nonzero constant
  term. Then it is the characteristic polynomial of `B`, and `det B != 0`.
- **Solution (certified for that pair).** A nonzero `z` with `A z = 0` checked directly (`in_ker_A: true`).
- **Inconclusive.** Constant term zero but the recovered vector is not in `ker A`. The sparse `C` can make
  `B` singular while `A` is injective: at `S_(2,4)`, `D = 7`, Wiedemann reported singular, but exact
  Gaussian elimination (`genrank.cpp`, a different random pair over `F_(2^31-1)`) gives full column rank
  22880.

| set | inj. certified in D | solution found at D | cardinality `Λ < 2` first at D |
|---|---|---|---|
| `X_2` | 1 (elimination) | 2 (elimination: kernel 1, 7, 35 at D = 2, 3, 4) | 3 |
| `X_3` | 2 | 3, 4, 5 | 6 (`Λ(5) = 2002/1001 = 2`, `Λ(6) = 5282/2740`) |
| `X_4` | 2, 3 | 4, 5, 6, 7 | `> 7` (`Λ(2..7)` = 75/27, 275/110, 1001/429, 3640/1638, 13260/6188, 48450/23256) |
| `X_5` | 2, 3, 4 | 5, 6, 7 | not computed |
| `S_(2,4)` (`P_(2,1)`) | 1..7 (elimination, other pair) | D = 8 inconclusive | 11 |
| `S_(3,5)` (`P_(2,2)`) | 1..8 (Wiedemann, the explicit pair of the claim) | — | `> 12` |

**Observation (not a claim).** A random pair of linear forms in `x_0, ..., x_m` has its first common
multiple in degree exactly `m` for `m = 2..5`. The cardinality method first works in degree
`m(m+1)/2` for `m = 2, 3`, which is the bound of Guba's Theorem `xmy`(b). Linear algebra solves much
earlier, so the bound of §3 is a statement about the cardinality method only.

For `P_(2,2)` the explicit pair has no solution in degree `<= 8`
(`thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9`). The `D = 9` run (`N = 587860`) was
cancelled before it finished (job 732629 task 7).

## 5. Shape of optimal doubling sets

`featmine.py` (MSI job 731635) groups `U = M_(D,R)` by local features of normal forms and records how
many elements a best 0/1 rule misclassifies, compared with the exact optimal `Y` from `doubling_flow`.
- **Exact rules need windows of about `D` letters.** Prefix features `c_p = i_p - p` are exact only
  with `k = D` (`X_2`, `D = 6`: 0 errors at `k = 6`; `S_(3,5)`, `D = 7`: 0 at `k = 7`). For `X_2` at
  `D = 8`, `k = 8` still leaves 48 of 43758 errors.
- **Best short windows:** letter gaps read from the end plus the distance to `L`. Error rates:

  | set | D | k | error rate |
  |---|---|---|---|
  | `X_2` | 8 | 7 | 2.4% |
  | `X_2` | 10 | 9 | 2.1% |
  | `S_(3,5)` | 7 | 7 | 3.6% |

So no bounded-window local rule defines the optimal sets in these degrees. A structured family for a
`P_(2,2)` certificate at large degree would have to be a genuinely global recursion. This is consistent
with the non-closure observations in `research/artifacts/thompson-f-monomial-doubling-2026-09-13.md`.

## 6. Compute record

- **Job 731635** (feature mining): 5 tasks, completed.
- **Job 731668** (exact elimination `genrank`): most tasks cancelled in favour of Wiedemann. The
  elimination data above come from direct runs of `genrank.cpp` (md5 `698ade4af542680c64a1a8c2b1bbbaf8`).
- **Job 732629** (Wiedemann, `genwied.cpp`): tasks 1, 2, 4, 5, 6, 8, 9 completed. Tasks 3, 7 and 10
  (`S_(2,4)` D = 9, `S_(3,5)` D = 9, `X_5` D = 8) were cancelled at 21:35 CDT.
- No jobs of this lane remain queued.

## 7. Exact gap

- **Amenability of F:** open in both directions. Nothing here settles either root.
- **Cardinality route to amenability:** certificates must exist for every `(d,m)`, and their degrees
  grow faster than every fixed tower in `log d` (§3). A proof of amenability along this route needs
  non-constructive or tower-recursive families; bounded explicit searches cannot supply it.
- **Linear-algebra route to `P_(2,2)`:** any common multiple for the explicit pair has degree `>= 9`.
  Deciding `P_(2,2)` needs either a generic solution in some degree `>= 9`, a structural non-Ore invariant
  (which would prove non-amenability), or a proof that every degree fails.
- **Non-amenability:** no finite computation certifies it
  (`thompson-f-nonamenable-iff-some-monomial-set-doubles`, `thompson-f-moment-data-cannot-certify-nonamenability`).
