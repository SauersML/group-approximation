# Kervaire--Laudenbach with torsion: extreme-height blocks and the two-level screen (2026-09-14)

Lane `hl-kl-two-level-words`. Target: `kl-two-level-words-over-torsion-free-by-cyclic`
(OPEN, from `hl-kl-howie-overlap`, ce6d15b38), first the `n = 2` case with a
repeated base letter.

**Verdict: partial.**
- Landed a general theorem over every group,
  `kl-holds-when-extreme-height-blocks-have-infinite-order`. Klyachko's proof
  of Theorem A needs infinite order only for the coefficient blocks at the
  extreme heights of a canonical cut, and there only at the middle of an
  inverse palindrome.
- Landed the screen `two-level-kl-violations-need-torsion-in-an-extreme-block`.
  A two-level counterexample needs a finite-order level-changing coefficient
  exactly there; every other two-level word injects, at every `n` and with any
  number of base-level letters.
- The target stays OPEN. The residue is the words with torsion at the middle of
  an inverse-palindromic extreme block.

Nodes landed:
- `klyachko-lemma-2-solves-relatively-free-shift-systems` + `klyachko-lemma-2-citation`
  (import);
- `stripped-infinite-order-elements-are-free-over-a-factor` +
  `stripped-infinite-order-free-factor-proof` (elementary, sharp);
- `kl-holds-when-extreme-height-blocks-have-infinite-order` +
  `kl-extreme-height-blocks-klyachko-proof`;
- `two-level-kl-violations-need-torsion-in-an-extreme-block` +
  `two-level-kl-extreme-block-screen-proof`.

## 1. Pins

### 1.1 Klyachko 1993

Source: A. A. Klyachko, *A funny property of sphere and equations over groups*,
Comm. Algebra 21(7) (1993), 2555--2575. Publisher PDF from
`/scratch.global/sauer354/hl-kl-torsion/src/k93/k93.pdf`, md5
`f312bfcc4bed22ff5dfb23f82181f2ab`. Pages 2568--2575 were read as rendered page
images; the scan prints some `<=` as `<`.

- p. 2569--2570, **Lemma 2**: "Let H be a group with two isomorphic subgroups P
  and P^phi. [diagram: H containing P --phi--> P^phi] a_i, b_i, c in H,
  gp(a_i,P) = <a_i>_inf * P, gp(b_i,P^phi) = <b_i>_inf * P^phi, i=0,...,k. Then
  the system of equations over H (prod_{i=0}^k b_i t^-1 a_i t) ct=1
  {t^-1 pt=p^phi, p in P} is solvable over H."
- p. 2570, proof of Lemma 2: "Proving by contradiction, It is sufficient to
  organize a motion satisfying the condition of Proposition 1a on arbitrary
  tesselation satisfying the conditions of Lemma 1a with fewer than two
  collision points."
- p. 2571: "If there is a collision in an interior source-vertex (or
  sink-vertex) (Fig.12), it means a relation in a gp(a_i,P) (or
  gp(b_i,P^phi)). This relation has to be trivial, and the tesselation is
  reducible as usually. As for the vertices of other kinds, it is evident that
  the schedule of staying of cars in such a vertex satisfy the condition of
  Proposition 1a (Fig.13). Thus, the only point which can be a point of
  complete collision is the exterior vertex. Contradiction to Proposition 1a."
- p. 2572, notation: "G^[i]=t^-i Gt^i ⊂ G*<t>, P_m = gp({G^[i], 0<i<m})
  R_m=gp({G^[i], 1<i<m}), phi: P_inf--->R_inf the natural isomorphism
  p|--->t^-1 pt". (The inequalities are `<=` in context: `P_0 = G`.)
- p. 2572, **Lemma 3**: "Let w in G*<t>, and the exponent sum of t in w is equal
  to one. Then w is conjugated to a product (prod_{i=0}^k b_i t^-1 a_i t)ct (1)
  were for some m 1) each a_i, b_i, c in P_m 2) each a_i not in P_{m-1}
  3) each b_i not in R_m."
- p. 2573, **Theorem 4**: "The group K=<G,t; w=1> is not trivial, if G is not
  trivial, and each coefficient of w has infinite order." From its proof: "Let
  H=G_0*...*G_m the free product of m+1 copies of G. The equation w=1 (in the
  form (1)) can be considered as an equation over H by means of the natural
  isomorphism H ≅ P_m, G_i ≅ G^[i], P ≅ P_{m-1}, P^phi ≅ R_m. By Lemma 2 the
  system of equations over H w=1 {t^-1 pt=p^phi, p in P} has a solution t~ in
  an overgroup H~ ⊃ H. (To verify the conditions of Lemma 2 one need to observe
  the following simple fact. If u in (A*B)\A, and each factor of u has infinite
  order, then gp(A,u)=A*<u>_inf.) It is evident, that w(t~)=1. Thus, H~ is an
  overgroup of G containing a solution of (2), hence the natural map G ---> K is
  a monomorphism, and K is non-trivial."

**Reading.** Infinite order enters Theorem 4 only through the simple fact, used
for `a_i` (with `A = P_(m-1)`, `B = G^[m]`) and `b_i` (with `A = R_m`,
`B = G^[0]`). Lemma 2 has no hypothesis on `c`.

### 1.2 Klyachko 2006 (arXiv:math/0406382v4, `main.tex`, on MSI)

- l.119--136: "A generalized equation over a group G with a variable group T is
  a formal expressio of the form g_1t_1g_2t_2...g_nt_n=1, where g_i in G,
  t_i in T. We call generalized equation (*') solvable over the group G if
  there exist a group G~ containing G as a subgroup and a homomorphism T -> G~,
  t |-> t~ (called a solution to generalized equation (*')) such that
  g_1t~_1g_2t~_2...g_nt~_n=1 in G~."
- l.263--267, **Definition 1**: "Generalized equation (1') is called unimodular
  if 1) the order of prod t_i in the group T is infinite; 2) gp(prod t_i) ◁ T;
  3) T/gp(prod t_i) is a group with the strong unique product property."
- l.252--254: "Theorem 1'. Any unimodular generalized equation over a
  torsion-free group is solvable over it."

## 2. The argument

1. **The canonical cut.** For a cyclically reduced degree-one word
   `g_1 t^(k_1) ... g_n t^(k_n)`, the height walk `h_j` has drift `+1` per period.
   The first maximum in a period is the unique rotation after which all heights
   of the period are `<= 0`. Then `v = w t^(-1) = prod g_j^[i_j]` with
   `i_j = -h_j in [0, s]`, a reduced word in `P_s`.
2. **Form (1) directly.** Cut `v` at the last mark of each bottom run
   (index `0`) and of each top run (index `s`). The pieces are `b_i`,
   `h_i = t^(-1) a_i t` and `c`, and they satisfy 1)--3) of Lemma 3. Minimality
   is never needed.
3. **The sharpened simple fact.** For `u in (A*B) \ A`, `gp(A,u) = A * <u>_inf`
   iff the core of `u`, stripped of its `A`-syllables at both ends, has infinite
   order. A reduced word whose end syllables lie in one factor has finite order
   iff it is an odd inverse palindrome around a finite-order middle.
4. **Assembly.** The cores of `a_i` and `b_i` are the blocks of the top and
   bottom runs; the final bottom run sits in `c`. Lemma 2 gives `t~`, and
   `psi : G * <t> -> H~` is the identity on `P_m` and kills `w`.

**Sanity.**
- **Theorem A.** If all coefficients have infinite order, every block does.
- **Sign-index two.** With exactly two sign changes, the constrained blocks are
  exactly the two sign-change coefficients: the degree-one case of
  `kl-sign-index-two-infinite-order-loops-inject` (Stallings /
  Clifford--Goldstein as recorded on main). Test T4 below.

## 3. The two-level case

- **Reduction to index two.** For `n = 2` every word over `P_0 = H<a>` has only
  the two levels `H` and `aH`. So the `n = 2` case of the target is
  Kervaire--Laudenbach over every group with a torsion-free normal subgroup of
  index two (after localization). The locally indicable case is Krstic
  (locally 2-indicable). The hyperlinear case is Pestov.
- **Where torsion sits.** In `P_0`, coefficients at level-preserving corners
  lie in `H`, hence are trivial or of infinite order. So torsion sits only at
  level changes, and for `n = 2` it consists of involutions.
- **The screen.** A violation needs a level-changing finite-order coefficient
  in the middle of an odd inverse-palindromic constrained block.
- **The known cases, and how the new theorem sits among them.**
  - The pivot-letter theorem allows torsion anywhere but needs one base-level
    letter.
  - The new theorem allows any letter distribution but constrains the torsion
    positions.

## 4. Attempts on the repeated-base-letter case that did not close it

1. **An equivariant change of variables.** An automorphism of
   `H * F(t_0, t_1)` commuting with the symmetry `t_0 -> t_1 -> z t_0 z^(-1)` has
   circulant abelianization `[[p', q'], [q', p']]`. Invertibility forces
   `p'^2 - q'^2 = ±1`, so `(p', q')` is `(±1, 0)` or `(0, ±1)`, which is not a
   new shape. So no equivariant Nielsen move turns a repeated base letter into a
   pivot.
2. **Symmetric words.** If `a w a^(-1)` is `M`-conjugate to `w^(±1)`, the
   rewritten system collapses to one relator with coprime degrees, which
   Klyachko solves. But invariance forces all level degrees equal (or
   alternating), so `deg w` is divisible by `n` (or is `0`). There are no
   degree-one symmetric words.
3. **Generalized equations.** Theorem 1' solves one generalized equation. The
   kernel system has two relators whose coefficients are twisted by `sigma`,
   and they cannot be merged into one relator. Treating `<a>` as part of the
   variable group loses the relations `a h a^(-1) = sigma(h)`, so a solution
   over `H` is not a solution over `P`.
4. **Substituting a word for `t`.** `t -> T(x)` with `deg T = ±1` maps
   `P_w -> P_(phi(w))` over `P`. But it multiplies letter counts at every level
   unless adjacent copies of `T` cancel, which needs trivial coefficients. It
   gives no pivot.
5. **The kernel presentation.** The star graph and pictures of the rewritten
   system over `H` cover those of `<P, t | w>`. A trivial star-graph cycle
   through an involution corner lifts to a trivial path. So weight tests are
   equivalent in the two presentations, and passing to the kernel gains
   nothing.
6. **Adjunction, one unknown at a time.** From `H * <t_1>`, adjoin `t_0` through
   `r_0` (Klyachko, degree one in `t_0` when `deg_u W = ±1`). The closing relator
   `r_1` then adds no unknown; this is the obstruction recorded in the target.
   Not resolved.

## 5. Model test (MSI job 794612)

Script `research/artifacts/hl-kl-two-level-words-2026-09-14-extremetest.py`.
Exact normal forms in free products of `S_3`, `Z/4` and `Z`; no external
packages.
- **T1.** Random degree-one words over `S_3`, `Z/4`, `Z`. Check that the
  canonical cut is unique and equals the first maximum, all indices lie in
  `[0, s]`, the pieces `b_i, h_i, c` have the stated index ranges, and they
  concatenate to `v`.
- **T2.** Random `u in (A*B) \ A`, with `A` and `B` among `S_3`, `Z/4` and `Z`.
  - If the core has infinite order, no random reduced `omega in A * <z>` maps
    to `1`.
  - If the core has finite order `k`, `(x^(-1) z x'^(-1))^k` maps to `1`.
- **T3.** For random blocks, the odd-inverse-palindrome criterion agrees with a
  direct cyclic-reduction computation of finite order.
- **T4.** For sign-index-two degree-one words, the constrained blocks are
  exactly the two sign-change coefficients.

Output: see section 5.1 (filled in from the job log).

### 5.1 Output

Job 794612 (MSI, 7 s), script md5 `fb2c1eafca88632fb6de56cad7b893a9`, verbatim:

```text
T3 palindrome-vs-cyclic-reduction trials=3139 failures=0
T2 stripped-core trials: infinite=1621 finite=1163 failures=0
T1 canonical-cut decomposition trials=3000 failures=0
T4 sign-index-two constrained blocks trials=1500 failures=0
TOTAL_FAILURES 0
```

**Incident.** The first submission, job 794056, hung and was cancelled. The
random block generator retried forever at lengths where no reduced word with
same-factor ends exists (`L = 2`, or `L` even with two factors). The fix bounds
the retries and skips those lengths, so T3 ran 3139 of 4000 draws. No result
from 794056 was used.

**Scope of the test.** Normal forms are exact. Factor groups `S_3` and `Z/4`
give finite-order syllables; `Z` gives infinite-order ones.
- T2 checks injectivity only on random reduced words of bounded length, so it
  is evidence for item 1 of the free-factor claim, not a proof.
- The sharpness relation is checked exactly.
- Lemma 2 itself is not tested.

## 6. Exact gap

**G1.** The target's residue: two-level words whose canonical cut has a
constrained block that is an odd inverse palindrome around a finite-order
level-changing coefficient. The first cases are:
- `n = 2`, an involution `ha` at the unique global maximum or minimum of the
  height walk;
- that coefficient is a single-mark block.

No tool here reaches them. Next handles, not run:
- apply the theorem to `w` substituted by `t -> x t y`. This conjugates
  sign-change coefficients but moves same-sign coefficients, and can destroy
  inverse palindromes whose middle is a same-sign coefficient;
- compare the canonical cuts of `w` and of its time-reversed conjugate
  `(w(t^(-1)))^(-1)`, which exempt different bottom runs.

**G2.** Beyond two levels, the general square system of `hl-howie-systems`
remains, but the theorem applies to any word directly, whatever its level
structure.

**Not read at source:** Stallings' sign-index-two paper and Clifford--Goldstein
(the consistency check uses main's recorded statement), Fenn--Rourke 1996, and
any post-1993 literature that may already record this form of Klyachko's
hypothesis. No novelty is claimed.
