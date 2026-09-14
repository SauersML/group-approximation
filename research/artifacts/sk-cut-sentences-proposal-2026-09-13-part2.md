# sk-cut-sentences proposal, part 2: items C12–C19, checks, KEEP list, hand-offs (2026-09-13)

Line numbers refer to `$SK/manuscript-disk-1646.tex` (340 lines). Part 1 has the summary table and C1–C11.

## C12. Subsection title (l.154), 0
Before: `\subsection*{A finite tower detects every normal subgroup}`
After: `\subsection*{Simplicity}`
Trade-off: "detects" is a metaphor. The new title matches the other two titles ("The ring and property (T)", "Finite models") and names the property proved. sk-exposition proposes the same change.

## C13. l.171, 0
Before: `provided the larger tower is disjoint. To see this, multiplying`
After: `provided the larger tower is disjoint. Indeed, multiplying`

## C14. No translates (l.178–193), −3
Before:
```
Choose a finite clopen partition $\mathcal P$ refining the letter
partition, with $C\cap T^jC=\varnothing$ for $C\in\mathcal P$ and
$0<|j|\le2w+3$. Some matrix
\[
 h=e_{ij}(s),\qquad
 s\in\{e_C,e_Cu,e_Cu^{-1}:C\in\mathcal P\},
\]
does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form
a subring containing all ring generators, so $g\in Z(G)=\{1\}$.

Each such $s$ lies in $B_1(U)$ for a translate $U$ of $C$:
\[
 e_C=E_{00}(C),\quad e_Cu=E_{10}(T^{-1}C),\quad
 e_Cu^{-1}=E_{-1,0}(TC).
\]
```
After:
```
Choose a finite clopen partition $\mathcal P$ refining the letter
partition, with $U\cap T^jU=\varnothing$ for $U\in\mathcal P$ and
$0<|j|\le2w+3$. Some matrix
\[
 h=e_{ij}(s),\qquad
 s\in\{e_U,e_Uu,e_Uu^{-1}:U\in\mathcal P\},
\]
does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form
a subring containing all ring generators, so $g\in Z(G)=\{1\}$.
This $s$ lies in $B_1(U)$ for its $U\in\mathcal P$, since $e_U=E_{00}(U)$,
$e_Uu=E_{0,-1}(U)$ and $e_Uu^{-1}=E_{01}(U)$.
```
Trade-off:
- The translates are unnecessary: both off-diagonal generators already lie in the tower over the partition set itself (M2).
- A display, the renaming C → U, and the letter C all go.
- The constant 2w+3 is left to sk-arbitrary, since only 2w+2 is used.

## C15. Transvection display (l.205–215), −4
Before:
```
Let $H_W$ be the copy of $\GL_d(\F_2)$ acting on the tower over $W$
and as the identity elsewhere. It lies in $G$. Indeed, index its
coordinates by $(p,a)$, where $1\le p\le3$ and $|a|\le m$.
A transvection between $(p,a)$ and $(q,b)$ with $p\ne q$ is
$e_{pq}(E_{ab}(W))$. For $p=q$ and $a\ne b$, take $q\ne p$ and use
\[
 [e_{pq}(E_{ab}(W)),e_{qp}(E_{bb}(W))]
       =I_3+E_{ab}(W)E_{pp}.
\]
This follows from $E_{ab}E_{bb}=E_{ab}$ and $E_{bb}E_{ab}=0$.
These transvections generate $H_W$.
```
After:
```
Let $H_W$ be the copy of $\GL_d(\F_2)$ acting on the tower over $W$
and as the identity elsewhere. It lies in $G$. Indeed, index its
coordinates by $(p,a)$, where $1\le p\le3$ and $|a|\le m$.
A transvection between $(p,a)$ and $(q,b)$ with $p\ne q$ is
$e_{pq}(E_{ab}(W))$. The other transvections are commutators of these,
since $[t_{xy},t_{yz}]=t_{xz}$ for distinct coordinates $x,y,z$, and
transvections generate $H_W$.
```
Trade-off:
- The display re-derives, in 3×3 notation, the standard identity for transvections in GL_d(F_2). The new sentence uses that identity directly (M3).
- It also removes the self-contradicting "For p=q ... take q≠p", which sk-referee-1 flagged.

## C16. Doctrine words, 0
- l.197: "Its corner part is invertible and therefore corresponds to" → "Its corner part is invertible, so it corresponds to".
- l.217: "Over $\F_2$, the group" → "The group". The field is already in the formula.
- Same kind of change folded into other items: "hence" at l.31 (C2), l.113 (C9), l.143 (C11), and "Hence" at l.99 (C7).

## C17. l.227, 0
Before: `simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$`
After: `simple, $I_N=R$. So $N=G$.\hfill$\square$`
Trade-off: the □ already marks the end of the proof.

## C18. l.233, 0
Before: `simple Kazhdan LEF group. Consequently, there are continuum many`
After: `simple Kazhdan LEF group. In particular, there are continuum many`

## C19. Irrational representative (l.257–261), −1
Before:
```
Every Turing degree has an irrational representative: use $\sqrt2-1$
for the computable degree, and interleave the characteristic sequence
of a noncomputable set with $1$'s in a binary expansion for any other
degree. There are continuum many degrees, and the word-problem degree
of a finitely generated group is an isomorphism invariant.
```
After:
```
Every Turing degree has an irrational representative: interleave the
binary digits of $\sqrt2-1$ with the characteristic sequence of a set
in that degree. There are continuum many degrees, and the word-problem
degree of a finitely generated group is an isomorphism invariant.
```
Trade-off:
- One rule for every degree, instead of two cases (M5).
- An equally short alternative (sk-referee-2, sk-exposition): drop the interleaving, since a noncomputable set's binary expansion is not eventually periodic. That still needs √2−1 for the computable degree.
- sk-word-problem owns the final choice, and may replace the Sturmian argument altogether.

## Checks of the replacements that carry mathematics
M1 (C6).
- With the other convention x^{-1}y^{-1}xy, the pair x = e_ik(r), y = e_kj(s) gives e_ik(−r)e_kj(−s)e_ik(r)e_kj(s). That is the standard commutator of e_ik(−r) and e_kj(−s), namely e_ij((−r)(−s)) = e_ij(rs). So (1) holds under both conventions in any ring.
- The other commutators in the note:
  - k = [g,h] lies in N∖{1} under either convention, since g and h do not commute;
  - the transvection identity (C15) holds in characteristic 2 under either convention, because transvections are involutions;
  - the level-ideal step uses only (1).
- So no formula in the note depends on the convention.

M2 (C14).
- E_{0,−1}(U) = e_{T^0U}u^{0−(−1)} = e_Uu and E_{01}(U) = e_Uu^{−1}, with both indices in [−1,1]. So s ∈ B_1(U) for U ∈ 𝒫.
- The later steps need the levels T^aU, |a| ≤ w+1, to be disjoint: by (2), gsg^{−1} and the factors of k−I_3 lie in B_{w+1}(U).
- That condition is U∩T^jU = ∅ for 0<|j| ≤ 2w+2, which 𝒫 satisfies. The disk version needs the same bound for its translates.

M3 (C15).
- For distinct coordinates x, y, z of F_2^d, the transvections t_xy = I+E_xy satisfy t_xy t_yz t_xy^{−1} t_yz^{−1} = t_xz.
- For x = (p,a) and z = (p,b) with a≠b, take y = (q,b) with q≠p. Then y≠x, y≠z, t_xy = e_pq(E_ab(W)) and t_yz = e_qp(E_bb(W)).
- So every elementary transvection of H_W lies in G, and these generate GL_d(F_2) = SL_d(F_2).

M4 (C9). A 3×3 matrix that commutes with every e_ij(1), i≠j, is scalar, cI_3 with c ∈ R. Commuting with every e_ij(r) forces c ∈ Z(R) = F_2, and a unit of F_2 is 1.

M5 (C19).
- Put x = Σ_i (b_i 2^{−2i−1} + a_i 2^{−2i−2}), where (b_i) are the binary digits of √2−1 and (a_i) is the characteristic sequence of A.
- The digit subsequence (b_i) is not eventually periodic, so x is irrational and its binary expansion is unique.
- x computes A by reading alternate digits, and A computes x because (b_i) is computable.

## KEEP (every other sentence), with the need it serves
- l.38–41: the question lineage (user's decision; not assessed).
- l.44–53: the theorem. Every clause is a property the note proves; which clauses to state is sk-cut-structure's call.
- l.63–65: Thom. The reader learns that a Kazhdan LEF group that is not residually finite was already known, so simplicity is the addition.
- l.70–82: conventions, ufu^{−1}=f∘T^{−1}, no periodic points, clopen partitions. Used at l.105–107, l.139–140 and l.178–180.
- l.84–95: generators of R, e_ij(r), (1), generators of G. Used for (T) through finite generation, and at l.185–187 and l.247.
- l.105–113: direct proof that R is simple with centre F_2. Used at l.187 and l.226.
- l.119–120: the definition of LEF. It is the theorem's key term, and l.146–149 checks exactly its partial-homomorphism clause.
- l.123–149: finite models. Each sentence carries a step (windows, joins, large N, injectivity, inverses).
- l.155–173: towers, matrix units, absorption (2). Used at l.195.
- l.175–187, 194–203, 217–227: the simplicity steps.
- l.238–256, 260–261: the word-problem steps.
- l.264–269: origin and authorship (user's decision; not assessed).

## Maximal cut, and what was added back
The maximal cut also deleted the second intro paragraph entirely (l.55–65), the groupoid citation in C8, and the LEF definition (l.119–120). It came to about 306 lines. Added back:
- the merged EJZ/GM/Stepanov sentence (C5): without it "the new step" has nothing to contrast with, and the reader cannot tell what is new or whom to credit;
- Thom: the nearest known example, which locates the novelty;
- the [BCFS, ClarkEdie, Steinberg] citation: credit for facts the note re-proves;
- the LEF definition: two lines, and the reader needs its partial-homomorphism convention to check l.146–149.

The final candidate is 317 lines.

## Hand-offs (not proposed here)
- sk-cut-structure:
  - the word-problem section as a whole (l.229–262, 34 lines, the note's only source of "continuum many");
  - the direct proof that R is simple, versus citation only;
  - the theorem clauses.
- sk-arbitrary: 2w+3 → 2w+2 (M2); d ≥ 9, where only d ≥ 3 is used; the redundant generator 1; EL_3 → EL_n.
- sk-referee-1, sk-referee-2 P1: the wording "separated by a segment w" at l.125–127 is ambiguous (the segment must start at the first occurrence). Both referees already propose a repair.
- sk-exposition, sk-referee-1: letter clashes, k (window radius and commutator) and w (periodic word and exponent bound).
- sk-citations: whether [Pestov] states LEF ⇒ sofic (C11), and whether an accurate credit sentence should replace the Nekrashevych pointer (C4).

## Status
- Editorial proposal; no Cairn node.
- This lane checked M1–M5, and they are queued with sk-referee-1 as `sk-cut-sentences-M1-M5`.
- No .tex was edited.
