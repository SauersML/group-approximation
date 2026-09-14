# sk-arbitrary proposal, part 1: unforced choices in the tower argument (2026-09-13)

Lane sk-arbitrary (SK swarm). Source: `simple_kazhdan_sofic_group.tex`, the disk version from 16:46 (340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99). Line numbers below are its line numbers.
Status: every item was re-derived by this lane. None has been reviewed yet; the request is queued with sk-referee-1. Nothing was applied to any .tex.
Part 2: EL_n, F_2, notation clashes, the unused simplicity of R, the Sturmian encoding, and the forced choices. Part 3: the combined candidate text.

## A1. Seed 1 (tower bound 2w+3). VERIFIED: 2w+2 suffices, and the canonical form is "levels |a| ≤ w+1 disjoint"
Only B_m(C) with m = w+1 is used:
- h − I has entries in B_1(C);
- the entries of g(h−I)g^{-1} are sums r s r' with exponents of r, r' at most w, so they lie in B_{1+w}(C);
- multiplying by h^{-1} = I + sE_ij stays inside the ring B_m(C).

B_m(C) is a matrix ring iff C ∩ T^jC = ∅ for 0<|j| ≤ 2m = 2w+2. The original translates U = T^{∓1}C wander exactly as C does, so even the original text needs only 2w+2.

Before (l.180): `$0<|j|\le2w+3$. Some matrix`
After: `$0<|j|\le 2m$, where $m=w+1$. Some matrix` (with `and $m=w+1$` deleted from l.194)
Length: 0. Reader: the constant is the one that is used, so the reader stops looking for where the extra 1 is needed.

## A2. NEW: define the matrix units convention-free as E_ab(W) = u^a e_W u^{-b}
This is the same element: u^a e_W u^{-b} = (u^a e_W u^{-a})u^{a-b} = e_{T^aW}u^{a-b} under l.76.
- Product rule: E_ab(W)E_cd(W') = u^a e_W u^{c-b} e_{W'} u^{-d}. For b = c this is E_ad(W∩W'). For b ≠ c it is 0, because u^{c-b}e_{W'}u^{b-c} = e_{T^{±(c-b)}W'} and U ∩ T^{±j}U = ∅ for 0<|j| ≤ 2m, whichever sign convention is used.
- Absorption: f u^i E_ab(W) = u^{a+i}(u^{-a-i} f u^{a+i}) e_W u^{-b} = E_{a+i,b}(W_1), where u^{-a-i}fu^{a+i} ∈ LC(X) and W_1 ⊆ W is clopen. Similarly E_ab(W) f' u^j = E_{a,b-j}(W_2).
- The span is B_m(U) ≅ M_{2m+1}(LC(U,F_2)). The coefficient of u^j is a sum of functions supported on the disjoint levels, so the map is injective.

Before (l.155-173):
```
Suppose the levels $T^aU$ are disjoint for all indices needed below.
For $|a|,|b|\le m$ and clopen $W\subseteq U$, put
\[
  E_{ab}(W)=e_{T^aW}u^{a-b}.
\]
These satisfy
$E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$.
Their span is a subring
\[
  B_m(U)\cong M_{2m+1}(\LC(U,\F_2)),
\]
with unit $e_{\bigcup_{|a|\le m}T^aU}$. If $r,r'$ involve only powers
$u^j$ with $|j|\le w$, then
\begin{equation}\label{eq:absorb}
  r B_m(U)r'\subseteq B_{m+w}(U),
\end{equation}
provided the larger tower is disjoint. To see this, multiplying
$E_{ab}(W)$ on the left by $fu^i$ and on the right by $f'u^j$ changes
its indices to $(a+i,b-j)$ and restricts its clopen coefficient.
```
After:
```
Let $U$ be clopen with $U\cap T^jU=\varnothing$ for $0<|j|\le2m$.
For $|a|,|b|\le m$ and clopen $W\subseteq U$, put
$E_{ab}(W)=u^ae_Wu^{-b}$. Then
$E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$, so their span is a subring
\[
  B_m(U)\cong M_{2m+1}(\LC(U,\F_2)),
\]
with unit $\sum_{|a|\le m}E_{aa}(U)$. If $r,r'$ involve only powers
$u^j$ with $|j|\le w$, and $U\cap T^jU=\varnothing$ for $0<|j|\le2(m+w)$, then
\begin{equation}\label{eq:absorb}
  r B_m(U)r'\subseteq B_{m+w}(U),
\end{equation}
since $fu^iE_{ab}(W)=u^{a+i}(u^{-a-i}fu^{a+i})e_Wu^{-b}=E_{a+i,b}(W_1)$
for a clopen $W_1\subseteq W$, and similarly on the right.
```
Length: −4. Reader: "the indices needed below" becomes an explicit condition, the product rule and absorption read off in one line each, and the formulas no longer depend on the T versus T^{-1} convention.

## A3. Seed 2 (translates). VERIFIED: unnecessary
With A2: E_{0,-1}(C) = u^0 e_C u^{1} = e_C u, and E_{0,1}(C) = e_C u^{-1}. So every s lies in B_1(C) itself, and U = C throughout. This check does not depend on A2: with the old definition, E_{0,-1}(C) = e_{T^0C}u^{0-(-1)} = e_Cu as well.

Before (l.189-194):
```
Each such $s$ lies in $B_1(U)$ for a translate $U$ of $C$:
\[
 e_C=E_{00}(C),\quad e_Cu=E_{10}(T^{-1}C),\quad
 e_Cu^{-1}=E_{-1,0}(TC).
\]
Set $k=[g,h]\in N\setminus\{1\}$ and $m=w+1$.
```
After:
```
Since $e_C=E_{00}(C)$ and $e_Cu^{\pm1}=E_{0,\mp1}(C)$, we have $s\in B_1(C)$.
Set $g'=[g,h]\in N\setminus\{1\}$.
```
In the rest of l.195-204, `U` becomes `C`. The renaming of k to g' is item A11 in part 2.
Length: −4. Reader: removes a display and the word "translate", and one tower serves every case.

## A4. Seed 3 (d ≥ 9). VERIFIED: noise
The only use of d is the simplicity (and trivial centre) of GL_d(F_2) for d ≥ 3 (l.217-218). And d = 3(2m+1) ≥ 3 for every m ≥ 0.
Before (l.200): `\kappa:U\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1)\ge9.`
After: `\kappa:C\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1).`
Length: 0. Reader: an unused bound invites a search for its use.

## A5. Seed 4 (generator 1). VERIFIED: redundant, but u^{-1} is not
- 1 = Σ_a e_a, so e_ij(1) = Π_a e_ij(e_a). The subring used at l.185-187 contains 1 for the same reason.
- u^{-1} is forced. The subring generated by LC(X) and u is R_+ = {Σ_{j≥0} f_j u^j}. The subgroup generated by the e_ij(R_+) lies in GL_3(R_+), which does not contain e_12(u^{-1}).

Before (l.94-96):
```
show that the matrices $e_{ij}(s)$, for
$s\in\{1,u,u^{-1}\}\cup\{e_a:a\in A\}$, generate $G$.
Here $[g,h]=ghg^{-1}h^{-1}$.
```
After:
```
show that the matrices $e_{ij}(s)$, for
$s\in\{u,u^{-1}\}\cup\{e_a:a\in A\}$, generate $G$.
```
This also applies A6. Length: −1.

## A6. Seed 5 (commutator convention). VERIFIED: irrelevant to every use
- (1): e_ik(-r)e_kj(-s)e_ik(r)e_kj(s) = e_ij((-r)(-s)) = e_ij(rs). Both conventions give [e_ik(r),e_kj(s)] = e_ij(rs), and over F_2 the signs vanish anyway.
- l.194, l.219 and l.223-226 only use that a commutator with an element of N lies in N.
- l.211-212: with X = I+rE_pq, Y = I+sE_qp, rs = r and sr = 0, one gets XY = (I+rsE_pp)YX, and I+rsE_pp commutes with YX. So X^{-1}Y^{-1}XY = XYX^{-1}Y^{-1} = I+rsE_pp.

Deleting l.96 is safe (see A5). Reader: one fewer sentence, and no loss.

## A7. Seed 6 (the E_bb commutator display). VERIFIED: it is the Steinberg relation [t_xy, t_yz] = t_xz
Take x = (p,a), y = (q,b), z = (p,b) with q ≠ p and a ≠ b. Then t_xy = e_pq(E_ab(W)), t_yz = e_qp(E_bb(W)), and [t_xy,t_yz] = t_xz = I+E_ab(W)E_pp. This holds under either commutator convention (A6).

Before (l.205-215):
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
and as the identity elsewhere. Index its coordinates by $(p,a)$, where
$1\le p\le3$ and $|a|\le m$. The transvections $e_{pq}(E_{ab}(W))$ with
$p\ne q$ lie in $G$, and their commutators give the remaining
transvections, so $H_W\subseteq G$.
```
Length: −6. Reader: states the one fact the argument needs (every transvection of H_W is a product of elementary matrices of G) with the standard identity in place of a display.
