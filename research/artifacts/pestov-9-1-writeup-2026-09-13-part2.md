# An infinite simple Kazhdan group that is sofic: Part 2 of 3

Lane `ex-pestov91-harden`, 2026-09-13. It stays in this repository: publishing outside needs the user's approval.
Notation, §§0–4 and Lemmas 3.x are in Part 1 (`pestov-9-1-writeup-2026-09-13-part1.md`):
- $X$ is an infinite minimal subshift, $T$ the shift, $\alpha(f) = f \circ T^{-1}$;
- $R = LC(X,\mathbb F_q) \rtimes \mathbb Z$, $G = EL_3(R)$, $S = G/Z(G)$;
- $B_m(U)$ is the tower subring of Part 1 §3.5, with matrix units $E_{ab}(W)$.

This part proves that $G$ and $S$ are LEF (§5), constructs finite simple approximants (§5.4), and proves that every
normal subgroup of $G$ is central or everything (§6).

## 5. Local embeddability into finite groups

### 5.1 Periodic models

Fix $k \ge 1$. By (U) of Part 1 §3.1 choose a point $x \in X$, a word $v \in L_{2k}(X)$, and two occurrences of $v$ in
$x$ at positions $p < p'$ with $N := p' - p \ge \max(2k+1,\ \ell(2k+1))$. Put $w = x_{[p,p')}$ and let $y$ be the
$N$-periodic sequence with $y_{[0,N)} = w$.

**Lemma 5.1.** $L_{2k+1}(y) = L_{2k+1}(X)$.

*Proof.*
- **$\subseteq$.** A window of $y$ of length $\ell \le 2k+1 \le N$ contains at most one seam, that is, at most one
  pair of consecutive positions $(mN-1, mN)$: two seams need $\ell \ge N+2$. A window without a seam is a subword
  of $w$, hence of $x$. A window with a seam is $\mathrm{suffix}_s(w)\,\mathrm{prefix}_t(w)$ with $s, t \ge 1$ and
  $s+t \le 2k+1$, so $t \le 2k$. Since $v$ is a prefix of $w$ and $x_{[p',p'+2k)} = v$, we have
  $\mathrm{prefix}_t(w) = x_{[p',p'+t)}$, while $\mathrm{suffix}_s(w) = x_{[p'-s,p')}$. So the window is
  $x_{[p'-s,p'+t)} \in L(X)$.
- **$\supseteq$.** $|w| \ge \ell(2k+1)$, so every word of $L_{2k+1}(X)$ occurs in $w$.

$\square$

**Model maps.** Let $P$ be the cyclic shift $\delta_n \mapsto \delta_{n+1}$ on $\mathbb F_q^{\mathbb Z/N}$. A function
$f \in LC(X,\mathbb F_q)$ has *radius* $\le \rho$ if $f(x) = \Phi(x_{[-\rho,\rho]})$ for some $\Phi$. For
$\rho \le k$ put
$$D_k(f) = \mathrm{diag}\big(\Phi(y_{[n-\rho,\,n+\rho]})\big)_{n \in \mathbb Z/N}.$$
This is well defined. If $\Phi$ and $\Phi'$ (radii $\rho, \rho' \le k$) both represent $f$, the window
$y_{[n-K,n+K]}$, $K = \max(\rho,\rho')$, lies in $L(X)$ by Lemma 5.1. So it equals $x_{[-K,K]}$ for some $x \in X$,
and both formulas give $f(x)$. $D_k$ is a ring homomorphism on functions of radius $\le k$, because it is evaluation
at points. Set
$$\psi_k\Big(\sum_j f_ju^j\Big) = \sum_j D_k(f_j)\,P^j.$$

**Lemma 5.2.**
- (a) If $g$ has radius $\rho$ and $\rho + |i| \le k$, then $P^iD_k(g)P^{-i} = D_k(\alpha^i(g))$.
- (b) $\psi_k$ is additive and unital. Suppose every coefficient radius $\rho$ and every exponent $i$ occurring in
  $r$ and $r'$ satisfy $\rho + |i| \le k$. Then $\psi_k(rr') = \psi_k(r)\psi_k(r')$.
- (c) If $r \ne 0$, then $\psi_k(r) \ne 0$ for all sufficiently large $k$.

*Proof.*
- (a) $P^iD_k(g)P^{-i}\delta_n = \hat g(n-i)\,\delta_n$, where $\hat g(n) = \Phi_g(y_{[n-\rho,n+\rho]})$. Also
  $\alpha^i(g)(x) = g(T^{-i}x) = \Phi_g(x_{[-\rho-i,\,\rho-i]})$ has radius $\le \rho+|i|$. At position $n$ it reads
  $\hat g(n-i)$.
- (b) By (a), $\psi_k((fu^i)(gu^j)) = D_k(f)\,D_k(\alpha^i g)\,P^{i+j} = D_k(f)P^i\,D_k(g)P^j$; extend bilinearly.
- (c) Let $f_j \ne 0$, nonzero on a word of $L_{2\rho+1}(X)$. For $k \ge \rho$ that word occurs in $y$ (Lemma 5.1),
  so $D_k(f_j) \ne 0$. The term $D_k(f_j)P^j$ is supported on the entries $(n+j, n)$. Once $N > 2\max|j|$, distinct
  exponents occupy disjoint entries, so no cancellation occurs.

$\square$

### 5.2 An embedding into an ultraproduct of matrix algebras

Choose the data of §5.1 for every $k$, with sizes $N_k$, and fix a nonprincipal ultrafilter $\omega$ on
$\mathbb N$. For $r \in R$ put $\Psi(r) = [\psi_k(r)]_\omega \in \prod_\omega M_{N_k}(\mathbb F_q)$, taking arbitrary
values at the finitely many $k$ where $\psi_k(r)$ is not defined.

**Proposition 5.3.** $\Psi$ is an injective unital ring homomorphism, and $\Psi(\lambda) = \lambda I$ for
$\lambda \in \mathbb F_q$.

*Proof.* Each identity $\Psi(r+r') = \Psi(r)+\Psi(r')$ and $\Psi(rr') = \Psi(r)\Psi(r')$ holds at all large $k$ by
Lemma 5.2(b), hence $\omega$-almost everywhere. Injectivity is Lemma 5.2(c). Constants have radius 0. $\square$

### 5.3 $G$ and $S$ are LEF, hence sofic and hyperlinear

A group $\Gamma$ is *LEF* if for every finite $F \subseteq \Gamma$ there are a finite group $Q$ and an injective map
$\phi : F \to Q$ with $\phi(gh) = \phi(g)\phi(h)$ whenever $g, h, gh \in F$.

**Lemma 5.4.** Every subgroup of an algebraic ultraproduct $\prod_\omega Q_k$ of finite groups is LEF.

*Proof.* Choose representatives for the elements of $F$. The finitely many identities $gh = g'$ and inequalities
$g \ne g'$ among elements of $F$ each hold on an $\omega$-large set of indices. A finite intersection of such sets is
nonempty, and any $k$ in it gives $\phi$. $\square$

**$G$ is LEF.** $\Psi$ induces an injective ring homomorphism
$M_3(R) \to \prod_\omega M_{3N_k}(\mathbb F_q)$. The units of the target are $\prod_\omega GL_{3N_k}(\mathbb F_q)$,
so $G \le GL_3(R)$ embeds in an ultraproduct of finite groups.

**$S$ is LEF.** Put $\Lambda = \{\lambda \in \mathbb F_q^\times : \lambda I_3 \in G\}$. Then $Z(G) = \Lambda I_3$ by
§6.4 below. Let $C = \Lambda I$, a finite central subgroup of every $Q_k = GL_{3N_k}(\mathbb F_q)$.
- **The target.** The map $\prod_\omega Q_k \to \prod_\omega(Q_k/C)$ is onto. Its kernel consists of the $[a_k]$ with
  $a_k \in C$ for $\omega$-almost every $k$. Since $C$ is finite, such an element is $\omega$-almost everywhere
  constant, equal to some $[\lambda I]$.
- **The kernel on $G$.** If $\Psi(g) = [\lambda I] = \Psi(\lambda I_3)$, then $g = \lambda I_3 \in Z(G)$ by
  injectivity.

So $S = G/Z(G)$ embeds in $\prod_\omega(Q_k/C)$ and is LEF by Lemma 5.4.

**Sofic and hyperlinear.** Apply LEF to $F \cup F\cdot F$ and compose with the left regular action of $Q$ on itself.
This gives permutations $\sigma(g)$ of the finite set $Q$ that are exactly multiplicative on $F$. For $g \ne 1$,
$\sigma(g)$ has no fixed point. So $S$ is sofic. The permutation matrices are unitaries with
$\|\sigma(g) - I\|_{2} = \sqrt 2$ in normalized Hilbert–Schmidt norm, so $S$ is hyperlinear. $\square$

### 5.4 Finite simple approximants

Replace $w$ in §5.1 by its primitive root $z$ ($w = z^e$, $z$ not a proper power). This leaves $y$ unchanged, so
Lemmas 5.1–5.2 still hold with $N_k = |z|$.

- **Sizes.** An aperiodic sequence has at least $m+1$ words of length $m$ (Morse–Hedlund). A cyclic word of length
  $N$ has at most $N$ cyclic windows. With Lemma 5.1, $N_k \ge 2k+2$.
- **Generation.** The images of the generators $u^{\pm1}$, $\chi_{[x_0=a]}$ and $\lambda$ are $P^{\pm1}$, the
  diagonal matrices $D_a$ of the positions of $a$, and $\lambda I$. $P^iD_aP^{-i}$ is the indicator of the positions
  $n$ with $y_{n-i} = a$. The rotations of a primitive word are distinct, so these indicators and their complements
  separate positions. Hence every diagonal matrix unit, and with $P$ every matrix unit, lies in the ring they
  generate. They generate $M_{N_k}(\mathbb F_q)$.
- **The groups.** The generators $e_{ij}(s)$, $s \in \{1, u^{\pm1}, \chi_{[x_0=a]}, \lambda\}$, of $G$ go to
  generators of $EL_3(M_{N_k}(\mathbb F_q)) = SL_{3N_k}(\mathbb F_q)$. The scalar $\lambda$ is needed when $q$ is not
  prime.

**Proposition 5.5.** With these markings, $SL_{3N_k}(\mathbb F_q) \to G$ and $PSL_{3N_k}(\mathbb F_q) \to S$ in the
space of marked groups.

*Proof.* A word $\omega$ of length $n$ in the generators has a value $g_\omega \in G$ whose coefficient radii and
exponents are $O(n)$. By Lemma 5.2(b) its value in $SL_{3N_k}(\mathbb F_q)$ is $\psi_k(g_\omega)$ for $k \gg n$.
- **$SL$.** By Lemma 5.2(c), $\omega = 1$ in $G$ iff $\omega = 1$ in $SL_{3N_k}(\mathbb F_q)$ for all large $k$.
- **$PSL$.** If $g_\omega = \lambda I_3$, then $\psi_k(g_\omega) = \lambda I$ is scalar. Conversely, suppose
  $\psi_k(g_\omega)$ is scalar for infinitely many $k$. Then some $\mu \in \mathbb F_q^\times$ occurs infinitely
  often, so $\psi_k(g_\omega - \mu I_3) = 0$ infinitely often. Lemma 5.2(c) gives $g_\omega = \mu I_3 \in Z(G)$.

$\square$

## 6. Normal subgroups

### 6.1 The level ideal

For $N \trianglelefteq G$ put $I(N) = \{a \in R : e_{12}(a) \in N\}$.
- It is an additive subgroup.
- The Weyl elements $w_{ij} = e_{ij}(1)e_{ji}(-1)e_{ij}(1) \in G$ conjugate each $e_{kl}(a)$ to some
  $e_{k'l'}(\pm a)$, and every pair $k' \ne l'$ is reached. For example $w_{23}E_{13}w_{23}^{-1} = E_{12}$.
- Commutators of elements of $N$ with elements of $G$ lie in $N$. With
  $$[e_{12}(a), e_{23}(b)] = e_{13}(ab), \qquad [e_{31}(b), e_{12}(a)] = e_{32}(ba),$$
  this gives $ab, ba \in I(N)$ for $a \in I(N)$ and $b \in R$.

So $I(N)$ is a two-sided ideal. If $I(N) \ne 0$, then $I(N) = R$ by Part 1 §3.3. Then every $e_{ij}(r)$ lies in $N$,
so $N = G$.

### 6.2 Root detection

**Theorem 6.1.** If $N \trianglelefteq G$ contains $g \notin Z(G)$, then $I(N) \ne 0$.

**(a) A localized root that does not commute with $g$.** Let $w$ bound the propagation of all entries of $g$ and
$g^{-1}$, and put $L = 2w+3$. Let $\Sigma_L$ be the set of elements $\lambda\chi_C$, $\lambda\chi_Cu$ and
$\lambda\chi_Cu^{-1}$, with $\lambda \in \mathbb F_q$ and $C$ a cylinder of radius $\ge k_L$ (Part 1 §3.1(P)).
- **A subring.** The set $C_g = \{s : g$ commutes with $e_{ij}(s)$ for all $i \ne j\}$ is closed under $\pm$, and under
  products since $e_{ij}(st) = [e_{ik}(s), e_{kj}(t)]$.
- **It must fail.** The additive span of $\Sigma_L$ contains $1 = \sum_C\chi_C$, $u^{\pm1} = \sum_C\chi_Cu^{\pm1}$,
  every $\lambda$ and every letter indicator. If $\Sigma_L \subseteq C_g$, then $C_g = R$ and $g$ is central.
- **The root.** So some $h = e_{ij}(s)$ with $s \in \Sigma_L$ does not commute with $g$. Moreover $s \in B_1(U)$ for
  some $U \in \{C, T^{-1}C, TC\}$, since $\chi_C = E_{00}(C)$, $\chi_Cu = E_{10}(T^{-1}C)$ and
  $\chi_Cu^{-1} = E_{-1,0}(TC)$. Every translate of $C$ has return times $> L$.

**(b) Localization.** Put $k = [g,h] \in N$, so $k \ne 1$, and $m' = w+1$.
- **$k - I$.** The entries of $ghg^{-1} - I$ are $g_{pi}\,s\,(g^{-1})_{jq}$. They lie in $B_{m'}(U)$ by Lemma 3.6,
  since $2(1+w) < L$. Also $h^{-1} - I = -sE_{ij}$. With $X = ghg^{-1} - I$ and $Y = h^{-1} - I$,
  $k - I = X + Y + XY \in M_3(B_{m'}(U))$, and likewise $k^{-1} - I$.
- **The monoid $Q_U$.** Let $e = \chi_V$ be the unit of $B_{m'}(U)$ and put $Q_U = (1-e)I_3 + M_3(B_{m'}(U))$. It
  is closed under products, because $(1-e)b = b(1-e) = 0$ for $b \in B_{m'}(U)$. Through
  $$M_3(B_{m'}(U)) \cong M_3\big(M_{2m'+1}(LC(U,\mathbb F_q))\big) \cong LC(U, M_d(\mathbb F_q)),
  \qquad d = 3(2m'+1) \ge 9,$$
  its multiplication is pointwise in $x \in U$.
- **The function $\kappa$.** $k \in Q_U$ corresponds to a locally constant $\kappa : U \to GL_d(\mathbb F_q)$ with
  $\kappa \not\equiv I$.

**(c) Some value $\kappa(x_0)$ is not scalar.** Choose a clopen $W \ni x_0$ in $U$ with $\kappa|_W = \kappa_0$.
- **The copy of $GL_d$.** For $\varepsilon \in GL_d(\mathbb F_q)$ let $\iota_W(\varepsilon) \in Q_U$ be the element
  corresponding to the function equal to $\varepsilon$ on $W$ and to $I$ on $U \setminus W$. Explicitly,
  $\iota_W(\varepsilon) = (1-\chi_{V_{m'}(W)})I_3 + \sum \varepsilon_{(p,a),(p',b)}\,E_{ab}(W)\,E_{pp'}$.
- **$\iota_W(SL_d) \le G$.** $SL_d(\mathbb F_q)$ is generated by the transvections $t = I + c\,e_{(p,a),(p',b)}$.
  - If $p \ne p'$, then $\iota_W(t) = e_{pp'}(c\,E_{ab}(W)) \in G$.
  - If $p = p'$, then $a \ne b$. Put $x = cE_{ab}(W)$ and $y = E_{bb}(W)$, so $xy = x$, $yx = 0$ and $x^2 = 0$. For
    $p'' \ne p$ the matrices $A = xE_{pp''}$ and $B = yE_{p''p}$ satisfy $A^2 = B^2 = BA = 0$ and $AB = xE_{pp}$.
    Hence $[e_{pp''}(x), e_{p''p}(y)] = (I+A)(I+B)(I-A)(I-B) = I + xE_{pp} = \iota_W(t)$.
- **Commutators.** Multiplication in $Q_U$ is pointwise, so $[k, \iota_W(\varepsilon)] = \iota_W([\kappa_0,\varepsilon])$.
  The group $N_W = \{\varepsilon \in SL_d(\mathbb F_q) : \iota_W(\varepsilon) \in N\}$ is normal in $SL_d(\mathbb F_q)$
  and contains every $[\kappa_0, \varepsilon]$.
- **$N_W$ is noncentral.** If $N_W$ were central, then $\varepsilon \mapsto [\kappa_0,\varepsilon]$ would be a
  homomorphism into the abelian group $Z(SL_d)$:
  $[\kappa_0, \varepsilon\delta] = \kappa_0\varepsilon\kappa_0^{-1}[\kappa_0,\delta]\varepsilon^{-1} = [\kappa_0,\varepsilon][\kappa_0,\delta]$,
  since $[\kappa_0,\delta]$ is scalar. $SL_d(\mathbb F_q)$ is perfect for $d \ge 3$, so the homomorphism is trivial.
  Then $\kappa_0$ commutes with every transvection and is scalar, a contradiction.
- **$N_W = SL_d$.** $PSL_d(\mathbb F_q)$ is simple, so $N_W Z = SL_d$. Then $SL_d/N_W$ is abelian, and perfectness
  gives $N_W = SL_d(\mathbb F_q)$.

In particular $e_{12}(\chi_W) = \iota_W(I + e_{(1,0),(2,0)}) \in N$, with $\chi_W \ne 0$.

**(d) $\kappa = \lambda I_d$ with $\lambda : U \to \mathbb F_q^\times$ locally constant, $\lambda \not\equiv 1$.**
- **$k$ is scalar.** $k = cI_3$ with $c \in LC(X,\mathbb F_q)^\times$, equal to $\lambda \circ T^{-a}$ on $T^aU$
  ($|a| \le m'$) and to 1 off $V$.
- **The root.** Choose a clopen $W \subseteq U$ with $\lambda|_W = \lambda_0 \ne 1$, and put
  $r = \chi_{T^{m'+1}W}\,u = u\,\chi_{T^{m'}W} \ne 0$.
- **Values of $c$.** $T^{m'+1}W$ is disjoint from $V$, because $m'+1-a \in [1, 2m'+1] = [1, L]$. So $c = 1$ there. And
  $\alpha(c^{-1}) = c^{-1} \circ T^{-1} = \lambda_0^{-1}$ there, because $T^{-1}$ maps $T^{m'+1}W$ onto level $m'$
  of the tower over $W$.
- **Conclusion.** $crc^{-1} = c\,\chi_{T^{m'+1}W}\,\alpha(c^{-1})\,u = \lambda_0^{-1}r$. So
  $$[k, e_{12}(r)] = e_{12}(crc^{-1})\,e_{12}(-r) = e_{12}\big((\lambda_0^{-1} - 1)\,r\big) \in N, \qquad (\lambda_0^{-1}-1)\,r \ne 0.$$

In both cases $I(N) \ne 0$. $\square$

### 6.3 Simplicity

By Theorem 6.1 and §6.1, a normal subgroup of $G$ not contained in $Z(G)$ is all of $G$. So $S = G/Z(G)$ is simple.

### 6.4 The centre, infiniteness, finite quotients

- **Centre.** If $g$ commutes with every $e_{ij}(1)$, then $gE_{ij} = E_{ij}g$ for all $i \ne j$, so $g = cI_3$ with
  $c \in R$. Commuting with every $e_{12}(r)$ forces $c \in Z(R)^\times = \mathbb F_q^\times$ (Part 1 §3.4). Scalars
  are central, so $Z(G) = \Lambda I_3$, a finite group.
- **Infinite.** $e_{12}(LC(X,\mathbb F_q)) \le G$ is infinite and meets $Z(G)$ trivially, so $S$ is infinite.
- **No finite quotients.** A finite-index normal subgroup $N$ of $G$ has $I(N)$ of finite index in the infinite group
  $(R,+)$. So $I(N) \ne 0$ and $N = G$. The same holds for $S$.

$\square$

*Continued in Part 3.*
