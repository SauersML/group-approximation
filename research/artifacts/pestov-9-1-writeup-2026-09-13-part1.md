# An infinite simple Kazhdan group that is sofic: a positive answer to Pestov's Question 9.1

**Write-up, Part 1 of 3.** Lane `ex-pestov91-harden`, 2026-09-13. It stays in this repository: publishing outside needs
the user's approval.
- Part 1: the question, the construction (with explicit generators for the Fibonacci subshift), the ring, property (T).
- Part 2 (`pestov-9-1-writeup-2026-09-13-part2.md`): local embeddability into finite groups; normal subgroups.
- Part 3 (`pestov-9-1-writeup-2026-09-13-part3.md`): consequences, a remark on Dadarlat's introduction, credits, and
  the literature check.

**Status.**
- The claim `simple-kazhdan-lef-group-from-minimal-subshift` is established in Cairn (8b65f0932), by lane
  `ex-kazhdan-simple-hyperlinear`.
- Two independent reviews passed: `ex-verify-groups` (0efeac4106) and `ex-pestov91-harden` (badc66e2d7, 80873d2cc7).
- Novelty: bounded literature checks found no earlier infinite simple Kazhdan group that is sofic or hyperlinear (Part 3).

## 0. The result

**Question** (Pestov, *Hyperlinear and sofic groups: a brief guide*, Bull. Symb. Logic 14 (2008), arXiv:0804.3968,
p. 21). "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it
be hyperlinear (sofic)?"

**Theorem.** Let $q$ be a prime power and $X \subseteq A^{\mathbb Z}$ an infinite minimal subshift over a finite
alphabet. Put $R = LC(X,\mathbb F_q) \rtimes \mathbb Z$ and $G = EL_3(R)$. Then the centre $Z(G)$ is finite, and
$S = G/Z(G)$ is:
1. finitely generated, infinite and simple;
2. a group with Kazhdan's property (T);
3. locally embeddable into finite groups (LEF), hence sofic, hence hyperlinear.

So Question 9.1 has a positive answer, in both its hyperlinear and its sofic form.

**The three inputs.**
- **Property (T)** is Ershov–Jaikin-Zapirain's theorem: $EL_n(R)$, $n \ge 3$, is Kazhdan for every finitely
  generated associative ring $R$ with 1.
- **Local embeddability** comes from approximating the subshift by periodic words, the mechanism of
  Grigorchuk–Medynets' LEF theorem for topological full groups, used here for rings. $R$ embeds in an
  ultraproduct of matrix algebras $M_N(\mathbb F_q)$, so $G$ embeds in an ultraproduct of $GL_{3N}(\mathbb F_q)$.
- **Simplicity** has two steps. First, $R$ is a simple ring. Second, a noncentral element of a normal subgroup is
  pushed into a matrix ring living on a tower of small cylinders. That produces a nonzero elementary matrix in the
  normal subgroup, and simplicity of $R$ spreads it everywhere.

Combining the three, and the root-detection argument of the second step, are the new part.

## 1. Background

- **Kirchberg.** For a Kazhdan group, the factorization property is equivalent to residual finiteness (as recalled
  in Thom, arXiv:0810.2180, §1). An infinite simple Kazhdan group is not residually finite, so it lacks the
  factorization property. Ozawa (*About the QWEP conjecture*, arXiv:math/0306067) noted that the full C*-algebra
  of a hyperlinear simple Kazhdan group would then fail the local lifting property. He wrote that it is unknown
  whether such a group exists. This is the origin of 9.1.
- **Earlier examples.** The known infinite simple Kazhdan groups, Kac–Moody lattices (Caprace–Rémy) and Gromov's
  quotients of hyperbolic Kazhdan groups, are not known to be sofic or hyperlinear. Kac–Moody lattices are finitely
  presented, and a finitely presented LEF group is residually finite, so no finitely presented simple group is LEF.
- **Nearest prior object.** Thom (arXiv:0810.2180, Theorem 1.4) gave a finitely generated LEF Kazhdan group that
  is not residually finite. It is not simple.

The group $S$ is infinitely presented (Part 3), which is what allows it to be LEF.

## 2. The construction

### 2.1 Minimal subshifts

$A$ is a finite alphabet and $T$ is the shift on $A^{\mathbb Z}$, $(Tx)_n = x_{n+1}$. A subshift $X$ is a closed
$T$-invariant set. It is *minimal* if every orbit is dense. An infinite minimal subshift has no periodic point, since
a finite orbit would be a proper closed invariant set. $L_m(X)$ is the set of words of length $m$ occurring in points
of $X$. Every clopen subset of $X$ is a finite union of cylinders $C(v) = \{x : x_{[-k,k]} = v\}$ of any sufficiently
large radius $k$.

### 2.2 The ring

$LC(X,\mathbb F_q)$ is the commutative ring of locally constant functions $X \to \mathbb F_q$, and
$\alpha(f) = f \circ T^{-1}$. The algebraic crossed product $R = LC(X,\mathbb F_q) \rtimes \mathbb Z$ consists of
the finite sums $\sum_j f_j u^j$, with multiplication $(f u^i)(g u^j) = f\,\alpha^i(g)\,u^{i+j}$. Its normal form
is unique. For a clopen $Y$, $u\chi_Y u^{-1} = \chi_{TY}$. An element has *propagation* $\le w$ if $f_j = 0$ for
$|j| > w$.

### 2.3 The group

$e_{ij}(r) = I + rE_{ij}$ for $i \ne j$ and $r \in R$, and $G = EL_3(R) \le GL_3(R)$ is the group they generate.
With $[x,y] = xyx^{-1}y^{-1}$, $e_{ij}(r)e_{ij}(s) = e_{ij}(r+s)$ and, for $\{i,j,k\} = \{1,2,3\}$,
$$[e_{ik}(r), e_{kj}(s)] = e_{ij}(rs).$$
So if $R$ is generated as a ring by a finite set $\Sigma$, then $G$ is generated by the $6(|\Sigma|+1)$ matrices
$e_{ij}(s)$, $s \in \Sigma \cup \{1\}$.

### 2.4 Explicit example: the Fibonacci subshift

- **The subshift.** Let $\sigma$ be the substitution $a \mapsto ab$, $b \mapsto a$, and $\varphi = abaababaabaab\cdots$
  its fixed point. $X_{\mathrm{Fib}}$ is the set of $x \in \{a,b\}^{\mathbb Z}$ all of whose finite subwords occur in
  $\varphi$. It is minimal, because $\sigma$ is primitive, and aperiodic, because it is Sturmian:
  $|L_m(X_{\mathrm{Fib}})| = m+1$.
- **Ring generators.** Put $p = \chi_{\{x_0 = a\}}$, so that $1 - p = \chi_{\{x_0 = b\}}$. Then
  $u^i p u^{-i} = \chi_{\{x_{-i} = a\}}$, and products of these and their complements give every cylinder. So $R$ is
  generated as a ring by $u$, $u^{-1}$ and $p$, together with one $\lambda$ with $\mathbb F_p[\lambda] = \mathbb F_q$
  when $q$ is not prime.
- **Visible relations.** Among the relations are $p^2 = p$, $[p, u^i p u^{-i}] = 0$, and
  $(1-p)\,u(1-p)u^{-1} = 0$. The last one says that $bb$ never occurs. The ring is not finitely presented by these.
- **Generators of $G$** (for $q$ prime): the 24 matrices $e_{ij}(1), e_{ij}(u), e_{ij}(u^{-1}), e_{ij}(p)$ with
  $i \ne j$. $S$ is generated by their images.
- **The first finite model.** Take the return word $w = abaab$, $N = 5$. Its cyclic windows of length 3 are
  $aba, baa, aab, aba, bab$, exactly $L_3(X_{\mathrm{Fib}}) = \{aab, aba, baa, bab\}$. Send
  - $u \mapsto P$, the cyclic shift $\delta_n \mapsto \delta_{n+1}$ on $\mathbb F_q^{\mathbb Z/5}$;
  - $p \mapsto D = \mathrm{diag}(1,0,1,1,0)$, the positions of $a$ in $w$.

  The five rotations of $abaab$ are distinct, so products of the $P^iDP^{-i}$ and their complements give every
  diagonal matrix unit, and with $P$ they generate $M_5(\mathbb F_q)$. The 24 generators go to
  $I_{15} + E_{ij} \otimes P^{\pm 1}$, $I_{15} + E_{ij} \otimes D$ and $I_{15} + E_{ij} \otimes I_5$. These
  generate $EL_3(M_5(\mathbb F_q)) = SL_{15}(\mathbb F_q)$.

  Longer return words give $SL_{3N}(\mathbb F_q)$ with $N \to \infty$. The marked groups converge to $G$, and the
  marked $PSL_{3N}(\mathbb F_q)$ converge to $S$ (Part 2 §5, Part 3 §7).

## 3. The ring

### 3.1 Two facts about infinite minimal subshifts

**(U) Uniform recurrence.** For every $m$ there is $\ell(m)$ such that every word of $L_{\ell(m)}(X)$ contains every
word of $L_m(X)$. This is standard: minimality and compactness.

**(P) Long cylinders return late.** For every $L$ there is $k_L$ such that every cylinder $C$ of radius $k \ge k_L$
satisfies $T^jC \cap C = \emptyset$ for $0 < |j| \le L$.

*Proof.* $T^jC(v) \cap C(v) \ne \emptyset$ means that $v$ occurs twice at distance $|j|$, so $v$ has period $|j|$.
If (P) failed for some $L$, some fixed $j$ would be a period of words $v_k \in L_{2k+1}(X)$ for infinitely many $k$.
A limit point of points in which $v_k$ is centred is a $j$-periodic point of $X$, which is impossible. $\square$

### 3.2 Generation

$u^i\chi_{[x_0=a]}u^{-i} = \chi_{[x_{-i}=a]}$. Products give all cylinders, and $\mathbb Z$-linear combinations give
$LC(X,\mathbb F_p)$. Adding a generator $\lambda$ of $\mathbb F_q$ over $\mathbb F_p$ gives $LC(X,\mathbb F_q)$.
So $R$ is generated as a ring by $u$, $u^{-1}$, the letter indicators and $\lambda$. It is finitely generated.

### 3.3 $R$ is simple

Let $J \ne 0$ be a two-sided ideal. Choose $0 \ne P = \sum_{j \in F} f_j u^j \in J$. After multiplying by a power of
$u$ we may assume $f_0(x) = c \ne 0$ for some $x$. Since $T^jx \ne x$ for $0 \ne j \in F$, there is a clopen
$W \ni x$ with $f_0|_W = c$ and $T^jW \cap W = \emptyset$ for $0 \ne j \in F$. Then
$$\chi_W P \chi_W = \sum_j f_j\,\chi_W\chi_{T^jW}\,u^j = c\,\chi_W \in J.$$
The union $\bigcup_n T^nW$ is open, invariant and nonempty, hence all of $X$. By compactness,
$X = T^{i_1}W \cup \dots \cup T^{i_s}W$. Each $\chi_{T^iW} = u^i\chi_Wu^{-i}$ lies in $J$, and
$1 = 1 - \prod_t(1 - \chi_{T^{i_t}W})$ expands into terms each containing a factor in $J$. So $J = R$. $\square$

### 3.4 The centre of $R$ is $\mathbb F_q$

Let $c = \sum f_ju^j$ be central.
- $c\chi_W = \chi_Wc$ gives $f_j(\chi_{T^jW} - \chi_W) = 0$ for every clopen $W$. For $j \ne 0$ and any $x$, choose
  $W \ni x$ with $T^{-j}x \notin W$; the bracket is $-1$ at $x$, so $f_j(x) = 0$.
- $cu = uc$ gives $f_0 \circ T = f_0$. A continuous invariant function on a minimal system is constant.

$\square$

### 3.5 Tower subrings

Let $U$ be clopen with $T^jU \cap U = \emptyset$ for $0 < |j| \le 2m$. The levels $T^aU$, $|a| \le m$, are then
pairwise disjoint. For clopen $W \subseteq U$ and $|a|, |b| \le m$ put
$$E_{ab}(W) = \chi_{T^aW}\,u^{a-b} = u^{a-b}\,\chi_{T^bW}.$$
Then $E_{ab}(W)\,E_{cd}(W') = \chi_{T^aW \cap T^{a-b+c}W'}\,u^{a-b+c-d}$. For $b \ne c$ the levels $T^aU$ and
$T^{a+c-b}U$ are disjoint, so
$$E_{ab}(W)\,E_{cd}(W') = \delta_{bc}\,E_{ad}(W \cap W').$$
The span $B_m(U)$ of these elements is a subring with unit $\chi_V$, where $V = \bigsqcup_{|a| \le m} T^aU$. The map
$(F_{ab}) \mapsto \sum_{a,b}(F_{ab} \circ T^{-a})\,\chi_{T^aU}\,u^{a-b}$ is a ring isomorphism
$M_{2m+1}(LC(U,\mathbb F_q)) \to B_m(U)$. It is injective because different levels have disjoint supports.

Two more facts:
- for clopen $W \subseteq U$ and $m' \le m$, $\chi_{V_{m'}(W)}$ commutes with $B_{m'}(U)$ and with
  $LC(X,\mathbb F_q)$, where $V_{m'}(W) = \bigsqcup_{|a| \le m'} T^aW$. Indeed
  $E_{ab}(W')\chi_{V_{m'}(W)} = \chi_{T^a(W \cap W')}u^{a-b} = \chi_{V_{m'}(W)}E_{ab}(W')$;
- under the isomorphism, $\chi_{V_{m'}(W)}$ is the central idempotent $\chi_W \cdot I$.

### 3.6 Absorption lemma

**Lemma.** Suppose $T^jU \cap U = \emptyset$ for $0 < |j| \le 2(m+w)$. If $r, r'$ have propagation $\le w$ and
$b \in B_m(U)$, then $r\,b\,r' \in B_{m+w}(U)$.

*Proof.* By linearity take $r = fu^i$, $b = E_{ab}(W)$, $r' = f'u^j$ with $|i|, |j| \le w$. Then
$$r\,b\,r' = f\,\chi_{T^{a+i}W}\,\alpha^{i+a-b}(f')\,u^{i+a-b+j}.$$
Split $W$ into clopen pieces $W_k$ on which $F = f\,\alpha^{i+a-b}(f')$ is constant, equal to $c_k$, on
$T^{a+i}W_k$. Then $r\,b\,r' = \sum_k c_k\,E_{a+i,\,b-j}(W_k)$, with $|a+i|, |b-j| \le m+w$. $\square$

## 4. Property (T)

M. Ershov and A. Jaikin-Zapirain, *Property (T) for noncommutative universal lattices*, Invent. Math. 179 (2010),
arXiv:0809.4095v2, main theorem (source `EL_n0909.tex`, lines 405–410):

> Let $R$ be a finitely generated (associative) ring with $1$ and $n \ge 3$. Let $G = EL_n(R)$, that is, the subgroup
> of $GL_n(R)$ generated by elementary matrices. Then $G$ has Kazhdan's property $(T)$.

By §3.2 our $R$ is a finitely generated ring with 1. So $G = EL_3(R)$ has property (T), and so does its quotient
$S$. No commutativity or stable-range hypothesis is involved. Before this theorem, property (T) for $EL_n(R)$ was
known only for commutative $R$ or under stable range conditions (Ershov–Jaikin-Zapirain's introduction). $\square$

*Continued in Part 2.*
