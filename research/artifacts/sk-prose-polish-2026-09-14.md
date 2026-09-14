# sk-prose-polish: sentence-level pass on the simple Kazhdan note

- Base: `simple_kazhdan_sofic_group.tex` rev4.5, md5 29d63f7944bccccbf9a91b0b2714c0b4, confirmed on main at 8d107797ee. Line numbers refer to that file.
- Doctrine applied:
  - So/then as the default connective, at most one sentence-initial So per paragraph;
  - the rules in sentence-level-bad-patterns and the Borcherds tone;
  - decisions on reader merits only.
- No step of any proof changes. OLD strings are verbatim, so each fix is one exact replacement.
- Length: the top 15 change the length by +0 lines net. The budgeted extended set adds +5, and the optional items are over budget.
- Other lanes own the introduction, the structure, the statements and the example. These fixes sit inside sentences, so they survive a restructure.

## Top 15, ranked by reader benefit

### 1. l.153–155 The definition of "small" misparses (Δ 0)
As written, "for $\xi\in B_{2w}\setminus\{e\}$ and every $f\circ\xi$, with …, is constant" can be read as quantifying over the $f\circ\xi$ too.
```tex
% OLD
Call a clopen set $V$ small if $V\cap\xi V=\varnothing$ for
$\xi\in B_{2w}\setminus\{e\}$ and every $f\circ\xi$, with $\xi\in B_w$ and
$f$ a coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$.
% NEW
Call a clopen set $V$ small if $V\cap\xi V=\varnothing$ for all
$\xi\in B_{2w}\setminus\{e\}$, and every $f\circ\xi$ with $\xi\in B_w$ and
$f$ a coefficient of an entry of $g$ or $g^{-1}$ is constant on $V$.
```

### 2. l.91–92 The Stepanov sentence has the wrong quantifier shape (Δ 0)
"Any $p,q$ satisfy $pr+qs=0$ with $(r,s)\ne0$" reads as if $r,s$ were given. The intended statement is existential.
```tex
% OLD
and any $p,q$ in it satisfy $pr+qs=0$ with $(r,s)\ne0$ by a dimension count
on a tower over one small cylinder.
% NEW
and for any $p,q$ in it there are $r,s$, not both $0$, with $pr+qs=0$, by a
dimension count on a tower over one small cylinder.
```

### 3. l.246–247 Unused notation (Δ −1)
$\tau_\pm$ and $\tau_a$ occur nowhere else (grep of main: the only other `tau` uses are $\tau_s$ and $\tau_1$ in §1). A reader searches for them.
```tex
% OLD
which span $\LC(X,\F_2)$. We write $\tau_\pm$ and $\tau_a$ for the letters
of $u^{\pm1}$ and $e_a$.
% NEW
which span $\LC(X,\F_2)$.
```

### 4. Theorem 2: s means both an arbitrary ring element and an element of S (Δ 0)
In l.114–116, "for all $r,s\in R$" is followed at l.118 by "$e_{ij}(s)$ with $s\in S$". Use $r,r'$ for arbitrary elements.
```tex
% OLD (l.114–116)
and for all $r,s\in R$
we have $\varphi_k(r+s)=\varphi_k(r)+\varphi_k(s)$ and
$\varphi_k(rs)=\varphi_k(r)\varphi_k(s)$ for large $k$.
% NEW
and for all $r,r'\in R$
we have $\varphi_k(r+r')=\varphi_k(r)+\varphi_k(r')$ and
$\varphi_k(rr')=\varphi_k(r)\varphi_k(r')$ for all large $k$.
% OLD (l.265–267)
for fixed $r,s\in R$ the identities
$\varphi_\ell(r+s)=\varphi_\ell(r)+\varphi_\ell(s)$ and
$\varphi_\ell(rs)=\varphi_\ell(r)\varphi_\ell(s)$ hold
% NEW
for fixed $r,r'\in R$ the identities
$\varphi_\ell(r+r')=\varphi_\ell(r)+\varphi_\ell(r')$ and
$\varphi_\ell(rr')=\varphi_\ell(r)\varphi_\ell(r')$ hold
% OLD (l.388–389)
so for fixed $r,s\in R_\Delta$ and large $n$, $\varphi_n$ is additive and
multiplicative on $r,s$, and $\varphi_n(1)=I$.
% NEW
so for fixed $r,r'\in R_\Delta$ and large $n$, $\varphi_n$ is additive and
multiplicative on $r,r'$, and $\varphi_n(1)=I$.
```
Optional, for full consistency: make the same change in \eqref{eq:elementary} (l.142) and at l.204.

### 5. l.33–43 Abstract: one sentence with two ideas; "this property" (Δ 0)
- The abstract repeats "locally embeddable into finite groups" three times, and "this property" and "the host" have no antecedent.
- This keeps rev4.5's U1 fix: the host is named in full, and "such a host" refers to the sentence just before.
```tex
% OLD
So $G_X$ is locally
embeddable into finite groups, sofic and hyperlinear, which answers the
question of Brown and Ozawa whether an infinite simple Kazhdan group can
be hyperlinear, and Pestov's sofic version of it.
A finitely generated group is locally embeddable into finite groups if and
only if it is a subgroup of an infinite finitely generated simple Kazhdan
group that is a limit of finite simple groups whose Cayley graphs form
expanders, and it also has solvable word problem if and only if the host
can be chosen with solvable word problem.
One such group contains every recursively presented finitely generated
group with this property.
% NEW
So $G_X$ is locally
embeddable into finite groups (LEF), sofic and hyperlinear, which answers
the question of Brown and Ozawa whether an infinite simple Kazhdan group
can be hyperlinear, and Pestov's sofic version of it.
A finitely generated group is LEF if and only if it is a subgroup of an
infinite, finitely generated, simple Kazhdan group that is a limit of
finite simple groups whose Cayley graphs form expanders. A finitely
generated LEF group has solvable word problem if and only if it is a
subgroup of such a host with solvable word problem.
One such host contains every recursively presented finitely generated LEF
group.
```

### 6. Theorem 1 and Corollary 3: "the limit", and the antecedent of "whose" (Δ 0)
- Theorem 1 says "the limit" of an unspecified sequence and nests two interruptions.
- In Corollary 3, "whose" follows "marked groups".
```tex
% OLD (l.65–67)
It is the limit, in the space of marked groups, of
finite simple groups $\SL_{3N}(\F_2)$ whose Cayley graphs, with respect to
the images of a fixed generating set, form a family of expanders.
% NEW
It is a limit of finite simple groups $\SL_{3N}(\F_2)$
in the space of marked groups, and the Cayley graphs of these groups with
respect to the images of a fixed generating set form a family of expanders.
% OLD (l.300–302)
that is a limit of finite simple groups $\SL_N(\F_2)$ in the space of
marked groups, whose Cayley graphs with respect to the images of a fixed
generating set form a family of expanders.
% NEW
that is a limit of finite simple groups $\SL_N(\F_2)$ in the space of
marked groups, where the Cayley graphs of these groups with respect to the
images of a fixed generating set form a family of expanders.
```

### 7. Groups said to "form expanders"; "$N_k\to\infty$ as $G$ is infinite" (Δ +1)
- At l.81 the groups, and at l.234 the quotients, are said to form expanders; the Cayley graphs do.
- At l.233, "as" right after $N_k\to\infty$ reads as "as $k\to\infty$".
- This item also fixes the So cluster at l.224/l.231.
```tex
% OLD (l.81)
$G_X$ is a limit of the groups $\SL_{3N}(\F_2)$, which form expanders as
% NEW
$G_X$ is a limit of the groups $\SL_{3N}(\F_2)$, whose Cayley graphs form expanders as
% OLD (l.231–235)
So these finite simple groups converge to $G$ in the space of
marked groups~\cite{Grigorchuk,Champetier}, $G$ is LEF, and
$N_k\to\infty$ as $G$ is infinite. Since $\EL_3(F)$ has
property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, its finite quotients form a
family of expanders~\cite{Margulis,Kassabov}.\qed
% NEW
Therefore these finite simple groups converge to $G$ in the space of
marked groups~\cite{Grigorchuk,Champetier}, $G$ is LEF, and
$N_k\to\infty$ because $G$ is infinite. Since $\EL_3(F)$ has
property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, the Cayley graphs of its finite
quotients with respect to the images of its generators form a family of
expanders~\cite{Margulis,Kassabov}.\qed
```

### 8. l.438 Two consecutive sentence-initial "So" (l.435, l.438) (Δ 0)
```tex
% OLD
$|m|\le3r$. So $\Delta$ is LEF, and the argument above applies to it.
% NEW
$|m|\le3r$. Therefore $\Delta$ is LEF, and the argument above applies to it.
```

### 9. l.425–428 The definition of θ is split by a long interruption (Δ 0)
```tex
% OLD
that stay in it, and let $\theta$, with $\theta(v)_{-3r}=1$ and
$\theta(v)_m=v_{m-1}$ otherwise, be the isomorphism from
$\{v\in Q^{[-3r,3r]}:v_{3r-1}=v_{3r}\}$ onto
$\{v\in Q^{[-3r,3r]}:v_{-3r}=1\}$.
% NEW
that stay in it, and let $\theta$ be the isomorphism from
$\{v\in Q^{[-3r,3r]}:v_{3r-1}=v_{3r}\}$ onto
$\{v\in Q^{[-3r,3r]}:v_{-3r}=1\}$ given by $\theta(v)_{-3r}=1$ and
$\theta(v)_m=v_{m-1}$ for $m>-3r$.
```

### 10. l.120 Theorem 2: "whose" attaches to the markings (Δ 0)
```tex
% OLD
$e_{ij}(\varphi_k(s))$, whose Cayley graphs form a family of expanders.
% NEW
$e_{ij}(\varphi_k(s))$; their Cayley graphs form a family of expanders.
```

### 11. l.412–415 An awkward hypothesis list, and "used to preserve solvable word problems … keeps the word problem solvable" (Δ 0)
The credit is unchanged. The next paragraph proves that the construction keeps the word problem solvable, so the redundant clause can go (it is the U2 wording).
```tex
% OLD
Now let $\Gamma$ be generated by a finite set $E$, LEF and with solvable
word problem. A half-line form of the Neumann--Neumann construction, used
by Darbinyan to preserve solvable word problems~\cite{Darbinyan15}, keeps
the word problem solvable.
% NEW
Now let $\Gamma$ be LEF with solvable word problem, generated by a finite
set $E$. We use a half-line form of the Neumann--Neumann construction,
which Darbinyan used to preserve solvable word
problems~\cite{Darbinyan15}.
```

### 12. l.123–126 "give … which gives …, and lamplighter actions show" (Δ 0)
```tex
% OLD
Periodic approximations give such maps for $\LC(X,\F_2)\rtimes_T\Z$, which
gives Theorem~\ref{thm:main}, and lamplighter actions show that the
countable subgroups of the groups in Theorem~\ref{thm:general} are exactly
the countable LEF groups (Corollary~\ref{cor:host}).
% NEW
Periodic approximations give such maps for $\LC(X,\F_2)\rtimes_T\Z$, and
Theorem~\ref{thm:main} follows. By Corollary~\ref{cor:host}, whose proof uses
lamplighter actions, the countable subgroups of the groups in
Theorem~\ref{thm:general} are exactly the countable LEF groups.
```

### 13. l.474–477 "in the generators in …", with a dangling "using" (Δ 0)
```tex
% OLD
Multiplying out a word in the generators in $\LC(A^{\Z},\F_2)\rtimes\Z$,
which maps onto $R$, gives a matrix with entries $\sum_jf_ju^j$, each
$f_j$ given by a table on the words of some length, using
$uf=(f\circ T^{-1})u$.
% NEW
Multiplying out a word in the generators over $\LC(A^{\Z},\F_2)\rtimes\Z$,
which maps onto $R$, with the rule $uf=(f\circ T^{-1})u$ gives a matrix with
entries $\sum_jf_ju^j$, where each $f_j$ is given by a table on the words of
some length.
```

### 14. l.73–75 A precise LEF definition (Δ 0)
"Embeds injectively … preserving the products that stay in that subset" is vague. With a precise definition, the later phrase "products that stay in" (l.333, l.373, l.425, l.436) points back to it.
The letter $\Phi$ is unused elsewhere; $F$ and $E$ are taken.
```tex
% OLD
A group is LEF~\cite{VershikGordon} if every finite subset embeds
injectively into a finite group, preserving the products that stay in
that subset.
% NEW
A group is LEF~\cite{VershikGordon} if each finite subset $\Phi$ maps
injectively into a finite group by a map that preserves every product
$gh$ with $g,h,gh\in\Phi$.
```

### 15. The remaining clusters of sentence-initial "So" (Δ 0)
Each of these paragraphs has two sentence-initial "So":
- l.147 (after l.144): OLD `for $n\ge3$.` / `So $G$ has property~\textup{(T)}, and it is infinite because` → NEW `for $n\ge3$,` / `so $G$ has property~\textup{(T)}. It is infinite because`.
- l.171, which follows ", so they agree everywhere.": OLD `so they agree everywhere. So` → NEW `so they agree everywhere. Therefore`.
- l.207, which follows ", so … \in J$.": OLD `\in J$. So $J=R$ and` → NEW `\in J$. Then $J=R$ and`.
- l.270 (after l.252): OLD `every matrix unit. So $\varphi_\ell(S)$ generates` → NEW `every matrix unit. Therefore $\varphi_\ell(S)$ generates`.
- l.281 (after l.277): OLD `finite. So $L(G)$ is a $\mathrm{II}_1$ factor, and` → NEW `finite. Then $L(G)$ is a $\mathrm{II}_1$ factor, and`.

## Extended set, within budget (Δ +5 in total)

- **16. l.336 (Δ 0).** "well defined as $|Q_k|$ divides $m_k$" is tautological-looking because $m_k=|Q_k|$.
  - OLD `defined as $|Q_k|$ divides $m_k$.` → NEW `defined because the order of $\mu_k(\gamma_j)$ divides $m_k$.`
- **17. l.216–218 (Δ 0).** "those … those":
  - OLD `$\SL_{3N_k}(\F_2)$ and those inside one block are commutators of those` / `between blocks.`
  - NEW `$\SL_{3N_k}(\F_2)$, and each transvection inside one block is a commutator` / `of transvections between blocks.`
- **18. l.156–158 (Δ +1).** One step of motivation: why small sets exist. Correct because the moved set is the complement of finitely many closed nowhere dense sets.
  - OLD `so the points` / `moved by every $\xi\in B_{2w}\setminus\{e\}$ are dense, and every nonempty` / `clopen set contains a nonempty small one.`
  - NEW `so the points` / `moved by every $\xi\in B_{2w}\setminus\{e\}$ form a dense open set. Small` / `enough clopen neighborhoods of these points are small, so every nonempty` / `clopen set contains a nonempty small one.`
- **19. l.330 (Δ +1).** A dangling participle:
  - OLD `countable LEF group, replaced by $\Gamma\times\Z$ so that it is infinite.`
  - NEW `countable LEF group; replacing $\Gamma$ by $\Gamma\times\Z$, we may assume` / `that $\Gamma$ is infinite.`
- **20. l.409–410 (Δ +1).** Two facts serving two different statements are joined by ", and":
  - OLD `subgroups, and there are countably many recursive presentations.`
  - NEW `subgroups. The last statement of Corollary~\ref{cor:host} follows, as there` / `are countably many recursive presentations.`
- **21. l.445–447 (Δ 0).** The undefined jargon "lamps", and "the word problem … decides":
  - OLD `for the lamps of $c$, so the word problem of $\Delta$ decides equality in` / `$\Lambda$ and computes the values of $c$.`
  - NEW `for the points of $\operatorname{supp}c$, so an algorithm for the word problem` / `of $\Delta$ decides equality in $\Lambda$ and computes the values of $c$.`
- **22. l.506 (Δ 0).** Terminology: the paper says "solvable" everywhere else.
  - OLD `the word problem is decidable if and only if $L(X)$ is` → NEW `the word problem is solvable if and only if $L(X)$ is`
- **23. l.525–526 (Δ 0).** "Flip conjugate" is used at l.528 without a definition.
  - OLD `If $(X,T)$ is topologically conjugate to $(Y,T')$ or to $(Y,T'^{-1})$, then` / `$G_X\cong G_Y$.`
  - NEW `If $(X,T)$ is flip conjugate to $(Y,T')$, that is, topologically conjugate` / `to $(Y,T')$ or to $(Y,T'^{-1})$, then $G_X\cong G_Y$.`
- **24. l.101–102 (Δ 0).** Sequence of tenses, and a causal "as":
  - OLD `remained, as it was unknown whether finitely generated simple Kazhdan` / `groups can be hyperlinear`
  - NEW `remained, since it was unknown whether finitely generated simple Kazhdan` / `groups could be hyperlinear`
- **25. l.53–54 (Δ 0).** Agency: a question does not "add".
  - OLD `and Pestov's Open question~9.1 adds the` / `sofic form~\cite{Pestov}.`
  - NEW `and Pestov asked the sofic form as Open` / `question~9.1~\cite{Pestov}.`
- **26. l.289–290 (Δ +1).** "For LEF groups the next corollary answers" reads as if only LEF inputs were considered.
  - OLD `amenable groups~\cite{KionkeSchesler}. For LEF groups the next corollary` / `answers the analogous question, with a Kazhdan host.`
  - NEW `amenable groups~\cite{KionkeSchesler}. Corollary~\ref{cor:lef} answers the` / `analogous question for simple Kazhdan groups that are limits of finite` / `simple groups.`
- **27. l.498–499 (Δ +1, the budget's last line).** "By substituting for its generators" leaves out what is substituted.
  - OLD `$G$, a word for $H$ becomes a word for $G$ by substituting for its` / `generators, so the word problem of $H$ reduces to that of $G$.`
  - NEW `$G$, a word for $H$ becomes a word for $G$ by substituting words in the` / `generators of $G$ for the generators of $H$, so the word problem of $H$` / `reduces to that of $G$.`
  - With 18, 19, 20 and 26 this makes +5. If a later lane frees lines, 28–30 below fit.

## Optional, over budget
- **28. l.353–354 (+1).** The Łoś attribution: $\Delta$ is infinite because it contains $\Gamma$, not because of the ultraproduct.
  - NEW `Finitely many equations and inequalities that hold in the ultraproduct` / `hold in some coordinate, so $\Delta$ is LEF, and $\Delta$ is infinite because` / `it contains $\Gamma$.`
- **29. l.378–379 (+1).** "move the attached points near $e$" has no object for "near $e$".
  - NEW `move the` / `attached points as $\Lambda$ moves the points of $\Omega$, on the coordinates` / `near $e$.`
- **30. l.339 (+0.5).** "Level" is used before it is defined. Add `the set of points with last coordinate $i$,` after `act on the level $i$`.

## Notation observations (no edit proposed unless main wants one)
- **The letter s has three roles:** arbitrary ring elements (\eqref{eq:elementary}, l.204), elements of $S$ (l.118, l.144), and generators of $\Lambda$ ($u_s$ at l.368, $P_s$ at l.390). Fix 4 covers Theorem 2. For $\Lambda$ a cheap option is $\lambda$.
- **Identity elements:** $1$ in $G,K,\Gamma,Q_k$ and $e$ in $\Lambda,\Delta$. This is defensible, but $\epsilon_{ee}$ (l.195) reads oddly. Since $\epsilon_{ee}=e_V$, the display could say $h=I_3+e_VE_{ij}$, at the cost of a less visible membership in $M_3(A_V)$.
- **Letter reuse:** $F$ (the free algebra) against $\F_2$; δ as a basis vector (§2), a group element (§3) and the Kronecker delta (l.179).
- **Structure, for the structure lane:** "Brown's formulation" sits under the heading "Proof of Theorem~1".
- **l.104, "The proof works for other actions.":** this is metacommentary. Option: "The same argument applies to other actions."
- **Heavy sentences to split if lines free up:**
  - l.346–350: a gerund subject, "sending γ to … is a homomorphism".
  - l.291–295: the Thompson sentence, five lines with nested clauses.
  - l.466–468: $X_{(3-\sqrt5)/2}$ is named in the statement before $X_\alpha$ is defined in the proof.
