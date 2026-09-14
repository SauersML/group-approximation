# sk-lef-embedding-e proposal: the LEF characterization as a corollary of Theorem 1

Lane `sk-lef-embedding-e`, 2026-09-13. Target: the shortest complete text for the note proving that a finitely
generated group is LEF exactly when it embeds in an infinite finitely generated simple Kazhdan LEF group.
Base: main's note at rev1 `5b1890ce6c`. Status: the mathematics is unreviewed; see §4.

The corollary rests on the peer construction `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`
(sk-universal-embedding-b) and on this lane's `tower-simplicity-holds-for-topologically-free-actions`
(landed `f21f2493bc`), which is what lets the note reuse its own proof instead of importing a groupoid criterion.

## 0. The one obstacle, and the decision

Theorem 1's proof is written for the shift on a minimal subshift, where every point is aperiodic. The lamplighter
action of `L = F_2 ≀ Δ` on `Z = F_2^Δ` is minimal but **only topologically free**: a shift `δ ≠ 1` fixes the
`δ`-periodic configurations. Exactly one sentence of the proof uses more than topological freeness, on main at
l.143-144:

> By compactness every clopen set is a finite disjoint union of small ones.

A clopen set containing a point fixed by some `ℓ ∈ B_(2w)` has no small partition. The **density argument** repairs it:
free points are dense by Baire, so every nonempty clopen set *contains* a small one, which is all the proof uses.

The alternative the coordinator raised, keeping the proof for free actions and using a free minimal `L`-subshift, is
**not available**: a free minimal subshift with finite models forces the acting group to be residually finite
(`free-subshift-with-finite-models-forces-rf-group`), and `Δ` here is LEF and need not be residually finite. The
Bernoulli host escapes precisely because it is not free and its models are partial. So the density argument is the
only route, and it is also shorter than the text it replaces.

## 1. Patch to the proof of Theorem 1 (length neutral)

### (a) Current text, main `5b1890ce6c` l.139-152, verbatim
```latex
Call a clopen set $V$ small if $V\cap T^jV=\varnothing$ for
$0<|j|\le2w$ and every $f\circ T^i$, with $|i|\le w$ and $f$ a
coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$.
Minimality and infiniteness imply that $T$ has no periodic points, so
every point has a small clopen neighborhood. By compactness every clopen
set is a finite disjoint union of small ones.

Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$.
Otherwise $g$ commutes with $e_{ij}(e_V)$ for every clopen $V$,
by~\eqref{eq:elementary}. Taking $V=X$ gives $g=cI_3$ with
$c=\sum_jc_ju^j\in R$. Then $e_Vc-ce_V=\sum_jc_j(e_V-e_{T^jV})u^j$
vanishes for every clopen $V$. Choosing $V$ to contain $x$ but not
$T^{-j}x$, we get $c_j(x)=0$ for $j\ne0$. So $c\in\LC(X,\F_2)$, and
comparing constant coefficients in $cc^{-1}=1$ gives $c=1$ and $g=1$.
```

### (b) Replacement, verbatim LaTeX
```latex
Call a clopen set $V$ small if $V\cap T^jV=\varnothing$ for
$0<|j|\le2w$ and every $f\circ T^i$, with $|i|\le w$ and $f$ a
coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$.
Minimality and infiniteness imply that $T$ has no periodic points, so
every nonempty clopen set contains a small one.

Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$. Indeed
$g$ commutes with $e_{ij}(r)$ exactly when $g_{pi}r=0$ and $rg_{jq}=0$
for $p\ne i$ and $q\ne j$, and $g_{ii}r=rg_{jj}$. Here
$\bigl(\sum_jc_ju^j\bigr)e_V=\sum_jc_je_{T^jV}u^j$, so $ce_V=0$ for
every small $V$ forces $c=0$: otherwise some $c_j$ equals $1$ on a
nonempty clopen $U$, and a small $V\subseteq T^{-j}U$ gives
$c_je_{T^jV}\ne0$. So $g$ is diagonal and $g_{ii}e_V=e_Vg_{jj}$. In
that identity the coefficients at $j\ne0$ are supported in the disjoint
sets $T^jV$ and $V$, so they vanish, and the coefficients at $0$ agree
on every small $V$. So $g=cI_3$ with $c\in\LC(X,\F_2)$ invertible,
which gives $c=1$ and $g=1$.
```

- **Length:** 14 lines against 14. Neutral.
- **Reader trade-off:** the same conclusion with one hypothesis less, and the reader no longer has to see why a clopen
  set can be partitioned into small ones. It also states which identity commuting with `e_{ij}(r)` is, which the
  current text leaves to the reader.
- Nothing else in the proof uses freeness; the tower, the copy of `GL_d(F_2)` and the level ideal are unchanged.

## 2. The corollary (the deliverable)

### (a) Text, verbatim LaTeX, to follow the proof of Theorem 1
```latex
\begin{corollary}
A finitely generated group is LEF if and only if it is a subgroup of an
infinite finitely generated simple Kazhdan LEF group.
\end{corollary}

\begin{proof}
Subgroups of LEF groups are LEF. Let $\Gamma$ be finitely generated and
LEF. Doubling the regular representations of its finite models embeds
$\Gamma$ in an ultraproduct of finite alternating groups, in which every
element is a commutator~\cite{Ore}; adjoining elements that realize the
commutators of a generating set, and a copy of $\Z$, gives an infinite
finitely generated LEF group $\Delta$ with
$\Gamma\subseteq[\Delta,\Delta]$. Let $L=\F_2\wr\Delta$ act on
$Z=\F_2^{\Delta}$, where $\Delta$ shifts coordinates and the lamp at
$\delta$ flips the coordinate at $\delta$, and put
$R=\LC(Z,\F_2)\rtimes L$, generated as a ring by the units of a
generating set of $L$ and by $e_{\{x:x(1)=1\}}$. Flipping finitely many
coordinates makes every orbit dense, so the action is minimal. It is
topologically free: a lamp moves every configuration, and a nontrivial
shift moves every configuration that differs at two coordinates it
exchanges. The proof of Theorem~\ref{thm:main} applies to $R$ word for
word, with $u_\ell$ in place of $u^j$ and word length in place of
$|j|$, once the finite models are supplied: for finite models
$(Q_n,\varphi_n)$ of $\Delta$, let $\F_2\wr Q_n$ act on itself and
attach to $(c,q)$ the configuration $h\mapsto c(q\varphi_n(h))$. Every
configuration is legal, so no window can fail, and these models embed
$R$ in an ultraproduct of matrix algebras over $\F_2$. So $G=\EL_3(R)$
is an infinite finitely generated simple Kazhdan LEF group, and
Whitehead's lemma puts $\operatorname{diag}([x,y],1,1)$ in $G$ for all
units $x,y$, so $\ell\mapsto\operatorname{diag}(u_\ell,1,1)$ embeds
$[L,L]\supseteq[\Delta,\Delta]\supseteq\Gamma$ in $G$.
\end{proof}
```

### (b) The bibliography entry it needs
```latex
\bibitem{Ore}
O.~Ore, \emph{Some remarks on commutators},
Proc. Amer. Math. Soc. \textbf{2} (1951), 307--314.
\doi{10.1090/S0002-9939-1951-0040298-4}.
```
sk-universal-embedding-b verified the statement on p. 308 and the DOI. sk-citations should confirm the page range.

### (c) Length
- Corollary and proof: **31 lines** (4 statement, 27 proof), plus 4 bibliography lines.
- A **19-line variant** drops two justifications, leaving them to the reader: the sentence beginning "It is
  topologically free" (3 lines) and the sentence "Every configuration is legal ... over $\F_2$" (3 lines), keeping
  "the action is minimal and topologically free" and "these models embed $R$ in an ultraproduct". I do not recommend
  it: topological freeness is the hypothesis the reader must check to reuse Theorem 1, and legality of every
  configuration is the reason the construction works at all.
- The 31 lines replace, not add to, the ~20 lines budgeted for the residually finite corollary (rev2 decision 22),
  which this subsumes.

### (d) Reader-facing trade-off
The note stops exhibiting one group and characterizes a classical class: the groups of Theorem 1 and their relatives
are exactly the receptacles for finitely generated LEF groups, so LEF is what a subgroup of such a group can be. It is
strictly stronger than the residually finite corollary and costs about 11 lines more. The reader must accept two new
facts, Ore's theorem and Whitehead's lemma, and one new object, the lamplighter action.

### (e) Status
- `tower-simplicity-holds-for-topologically-free-actions` + `-proof` (this lane, `f21f2493bc`): established,
  **unreviewed**. Queued with sk-verify-4.
- `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` (peer, `22e2749154`): established, **unreviewed**.
- `rf-groups-lie-in-derived-subgroups-of-rf-groups` (peer): **two independent PASSes** (sk-verify-3, sk-verify-4).
- `elementary-groups-over-fg-rings-have-property-t`, and LEF for subgroups of ultraproducts of finite groups: on main
  and reviewed.
- Recommendation: land the §1 patch now, since it is length neutral and strictly weakens a hypothesis; hold the
  corollary until a verifier passes the lamplighter host and this lane's node.

## 3. Why the corollary needs nothing else from the note

With the §1 patch, Theorem 1's proof reads as a proof of: *for a finitely generated group `L` acting minimally and
topologically freely on a Cantor set with `LC(Z,F_2) ⋊ L` finitely generated and LEF as a ring, `EL_3` of that ring is
an infinite finitely generated simple Kazhdan LEF group.* The note never has to say this in that generality; the
corollary's proof invokes it by pointing at the two places where the shift was used. If main prefers, one sentence at
the head of the proof of Theorem 1 ("the argument uses the shift only through minimality and the absence of periodic
points") makes the invocation explicit for 1 line.

## 4. What I checked in the peer chain, and what I did not

Checked by re-derivation, no error found:
- minimality of `L ↷ F_2^Δ`, and topological freeness in both cases `δ = 1` and `δ ≠ 1`;
- `R` finitely generated, with the cylinder indicators generated from `e_{x(1)=1}` and the units;
- the model space `F_2^(Q_n) × Q_n` is the finite group `F_2 ≀ Q_n` acting on itself by the regular action, and the
  affine formula of the peer's Lemma 3 is that action;
- partial multiplicativity of `ℓ ↦ σ_ℓ` for large `n`, from the ball isomorphisms of the `Q_n`;
- injectivity of the ultraproduct map from simplicity of `R`, since the map is unital;
- the Whitehead identity `diag(a,a^(-1))diag(b,b^(-1))diag((ab)^(-1),ab) = diag(1,a^(-1)b^(-1)ab)`, and that
  `ℓ ↦ diag(u_ℓ,1,1)` is an injective homomorphism (unlike `ℓ ↦ diag(u_ℓ,u_ℓ^(-1),1)`, which is not one);
- `Γ ⊆ [Δ,Δ] ⊆ [L,L]`, using `L^(ab) = F_2 × Δ^(ab)`.

Not checked: Ore's paper itself, the finite-model bookkeeping of the peer's Lemma 3 at the level of individual words,
and any literature search for prior versions of the characterization. Kionke–Schesler (arXiv:2304.09307, Thm 1.2)
give the residually finite input and no property (T); the LEF input with (T) is new within the swarm's bounded checks.

A cheaper overgroup step would remove Ore from the note. Two candidates fail and are recorded here so that nobody
retries them: `γ ↦ (γ,γ^(-1))` into `Γ ≀ Z/2` is not a homomorphism unless `Γ` is abelian, and any positionwise map
into `Γ ≀ P` has abelianized image a multiple of `γ̄`, which is nonzero in general.

## 5. Firewall: there is no single receptacle

No one countable group contains every finitely generated LEF group: the note's own corollary gives continuum many
pairwise nonisomorphic groups `G_X`, each LEF, while a countable group has only countably many finitely generated
subgroups. So the corollary must quantify over hosts, as it does. This is worth one clause if a reader might expect a
universal object, and nothing more.
