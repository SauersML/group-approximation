# Proposal for the note: other acting groups (sk-general-actions-a)

Target: `simple_kazhdan_sofic_group.tex`. Line numbers refer to the frozen copy `manuscript-disk-1646.tex` (md5 7b3dc4ec…).
Mathematics and proofs: `research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md`.

## Summary
- The note's proof runs verbatim over any finitely generated group `Γ` acting freely and minimally on a subshift with finite models: for every finite window, some finite subshift has the same patterns.
- Such subshifts exist exactly over residually finite groups.
- I recommend a short unnumbered subsection at the end of §1 (Tier 1). Tier 2 adds the construction for every residually finite group.
- I do not recommend moving the headline to `Γ`: the answer to Brown, Ozawa and Pestov is hypothesis-free over `Z`, and `Γ`-notation throughout the proof costs the reader more than a remark does.

## (a) Placement
Insert between disk l.227 (`...completing the proof.\hfill$\square$`) and l.229 (`\section{Every word-problem degree}`). Nothing else changes.
- The note has no remark environment, so this uses `\subsection*`.
- `\SL` is already defined (l.15).
- If other lanes change `EL_3` to `EL_n` or `F_2` to `F_q`, the text adapts verbatim.

Current text (l.226-229), verbatim:
```
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$

\section{Every word-problem degree}
```

### Tier 1 (recommended): insert after l.227
```latex
\subsection*{Other acting groups}
The proof works for other acting groups. Let a finitely generated group
$\Gamma$ act freely on an infinite minimal subshift $X\subseteq A^{\Gamma}$
by $(\gamma x)(h)=x(h\gamma)$, and suppose that for every finite
$F\subseteq\Gamma$ some finite subshift has the same $F$-patterns as $X$.
If $\gamma\ne e$, compactness gives a finite $F\ni e$ such that every
$x\in X$ has $x(h)\ne x(h\gamma)$ for some $h\in F$. So $\gamma$ fixes no
point of a finite subshift with the $(F\cup F\gamma)$-patterns of $X$,
and in particular $\Gamma$ is residually finite. Replace $u^j$ by
$u_\gamma$, bounds on exponents by bounds on word length, and the
periodic sequence $y$ by a finite subshift $Y$ with the patterns of $X$
on a window so large that no nontrivial $\gamma^{-1}\gamma'$, with
$\gamma,\gamma'$ among the exponents involved, fixes a point of $Y$.
Then the argument above shows that $\EL_3(\LC(X,\F_2)\rtimes\Gamma)$ is an
infinite finitely generated simple group with property~\textup{(T)} that
is LEF.
```

### Tier 2 (optional): continue the same subsection
```latex
Conversely, every infinite finitely generated residually finite group
$\Gamma$ has such subshifts. Choose normal subgroups
$\Gamma=K_0>K_1>\cdots$ of finite index with $\bigcap_mK_m=1$ and
$[K_m:K_{m+1}]\ge3$. Let $x\in\{0,1,2\}^{\Gamma}$ have $x(e)=1$, be
constant on each coset of $K_{m+1}$ contained in $K_m\setminus K_{m+1}$,
and take the values $1$ and $2$ on exactly one of these cosets each. Then
$x(hk)=x(h)$ whenever $h\notin K_n$ and $k\in K_n$. If
$FF^{-1}\cap K_n=1$, then for each $\sigma$ at most one $h\in F$ has
$h\sigma\in K_n$, and there $x(h\sigma k)$, $k\in K_n$, takes every value
of $x$ on $K_n$. So the configurations that agree with $x$ off $K_n$ and
are constant on $K_n$ form a finite subshift with the $F$-patterns of
$X=\overline{\Gamma x}$. Each $F$-pattern of $x$ also recurs along a coset
of some $K_m$, so $X$ is minimal. Finally, let $\gamma\notin K_n$, let $T$
be a transversal of $K_n$, and let $\sigma\in\Gamma$. If
$\sigma^{-1}\gamma\sigma\in K_m\setminus K_{m+1}$, one of the two cosets
of $K_{m+1}$ in $K_m\setminus K_{m+1}$ valued $1$ and $2$ contains some
$h\sigma$ with $h\in T$ and $x(h\sigma)\ne x(h\gamma\sigma)$. So $\gamma$
fixes no point of $X$. This applies, for example, to $\SL_3(\Z)$.
```

## (b) Proof text
Both tiers carry their own proofs, and the text above is complete as it would appear.
- Tier 1: the necessity of residual finiteness is proved in the paragraph. The sufficiency is the note's proof after the stated substitutions; each substituted step is written out in artifact §1, Steps 1–5.
- Tier 2: the construction and its three properties (finite models, minimality, freeness at every point) are proved in the paragraph. Artifact §3 gives every detail.

Two points a careful reader will check, both handled in the artifact:
- **Towers.** With `E_{γδ}(W)=e_{γW}u_{γδ^{-1}}`, the coefficients `e_C` and `e_C u_t` are `E_{ee}(C)` and `E_{e,t^{-1}}(C)`, so no translate of `C` is needed. The partition condition is `C∩γC=∅` for `γ∈B_{2w+2}\setminus\{e\}`.
- **Distinctness.** In the finite models, distinctness of the cyclic diagonals (disk l.142-144, "N larger than twice the largest absolute exponent") becomes the no-fixed-point condition in Tier 1, which the same compactness sentence supplies.

## (c) Length
- Tier 1: +16 source lines (about 11 typeset lines).
- Tier 2: +21 source lines (about 15 typeset lines).
- No deletions.

## (d) Reader-facing trade-off
- **Tier 1.** The theorem is stronger at small cost: the reader learns that the construction works over every finitely generated group with finite-model subshifts, and that these groups are exactly the residually finite ones. No new machinery is needed. The one new fact to trust is the routine substitution, whose only nonobvious step (no fixed points) is proved in the paragraph.
- **Tier 2.** It adds, with complete proof, one simple Kazhdan LEF group for every infinite finitely generated residually finite group (e.g. `SL_3(Z)`). The cost is fifteen typeset lines that answer no published question I know of (bounded: repository graph only; sk-questions-ggt may find one).
- **Not proposed:** "every f.g. RF group embeds in a simple Kazhdan LEF group". The Whitehead map `γ↦diag(u_γ,u_γ^{-1},1)` is not a homomorphism for nonabelian `Γ` (artifact §5). Only `[Γ,Γ]` embeds, via `c↦diag(1,c,1)`.

## (e) Status
- New Cairn claims, all unreviewed, review requested from sk-referee-1:
  - `finite-model-subshift-elementary-groups-simple-kazhdan-lef` (Theorem G, the note's tower proof over `Γ`);
  - `free-subshift-with-finite-models-forces-rf-group` (Proposition N);
  - `rf-groups-have-free-minimal-subshifts-with-finite-models` (Proposition E).
- Reviewed nodes on main that cover the same family by other proofs:
  - `rf-subshifts-are-periodic-window-approximable` (the finite-model condition, PASS);
  - `rf-toeplitz-subshifts-over-residually-finite-groups` (binary Toeplitz, PASS twice);
  - `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` (PASS twice);
  - `residually-finite-actions-give-matricial-crossed-products` (PASS).
- Credit to add if Tier 2 is used: Toeplitz arrays over residually finite groups (Krieger; Cortez–Petite, J. London Math. Soc. 78 (2008)). Bibliographic details are for sk-citations to verify. Tier 1 needs no new citation.
