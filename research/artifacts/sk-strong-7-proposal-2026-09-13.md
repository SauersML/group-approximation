# sk-strong-7 proposal: one operator-algebra remark for the note

Lane sk-strong-7, 2026-09-13.
- **Base:** main's `simple_kazhdan_sofic_group.tex` at tip dcad1544bd (blob md5 274f1936…, 618 lines). Line numbers refer to that blob, not to the frozen disk copy, because the note has moved on.
- **Mathematics:** `research/artifacts/sk-strong-7-operator-algebras-2026-09-13.md`, and the nodes `kazhdan-simple-quotients-countable-in-separable-factors` and `separable-factors-hold-countably-many-subshift-groups`. Both are unreviewed and queued with sk-verify-7.

## P1 (recommended): the group factors L(G_X) have countable fibres

### (a) Current text, main l.402–406
```latex
For derived topological full groups, Grigorchuk and Medynets proved that
the word problem is decidable if and only if $L(X)$ is
recursive~\cite[Theorem~1.1(3)]{GMpres}.

\section{Questions}
```

### (a, b) Replacement (the complete argument as it would appear)
```latex
For derived topological full groups, Grigorchuk and Medynets proved that
the word problem is decidable if and only if $L(X)$ is
recursive~\cite[Theorem~1.1(3)]{GMpres}.

The same count holds for the group von Neumann algebras. For a fixed
alphabet, every $G_X$ is a simple quotient of the Kazhdan group
$\EL_3(F)$, and $e_{12}(\prod_{t<m}\tau_-^t\tau_{v_t}\tau_+^t)$ lies in
the kernel if and only if $v\notin L(X)$, so different subshifts give
different kernels. The proof of~\cite[Theorem~2]{OzawaUniversal} then
shows that the unitary group of a separable $\mathrm{II}_1$ factor
contains $G_X$ for only countably many $X$. So the $\mathrm{II}_1$
factors $L(G_X)$, which embed in $\mathcal R^\omega$, fall into continuum
many isomorphism classes, each containing $L(G_X)$ for only countably
many $X$.

\section{Questions}
```

Bibitem, inserted after `\bibitem{Ozawa}` (metadata confirmed through Crossref):
```latex
\bibitem{OzawaUniversal}
N.~Ozawa, \emph{There is no separable universal $\mathrm{II}_1$-factor},
Proc. Amer. Math. Soc. \textbf{132} (2004), 487--490.
\doi{10.1090/S0002-9939-03-07127-2}.
```

### Checks behind each sentence
- **"$G_X$ is a simple quotient of $\EL_3(F)$":**
  - main l.160–181 already defines `F = F_2⟨τ_+, τ_-, τ_a⟩` with the surjection `π` onto `R`, and says `EL_3(F)` has (T) by EJZ;
  - `G = EL_3(R)` is a quotient of `EL_3(F)` (l.169–170);
  - simplicity is Theorem 1.
- **The kernel condition:**
  - `π(τ_-^tτ_{v_t}τ_+^t) = u^{-t}e_{v_t}u^t`, the indicator of `{x : x_t = v_t}`, so the product is the cylinder indicator `e_{[v]}`;
  - `e_{12}(r) = I_3` iff `r = 0`.
  This is the same element the word-problem proof uses (l.382–384), so no new notation is introduced.
- **"different subshifts give different kernels":** a subshift is determined by its language.
- **The proof of Ozawa's Theorem 2:**
  - it uses property (T) of the common group, simplicity of the quotients, and distinctness of the kernels, all present here (verbatim key step in the artifact §1.2);
  - the conclusion quantifies over subgroups of `U(M)` isomorphic to `G_X`, exactly as printed;
  - `node kazhdan-simple-quotients-countable-in-separable-factors-proof` re-derives it in full.
- **"embed in $\mathcal R^\omega$":** main l.255–260 already proves it.
- **"continuum many isomorphism classes, each containing only countably many $X$":**
  - if `L(G_Y) ≅ L(G_X)`, then `U(L(G_X))` contains `G_Y`, and `L(G_X)` is separable;
  - so each class contains countably many `X`;
  - there are continuum many `X_α` (§2 of the note), so there are continuum many classes.

### (c) Length
+10 text lines and +4 bibliography lines.

### (d) Reader trade-off
- The paragraph strengthens the corollary from groups to their II_1 factors, and it applies the note's own Kazhdan group and cylinder elements.
- The reader trusts one short published argument, Ozawa's one-paragraph proof, and needs no new machinery.
- It also places `G_X` where Ozawa's printed wish points: a family of simple Kazhdan quotients of one Kazhdan group that embeds in `U(R^ω)`.

### (e) Status
- Both nodes are established but unreviewed (sk-verify-7 queue).
- Credit is due for the phenomenon that no separable factor contains every R^ω-embeddable separable factor: Nicoara–Popa–Sasyk 2007, cited through Peterson 2026. The primary source was not read.
- The paragraph does not claim that phenomenon, so no further citation is needed.

## P2 (optional, +1 line): the McDuff factor cannot be hyperfinite
- **Where:** after "This is Brown's formulation." (main l.261).
- **Text:**
```latex
By Kirchberg's Corollary~1.2, $G$ admits no faithful representation into
the unitary group of $\mathcal R$ itself~\cite{Kirchberg}.
```
- **Support:** node `brown-mcduff-witness-for-simple-kazhdan-lef-group` (b), reviewed PASS (sk-review-2 part 3; second concurrence sk-verify-5).
- **Trade-off:** it answers Brown's parenthetical comparison with Robertson in one line, with no new citation.

## P3 (only if character rigidity enters the note): the trace simplex
If `subshift-elementary-groups-are-character-rigid` passes review and the note adopts it, the one-sentence operator-algebra form is: "the tracial states of `C*(G_X)` form the segment between the trivial character and `τ_λ`; the only amenable one is trivial, and `τ_λ` is an MF trace". Only the first clause needs rigidity; the other two follow from Kirchberg–Ozawa and the finite models. Do not add it separately from the rigidity sentence.

## Not proposed
- "No separable universal R^ω-embeddable factor": known (NPS07).
- QWEP, OAP and AP statements: routine, and they answer nothing printed.
- MF of `C*(G_X)` and Brown's Q3 for `L(G_X)`: open.
