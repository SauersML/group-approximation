# sk-design-example-figure: a worked example and one figure for the finite models (2026-09-14)

Lane report. It proposes text only; main decides and lands the note.

- **Base:** rev4.5 of `simple_kazhdan_sofic_group.tex`, md5 29d63f7944bccccbf9a91b0b2714c0b4 (main e7bf2c8174).
- **Candidate:** `$SK2/lanes/sk-design-example-figure/candidate.tex`, md5 f9c5e10dd3139994326762081d98ecec.

## Proposal

1. **One figure with two panels.** It floats to the top of page 2.
   - **(a)** The 5-periodic sequence 01001, which has the words of length 3 of the Fibonacci subshift, on a 5-cycle. The rotation is `P = φ(u)`; shaded nodes are the letter 1, so they show `D_1(e_1) = φ(e_1)`.
   - **(b)** A small clopen set V with two translates bV, V, aV. The arrow is ε_ab = e_{aV}u_{ab^{-1}}, which moves bV to aV.
2. **Three pointers to the figure.**
   - Introduction: after "finite models in the matrix algebras M_N(F_2)" (a), and after "GL_d(F_2) over a clopen tower" (b).
   - Section 1: at the definition of ε_ab (b).
3. **A worked example.** `\subsection*{An example}` at the end of Section 2, right after the proof of Theorem 1. It covers, in order:
   - the four words of length 3 and the approximant 01001;
   - the displayed matrices P and D_1(e_1);
   - positions 1 and 4, which have the same window 010;
   - D_1(e_1)·P^3D_1(e_1)P^{-3} = E_44, then every matrix unit, hence φ(S) generates M_5(F_2), hence the e_ij(φ(s)) generate SL_15(F_2).

No proof step and no result changes. The example makes the sentence at rev4.5 l.268–271 visible ("products of the P^iD_ℓ(e_a)P^{-i} give every diagonal matrix unit, and with P every matrix unit").

## Why this example (answering "isn't Fibonacci arbitrary?")

Every example is a choice, but this one adds no new object and has three advantages:
- **Already in the note.** The Fibonacci subshift X_{(3−√5)/2} is the one subshift the note already names (Corollary 5).
- **Smallest possible model.** Its words are as few as an infinite subshift allows (Morse–Hedlund, classical; not source-checked here). The brute force on MSI shows 01001 is, up to rotation, the unique periodic sequence of least period with exactly its four words of length 3; no period 1–4 works. So the matrices are 5×5, small enough to display.
- **Shows the one subtle step of Section 2.** Positions 1 and 4 share the window 010, so no function of a bounded window separates them, but a letter indicator times its P^3-conjugate does. That is why the proof takes products of conjugates and uses the least period.

Panel (b) pairs this with the other way the note turns dynamics into matrices: along a periodic orbit the ring maps onto M_N(F_2), and on the translates of a small set it contains M_{|B_w|}(F_2).

**Rejected alternatives:**
- **Thue–Morse:** not in the note, 6 words of length 3, least approximant period 6 (checked), and it shows no extra feature.
- **A generic periodic word with no subshift:** it shows P and D, but hides that the model sees exactly the words of X.
- **A Kakutani–Rokhlin tower picture for Section 2:** Section 2 uses periodic approximants, not towers, so the picture would not match the proof.
- **The 15×15 generators of SL_15(F_2):** too large to read.
- **Two separate floats:** one two-panel figure costs less space.

## Checks on MSI

One-shot scripts `check.py` and `check2.py` in `/scratch.global/sauer354/sk/design-example-figure/`. Output, verbatim:

```
L3 via arcs: ['001', '010', '100', '101'] 4
L3 via sample: ['001', '010', '100', '101'] True
cyclic windows of 01001: ['001', '010', '100', '101'] equal L3: True
window at t=1: 010 window at t=4: 010
least period: 5
D(e_1) diag: [0, 1, 0, 0, 1]
P^3 D P^-3 diag: [0, 0, 1, 0, 1] is diagonal: True
entry at t equals y_{t-3}: True
D * P^3 D P^-3 == E44: True
P^{t-4} E44 P^{4-t} = E_tt and P^{s-t} E_tt = E_st for all s,t: True
positions t with y_t = y_{t-3} = 1: [4]
Fibonacci least period with exactly these length-3 words: 5 words: ['00101', '01001', '01010', '10010', '10100']
Thue-Morse least period with exactly these length-3 words: 6 words: [...]
Fibonacci word prefix: 010010100100101001010 L3: ['001', '010', '100', '101']
```

- **Words of length 3:** L3 comes from the note's own coding c(θ)_t = ⌊θ+(t+1)α⌋ − ⌊θ+tα⌋ with α = (3−√5)/2, both on the arcs between the points −jα and on a 20000-letter sample. The fixed point of 0↦01, 1↦0 gives the same L3.
- **Matrix convention:** Pδ_t = δ_{t+1}, as at rev4.5 l.258, so column t of P has its 1 in row t+1.

## Compile on MSI (TeX Live 2025, pdflatex ×3)

- 0 errors, 0 overfull boxes, 0 undefined references.
- 9 pages; rev4.5 has 8, and the budget is ≤ 9.
- 2 underfull boxes, both in bibliography entries this lane did not touch (Champetier, Ozawa).
- Rendered with gs at 100 dpi and inspected:
  - Figure 1 sits at the top of page 2. The cycle arrows run 0→1→2→3→4→0 clockwise, matching Pδ_t = δ_{t+1}.
  - The example is on page 4, before "Brown's formulation".
- About 0.55 page in total: the figure with its caption is about 0.3, the example with its display about 0.25.
- **GitHub Actions:** TikZ already builds there. `mf_recognition_complexity.tex` loads tikz and is built by the same pinned `ghcr.io/xu-cheng/texlive-alpine@sha256:556e2e2c…` image in `draft-recognition-pdf.yml`, the image `draft-simple-kazhdan-pdf.yml` uses.

## If the paper is restructured

- **If the models paragraph moves to page 1** (sk-design-page-one): keep the figure next to it. Both captions are self-contained.
- **If Section 1 splits** (sk-design-structure): panel (b) goes with "Simplicity" and the example with the finite models. The figure can split into two small floats, each about 0.15 page.

## Verbatim OLD → NEW (unified diff against rev4.5)

Line delta: 775 → 842 lines (+67). Three lines of rev4.5 change, each gaining a figure pointer; everything else is added.

```diff
--- rev4.5 simple_kazhdan_sofic_group.tex (md5 29d63f79)
+++ candidate.tex (md5 f9c5e10d)
@@ -2,6 +2,7 @@
 \usepackage[T1]{fontenc}
 \usepackage{lmodern,amsmath,amssymb,amsthm,microtype}
 \usepackage[margin=1.15in]{geometry}
+\usepackage{tikz}
 \usepackage[colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue]{hyperref}
 \input{coderepo.tex}
 \hypersetup{pdftitle={Infinite simple Kazhdan groups that are limits of finite simple groups},pdfauthor={\paperauthorname},pdfkeywords={Property (T), sofic groups, hyperlinear groups, locally embeddable into finite groups, simple groups, minimal subshifts, word problem, expanders}}
@@ -76,12 +77,12 @@
 the theorem of Ershov and Jaikin-Zapirain~\cite{EJZ} the group $G_X$ has
 Kazhdan's property~\textup{(T)}~\cite{Kazhdan}. Periodic sequences
 approximating $X$ give the ring finite models in the matrix algebras
-$M_N(\F_2)$, as in the proof by Grigorchuk and Medynets that topological
+$M_N(\F_2)$ (Figure~\ref{fig:models}(a)), as in the proof by Grigorchuk and Medynets that topological
 full groups of minimal Cantor systems are LEF~\cite[Theorem~2.6]{GM}. So
 $G_X$ is a limit of the groups $\SL_{3N}(\F_2)$, which form expanders as
 in Kassabov's construction~\cite{Kassabov}. In the proof of simplicity, a nontrivial
 normal subgroup contains a nontrivial commutator lying in a copy of the
-finite simple group $\GL_d(\F_2)$ over a clopen tower, so it contains this
+finite simple group $\GL_d(\F_2)$ over a clopen tower (Figure~\ref{fig:models}(b)), so it contains this
 group and with it an elementary matrix. For derived topological full
 groups, Matui showed by a similar argument that a nontrivial normal
 subgroup meets a simple union of alternating groups on
@@ -91,6 +92,38 @@
 and any $p,q$ in it satisfy $pr+qs=0$ with $(r,s)\ne0$ by a dimension count
 on a tower over one small cylinder.
 
+\begin{figure}[t]
+\centering
+\begin{tikzpicture}[>=stealth]
+  \foreach \t/\y/\c in {0/0/white,1/1/gray!30,2/0/white,3/0/white,4/1/gray!30}{
+    \node[circle,draw,fill=\c,minimum size=5.5mm,inner sep=0pt]
+      at ({90-72*\t}:1.05) {$\y$};
+    \node[font=\scriptsize] at ({90-72*\t}:1.6) {$\t$};
+  }
+  \foreach \t in {0,...,4}
+    \draw[->] ({73-72*\t}:1.05) arc[start angle={73-72*\t},end angle={35-72*\t},radius=1.05];
+  \node at (0,0) {$P$};
+  \node at (0,-2) {(a)};
+  \begin{scope}[xshift=3.6cm]
+    \draw[gray] (0,0) -- (5.6,0) node[right,black] {$Z$};
+    \foreach \x/\l in {0.3/bV,2.4/V,4.5/aV}{
+      \draw[line width=3pt] (\x,0) -- ++(0.8,0);
+      \node[below] at (\x+0.4,-0.08) {$\l$};
+    }
+    \draw[->] (0.7,0.18) to[bend left=35] node[above] {$\epsilon_{ab}$} (4.9,0.18);
+    \node at (2.8,-2) {(b)};
+  \end{scope}
+\end{tikzpicture}
+\caption{(a) The $5$-periodic sequence $y$ with $y_{[0,5)}=01001$, which
+has the same words of length~$3$ as the Fibonacci subshift, written on a
+$5$-cycle. The unit $u$ acts as the rotation $P$, and the indicator $e_1$
+of the letter~$1$ as the diagonal matrix with $1$ at the shaded positions.
+(b) A small clopen set $V$ and two of its translates. The elements
+$\epsilon_{ab}=e_{aV}u_{ab^{-1}}$, which move $bV$ to $aV$, multiply like
+matrix units.}
+\label{fig:models}
+\end{figure}
+
 Hyperlinear groups were named by R\u{a}dulescu~\cite{Radulescu}, and sofic
 groups were introduced by Gromov~\cite{Gromov99} and named by
 Weiss~\cite{Weiss}.
@@ -173,7 +206,7 @@
 $cc^{-1}=1$ gives $c=1$ and $g=1$.
 
 Fix such $h$ and $V$, and put $d=3|B_w|$. For $a,b\in B_w$ put
-$\epsilon_{ab}=e_{aV}u_{ab^{-1}}$. Since
+$\epsilon_{ab}=e_{aV}u_{ab^{-1}}$ (Figure~\ref{fig:models}(b)). Since
 $\epsilon_{ab}\epsilon_{a'b'}=e_{a(V\cap b^{-1}a'V)}\,u_{ab^{-1}a'b'^{-1}}$
 and $b^{-1}a'\in B_{2w}$, we get
 $\epsilon_{ab}\epsilon_{a'b'}=\delta_{ba'}\epsilon_{ab'}$. As $h\ne I_3$,
@@ -269,6 +302,40 @@
 so products of the $P^iD_\ell(e_a)P^{-i}$ give every diagonal matrix unit,
 and with $P$ every matrix unit. So $\varphi_\ell(S)$ generates
 $M_{N_\ell}(\F_2)$, and Theorem~\ref{thm:general} applies.\qed
+
+\subsection*{An example}
+Let $X$ be the Fibonacci subshift $X_{(3-\sqrt5)/2}$ of
+Corollary~\ref{cor:wp}. Its words of length~$3$ are $001$, $010$, $100$
+and $101$. These are also the words of length~$3$ of the $5$-periodic
+sequence $y$ with $y_{[0,5)}=01001$, and no smaller period is possible.
+With $\ell=1$ and $y$ in place of $y_\ell$ we get $N=5$ and the model of
+Figure~\ref{fig:models}(a): $\varphi(e_0)=I-\varphi(e_1)$ and
+\[
+  \varphi(u)=P=
+  \begin{pmatrix}
+  \cdot&\cdot&\cdot&\cdot&1\\
+  1&\cdot&\cdot&\cdot&\cdot\\
+  \cdot&1&\cdot&\cdot&\cdot\\
+  \cdot&\cdot&1&\cdot&\cdot\\
+  \cdot&\cdot&\cdot&1&\cdot
+  \end{pmatrix},\qquad
+  \varphi(e_1)=D_1(e_1)=
+  \begin{pmatrix}
+  \cdot&\cdot&\cdot&\cdot&\cdot\\
+  \cdot&1&\cdot&\cdot&\cdot\\
+  \cdot&\cdot&\cdot&\cdot&\cdot\\
+  \cdot&\cdot&\cdot&\cdot&\cdot\\
+  \cdot&\cdot&\cdot&\cdot&1
+  \end{pmatrix},
+\]
+with rows and columns indexed by $t=0,\dots,4$ and zeros shown as dots.
+The windows of $y$ centered at $1$ and at $4$ are both $010$, so every
+$D_1(f)$ has equal entries at these positions. But $P^3D_1(e_1)P^{-3}$ is
+diagonal with entry $y_{t-3}$ at $t$, so
+$D_1(e_1)\,P^3D_1(e_1)P^{-3}=E_{44}$. Then $P^{t-4}E_{44}P^{4-t}=E_{tt}$
+and $P^{s-t}E_{tt}=E_{st}$ give every matrix unit. So $\varphi(S)$
+generates $M_5(\F_2)$, and the $e_{ij}(\varphi(s))$ with $s\in S$ generate
+$\SL_{15}(\F_2)$, as in Section~\ref{sec:proof}.
 
 
 \subsection*{Brown's formulation}
```
