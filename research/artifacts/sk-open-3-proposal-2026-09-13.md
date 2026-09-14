# sk-open-3 proposal: a concrete Fibonacci instance of the finite models (2026-09-13)

Lane sk-open-3 (lens: the object itself). The nodes are unreviewed; review is queued with sk-referee-2. Line numbers
refer to `sk/manuscript-disk-1646.tex`.

## Recommendation first
- The disk note cut main's Remark [the Fibonacci subshift] (b965d63ba l.497-512).
- If the note keeps a concrete example, use Option B (3 lines). Option A (11 lines) proves B's claims inside the note.
- If the note stays purely general, add nothing: the general construction l.123-149 already covers Fibonacci.
- By reader merits, B gives a checkable instance with explicit numbers at almost no length.

## Option B (preferred if any)
**(a) Current text, l.146-152:**
```latex
For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}.
```
**Replacement.** The same text, followed by a new paragraph:
```latex
For the Fibonacci subshift of $a\mapsto ab$, $b\mapsto a$, the Fibonacci
words $f_1=a$, $f_2=ab$, $f_{k+1}=f_kf_{k-1}$ give these models: the ball
of radius $r$ in the generators $e_{ij}(s)$ maps injectively into
$\GL_{3|f_k|}(\F_2)$, preserving products, once $|f_k|\ge 4r$.
```
- (b) Proof, as the reader would supply it: Option A below.
- (c) Length: +4 lines.
- (d) Trade-off: the reader gains an explicit model sequence and radius bound for one subshift, and must trust two
  standard facts about Fibonacci words (`f_kf_k` occurs; `f_k` is primitive). No new machinery.
- (e) Status: `fibonacci-words-model-balls-of-fibonacci-kazhdan-group` item 4, unreviewed.

## Option A (the same with its proof)
**(a)** Same insertion point, after l.152.
```latex
For the Fibonacci subshift of $a\mapsto ab$, $b\mapsto a$, take for the
periodic word the Fibonacci word $f_k$, where $f_1=a$, $f_2=ab$ and
$f_{k+1}=f_kf_{k-1}$. The word $f_kf_k$ occurs in $X$, since
$f_{k+3}=f_{k+1}f_kf_kf_{k-1}$, and $f_k$ is not a proper power, since
$|f_k|$ is coprime to its number of $b$'s. So every word of $f_k^\infty$
of length at most $|f_k|+1$ occurs in $X$. By the Morse--Hedlund bound,
$f_k^\infty$ has at least $L+1$ words of each length $L<|f_k|$, so it has
all words of $X$ of that length. Products in the ball of radius $r$ need
windows of radius $2r$, and differences need radius $r$. So that ball maps
injectively into $\GL_{3|f_k|}(\F_2)$, preserving products, once
$|f_k|\ge4r$. For $r=1$ this is $\GL_{15}(\F_2)$.
```
- (b) Complete as written. The window-radius sentence refers the reader to l.137-144.
- (c) Length: +11 lines.
- (d) Trade-off: as in B, with the proof inside. Longer, and still only an example.
- (e) Status: as in B.

The sharp version (`|f_k| ≥ 2r+2`) needs the near-cube `f_k^2 f_{k-1}f_{k-1}f_{k-2}` and three more lines. It is
not recommended for the note. Proof and data: `research/artifacts/sk-open-3-fibonacci-models-2026-09-13-part1.md`.

## Factual flags for main (not proposals)
1. **"First finite model $\SL_{15}$" is not minimal.**
   - main b965d63ba l.153 and l.509-512 say "first finite model $\SL_{15}(\F_p)$".
   - With the 24 involutions `e_ij(s)`, `s ∈ {1, u^{±1}, χ_a}`, the circular word `aba` already gives an injective
     partial homomorphism on `B_2` (445 elements, all 198,025 products checked) into `SL_9(F_2)`. `ab` fails on `B_1`.
   - If a Fibonacci remark returns, say "the model from $abaab$" (whose images generate $\SL_{15}$) and drop "first".
   - Evidence only: an exact computation on MSI, `fibball.py`.
2. **Morse–Hedlund citation.**
   - The complexity bound ("an aperiodic sequence has at least m+1 words of length m", main l.463-465) is from Morse and
     Hedlund, *Symbolic dynamics*, Amer. J. Math. 60 (1938), not from the 1940 Sturmian paper the disk bibliography
     carries (l.302-306).
   - This is recalled, not re-verified here. sk-citations owns the check.
3. **Kazhdan constant for binary alphabets.**
   - EJZ (6.2), verified from the page image of arXiv:0809.4095v2 p.34, is
     `κ(EL_n(R),Σ) ≥ 1/(8(12√(2d)+2√(3n)+36√2))`.
   - For a binary alphabet, `e_b = 1 - e_a`, so d = 3 suffices: κ > 1/691 for 24 involutions. The peer node
     `subshift-el3-models-explicit-kazhdan-constant` has 1/727 for the 30-generator set with d = 4. Its formula and
     arithmetic are correct.
   - This matters only if the note prints a constant.
