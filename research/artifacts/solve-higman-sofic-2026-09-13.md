# Soficity of Higman's group H4: literature pins and quotient constraints

Lane solve-higman-sofic, 2026-09-13. Root: `higman-group-is-sofic` (OPEN).
Nothing here is independently reviewed.

## 0. Sources

All three TeX sources were fetched on MSI with `curl https://arxiv.org/e-print/<id>`
into `~/hsofic/`.

| Source | File on MSI |
|---|---|
| Helfgott--Juschenko, *Soficity, short cycles and the Higman group*, arXiv:1512.02135 | `hj/Helfgott-Juschenko.tex` |
| Kassabov--Kuperberg--Riley, *Soficity and variations on Higman's group*, arXiv:1712.07191 | `var/soficity_Higman_variations.tex` |
| Thom, *About the metric approximation of Higman's group*, arXiv:1005.0823 | `thom/main.tex` |

Glebsky's arXiv:1604.06359 was **not** fetched. His theorem is used only as
restated by Kassabov--Kuperberg--Riley.

## 1. Verbatim pins

### Helfgott--Juschenko

**l.261–262.** "It is not known whether it has amenable quotients."

**l.243.** "if a group is sofic, all of its subgroups are sofic as well."

**l.276–288, Theorem `thm:jut`.** "Let $m\geq 2$. Assume that the group $H_{4,m}$
is sofic. Then, for every $\epsilon>0$, there is an $N>0$ such that, for every
$n\geq N$ coprime to $m$, there is a bijection
$f:\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ such that $f(x+1) = m f(x)$
for at least $(1-\epsilon) n$ elements $x$ of $\mathbb{Z}/n\mathbb{Z}$, and
$f(f(f(f(x)))) = x$ for all $x\in \mathbb{Z}/n\mathbb{Z}$."

**l.326–337, Proposition `prop:norvi`.** For $p\nmid (m-1)$ and a bijection $f$
of $\mathbb{Z}/p^r$: either $f^4(x)\ne x$ for at least $p^r/2$ values, or
$f(x+1)\ne m f(x)$ for at least $p^{r/4-1}/2^{1/4}$ values. The authors add that
this is "unfortunately much too weak to contradict the conclusion of Theorem
\ref{thm:jut}".

### Kassabov--Kuperberg--Riley

**l.213.** "If $G = \BS(1,2) = \langle a,b \mid b^a = b^2 \rangle$ and
$\phi: \langle b \rangle \to \langle a \rangle$ maps $b \mapsto a$, then
$\overline \H_4(G, \phi) = H_4$."

**l.438–442.** $\H_k(G,\phi)=\langle G, t \mid t^k = 1, b^t = \phi(b)\rangle$ is
the semi-direct product of $\overline{\H}_k(G,\phi)$ with $C_k$, and
$\overline\H_k$ is its kernel to $C_k$.

**l.1187.** "If $m \not= \pm 1$, then the image of $a$ in any proper quotient
of $\BS(1,m)$ is finite."

**l.1234–1243, Theorem `th-functions-BS`.** "The group $\H_k(\BS(1,m))$ has a
sofic quotient $Q$ such that the composition $\BS(1,m) \to \H_k(\BS(1,m)) \to Q$
is injective if and only if for all $\ep >0$ there exists an integer $C$ such that
for all $n>C$ coprime to $m$, there exist a permutation
$f \in \Sym(\Z / n \Z)$ of order dividing $k$ such that $f(x+1) = m f(x)$ for at
least $(1-\ep)n$ values of $x$."

**l.262–266, Theorem `GS version`.** Such $f$ with $f$ of order dividing 4 exist
for all $m>2$.

**l.1281.** "We stress that the analogue of Theorem~\ref{GS version} is unknown
when $m=2$."

**l.1284.** "We believe that by carefully tracking all bounds one gets that
$C = O\left(2^{K \ep^{-2}}\right)$."

**l.314.** "...where soficity of $\H_k(G, \phi)$ remains unknown for $m \geq 2$."

### Thom

**l.368–372, Theorem `main`.** Commutator-contractive invariant length functions
on finite groups, $\varepsilon<1/64$, and
$d(a_i,[a_{i+1},a_i]) \leq \varepsilon$ imply $\ell(a_i) < 4 \varepsilon$.

**l.395.** Corollary `corhig`: "Higman's group does not have the
$\cF_{\rm c}$-approximation property."

## 2. Landed nodes

**New claims, established by elementary proofs** (no novelty claimed):

| Claim | Proof route |
|---|---|
| `nontrivial-higman-quotients-keep-all-four-bs-subgroups` | `higman-quotient-smallest-prime-proof` |
| `base-two-exponential-permutations-iff-sofic-higman-quotient` | `base-two-permutations-sofic-quotient-reduction-proof` |
| `almost-commuting-opposite-higman-generators-force-collapse` | `almost-commuting-higman-collapse-proof` |
| `nontrivial-higman-quotients-are-not-locally-elementary-amenable` | `higman-quotient-local-embedding-obstruction-proof` |
| `nontrivial-higman-quotients-have-tower-distorted-generators` | `higman-quotient-tower-distortion-proof` |

**Import.** `bs1m-higman-sofic-quotients-iff-exponential-permutations`, through
`bs1m-higman-exponential-permutations-citation`.

**Open claims.**
- `higman-group-is-sofic` (root).
- `order-four-exponential-permutations-exist-for-base-two`, fed by
  `higman-soficity-forces-base-two-exponential-permutations`.

## 3. What a nontrivial sofic quotient `Q = H4/N` must look like

**The central equivalence.** The base-two Helfgott--Juschenko permutations
exist if and only if some such `Q` exists.

**Constraints on `Q`:**
- **Faithful pieces.** Every generator has infinite order, and `<a,b>`, `<b,c>`,
  `<c,d>`, `<d,a>` are faithful copies of `BS(1,2)`. The four orders of a
  would-be torsion quotient contradict each other at smallest primes.
- **No commuting opposite pairs.** `[a,c]` and `[b,d]` are nontrivial, and
  quantitatively non-commuting in every bi-invariant metric: all generator
  lengths are at most `63 delta + 24 eta`.
- **Not locally elementary amenable.**
  - `Q` is not LEF, not locally embeddable into elementary amenable groups, and
    has no nontrivial homomorphism to any group whose nontrivial finitely
    generated subgroups have finite quotients.
  - So Kassabov--Kuperberg--Riley's residual solvability (Theorem `ressolvable`)
    cannot produce `Q`.
- **Tower distortion.** `|g^T(j)| <= 2^(j+1) - 1` for every generator `g`,
  where `T` is the tower function.

## 4. Attempts that died or were not run

- **Glebsky's `p`-quotient mechanism.** It needs `p | m - 1`, and base two has no
  such `p`. Torsion quotients are excluded by §3.
- **Explicit permutation search (directive step 2b).** Not run. Section 3 turns
  it into a search for approximations of a nontrivial `H4`-quotient. Even for
  `m > 2`, where the permutations exist, the threshold is believed to be
  `2^(K eps^-2)` (KKR l.1284), so a search at feasible `n` cannot separate the two
  cases.
- **A special approximation of `BS(1,2)` as a non-soficity witness (directive
  step 2c).** It dies. For amenable `G`, KKR `main-precise` (1)⇔(3) says every
  sufficiently good approximation of `BS(1,2)` admits the order-four almost
  conjugator once one does. So no clever choice of the cyclic models can witness
  non-existence.
- **Transfer of Thom's commutator-contractive theorem.** It does not apply,
  because normalized Hamming length is not commutator-contractive.
- **Amalgam over an amenable edge quotient.** Recorded in the root. An abelian
  edge image forces `c = 1`. Nilpotent and metabelian edge images are untested.

## 5. Exact gap

Decide whether `H4` has a nontrivial sofic quotient. Equivalently, decide whether
the base-two order-four permutations exist.

**Concrete sub-questions:**
- Does `H4` have a nontrivial amenable, necessarily non-elementary, quotient?
- Does `G_1 = <a,b,c | b^a = b^2, c^b = c^2>` have a sofic quotient with `b` of
  infinite order, in which `<a,c>` has an amenable image and an `a <-> c`
  invariant kernel?
