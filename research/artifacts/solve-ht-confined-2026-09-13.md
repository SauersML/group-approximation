# Confined subgroups of Kac--Moody lattices and high transitivity (2026-09-13)

Lane `solve-ht-confined`. Target: `fp-simple-kac-moody-lattices-are-highly-transitive`
(BFFHZ Question 3.6, part one), route (b): a confined subgroup with no faithful highly
transitive action.

## Verdict

**Route (b) is closed against every known obstruction.** Every confined subgroup of
`G(F)` is lim-free and MIF, and satisfies every necessary condition for high
transitivity that Le Boudec--Matte Bon list. The natural candidates are not even
confined:
- stabilizers of points of the curtain model;
- subgroups with a smaller limit set;
- stabilizers of limit points.

The question itself stays OPEN.

## Source pins

**Le Boudec--Matte Bon**, *Confined subgroups and high transitivity*, Ann. H.
Lebesgue 5 (2022) 491--522, PDF on MSI (`/scratch.global/sauer354/km-ht/lbmb/lbmb.pdf`),
read as page images:
- **p. 492:** "A subgroup $H$ of $G$ is called a confined subgroup if the closure of the
  $G$-orbit of $H$ in Sub($G$) does not contain the trivial subgroup. Equivalently, $H$
  is a confined subgroup if there exists a finite subset $P$ of non-trivial elements of
  $G$ such that $gHg^{-1} \cap P$ is not empty for every $g \in G$."
- **Theorem 1.1 (p. 493):** "Suppose that a group $G$ admits a faithful and highly
  transitive action on $\Omega$ and that $G$ is not partially finitary. If $H$ is a
  confined subgroup of $G$, then $\Omega_{H,f}$ is finite, and the action of $H$ on
  $\Omega \setminus \Omega_{H,f}$ is highly transitive."
- **Corollary 1.4 (p. 493):** "Let $G$ be a group that is not partially finitary, and
  let $H$ be a confined subgroup of $G$. If $H$ does not admit any faithful highly
  transitive action, then neither does $G$."
- **Lemma 2.1 (p. 496):** "Suppose that the action of $G$ on the compact space $Y$ is
  topologically nowhere free. Then for every $y \in Y$, the germ stabilizer $G^0_y$
  (and hence the stabilizer $G_y$) is a confined subgroup of $G$."
- **§2.3 (p. 496):** "we call a group $G$ partially finitary if $G$ admits an embedding
  into the symmetric group Sym($\Omega$) over an infinite set such that the image of $G$
  contains Alt$_f(\Omega)$."
- **§2.4 (pp. 497--498):**
  - "As far as we know, at the moment these observations provide the only known
    obstructions to the existence of highly transitive actions of a countable group."
  - "every non-trivial normal subgroup of $G$ has trivial centralizer in $G$"
  - "the group $G$ admits all finite symmetric groups (hence all finite groups) as
    subquotients"
  - "$G$ cannot satisfy a non-trivial identity"
  - "By [HO16, Theorem 5.9], if a group $G$ admits a faithful highly transitive action
    and $G$ is not partially finitary, then $G$ does not satisfy a mixed-identity."

**Rybak**, arXiv:2605.14159v3, TeX on MSI (`km-ht/2605.14159.d/main.tex`):
- l.180 and l.183: definitions of topologically free and lim-free.
- l.345, l.351--356, l.358, l.360, l.364--369, l.371--392, l.395--398, l.401--404:
  standard hyperbolic facts (F1)--(F7).
- Theorem `real main theorem`, l.946--952.
- Proof of Proposition A, l.1549--1560.

**Choi--Gekhtman--Yang--Zheng**, arXiv:2405.09070, TeX on MSI (`km-ht/cce/src/main.tex`):
- Corollary `FullLimitSet`, l.2683--2685.
- Standing assumption of a proper action, l.870; proper geodesic space, l.954.

This is the closest statement found; it doesn't cover non-proper actions.

## Landed nodes

- `confined-subgroups-of-lim-free-actions-have-full-limit-set`, with route
  `lim-free-confined-subgroups-full-limit-set-proof`: a direct proof. It uses the
  north--south dynamics of a loxodromic `l` whose attracting point `l^+` is moved by
  every element of the confining set.
  1. **No bounded orbit.** Conjugating an elliptic `H` by `l^n` drags its orbit to
     `l^+`, so a confining element would fix `l^+`.
  2. **Full limit set.** Choose `l^-` outside `Λ_S(H)`. Then `l^n Λ_S(H)` shrinks to
     `l^+`, and the same contradiction follows.
  3. **No fixed boundary point.** A fixed limit point has a dense orbit by minimality,
     so push it onto a generic point.
- `rybak-general-type-limit-set-topologically-free-iff-mif` (import), with route
  `rybak-limit-set-mif-criterion-citation`.
- `fp-simple-kac-moody-lattices-are-lim-free` (import), with route
  `fp-simple-kac-moody-lattices-lim-free-citation`.
- `kac-moody-lattice-confined-subgroups-are-lim-free-and-mif`, with route
  `kac-moody-confined-subgroups-lim-free-proof`.

## Search record

Two web searches on 2026-09-13:
- "highly transitive Kac-Moody groups over finite fields confined subgroups";
- "confined subgroups topologically free action limit set hyperbolic space mixed
  identity free".

They returned LBMB, Rybak, Choi--Gekhtman--Yang--Zheng and unrelated Kac--Moody
papers. No result on high transitivity of these groups was found. This is a spot
check, not exhaustive.

## Exact gap

1. **(a) Positive.** A globalization mechanism for lim-free weakly hyperbolic groups
   that don't split. The theorem above shows the class is closed under passing to
   confined subgroups, which is consistent with the LBMB inheritance of high
   transitivity, but it gives no construction.
2. **(b) Negative.** An obstruction to high transitivity beyond LBMB §2.4 that holds
   for some lim-free MIF subgroup of `G(F)` confined in `G(F)`. No such obstruction is
   known.
