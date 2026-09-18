# Which finitely presented residually finite hosts can contain Z_(l)? (lane gq-k2-q, 2026-09-18)

Coordinator's scope for this pass: literature on residually finite Higman embeddings, excluding KMS (owned by
gq-infinite-primes); the finitely generated metabelian question; automaton and self-similar hosts. Bottleneck:
`z-localized-embeds-in-fp-rf-group`.

## 1. Literature

- **Rauzy**, arXiv:2002.02540, *Obstruction to a Higman embedding theorem for residually finite groups with solvable
  word problem*. Abstract, verbatim from the arXiv page: "We prove that, for a finitely generated residually finite
  group, having solvable word problem is not a sufficient condition to be a subgroup of a finitely presented
  residually finite group. The obstruction is given by a residually finite group with solvable word problem for
  which there is no effective method that allows, given some non-identity element, to find a morphism onto a finite
  group in which this element has a non-trivial image."
  - The obstruction is effective residual finiteness. It says nothing about infinitely generated abelian subgroups
    such as `Z_(l)`.
  - Already in the graph as `rf-higman-embedding-for-decidable-groups-fails`.
- **Kharlampovich–Myasnikov–Sapir**, arXiv:1204.6506. The abstract (read) constructs finitely presented residually
  finite groups of solvable class 3 with hard word problems. For the source reading I defer to gq-infinite-primes
  (board and `a1c262c67`): there is no embedding theorem, §1.1.7 only poses the question, and every torsion-free
  subgroup of a KMS group is finitely generated free abelian, so no KMS group contains `Z_(l)`.
- **Searches** for residually finite Higman-type embedding theorems, and for finitely presented residually finite
  groups containing `Z[1/P]` with `P` infinite, found nothing beyond these two papers. I found no general theorem
  deciding the question. It appears open.

## 2. Host classes now excluded

| class | result | node |
|---|---|---|
| finitely generated linear (any field) | roots at finitely many primes | `fg-linear-groups-have-roots-at-finitely-many-primes` |
| finitely generated metabelian | roots at finitely many primes (generic freeness on `G'`) | `fg-metabelian-groups-have-roots-at-finitely-many-primes` |
| KMS groups `G(M)` | torsion-free subgroups finitely generated | gq-infinite-primes, `a1c262c67` |
| groups acting on a tree | `Z_(l)` fixes a vertex or an end | `z-localized-fixes-a-vertex-or-end-of-every-tree` (new) |
| free-by-cyclic, and mapping tori of endomorphisms injective on `H_1(F;Q)` | no `Z_(l)` | `free-group-mapping-tori-contain-no-z-localized` (new) |
| hyperbolic, CAT(0), and more generally groups whose abelian subgroups are finitely generated | trivially excluded | — |
| quotients `St_N(R_l)/K_rf`, and `E_N(R_l)` | corner symbols | `resolvent-elementary-groups-are-not-fp`, OPEN refutation of the residual route |

The metabelian exclusion the coordinator asked for is already on main. It is a lane proof and has not been
reviewed, so it should go to referees: it carries the `≥ 3` lower bound of `z-localized-embeds-in-fg-rf-soluble-group`.

## 3. What the tree lemma says a witness must look like

A witness that splits as a graph of groups either hides `Z_(l)` in a vertex group, or builds it along an ascending
ray of vertex stabilizers. In the second case successive vertex groups must supply `q`-th roots for unboundedly many
primes `q`, as `BS(1,m)` does for the primes of `m`.
- For mapping tori of free groups this reduces to root sets of `φ`-iterates.
- There the lower central series forces the relevant element to sink through every `γ_c F`.
- An open case remains: an endomorphism that kills rational homology, with a sinking element whose iterates are
  `p`-th powers for infinitely many `p`.

## 4. Self-similar and automaton hosts (observations, not landed as nodes)

- **Z_(l) acts by finite-state automata.** `Z_(l) ⊂ Z_l` acts on the `l`-ary tree by translations `x ↦ x + r`. Each
  is finite-state, because `r` has an eventually periodic `l`-adic expansion.
- **Affine generators are not enough.**
  - Any finitely generated group of affine maps `x ↦ u x + c` of `Z_l` is metabelian, so it is excluded.
  - Conjugating the translation by `q` to the translation by `1` needs a map `g` with `g(x + q) = g(x) + 1`. Minimality
    of translation on `Z_l` forces `g(x) = x/q + const`. So a finitely generated self-similar host must produce the
    translations by `1/q` without a dilation by `q`.
- **G_l is residually `l`.** Sketch: its quotients `(Z/l^k)[y]/(y^(l^m) − 1) ⋊ (image of H)` are finite `l`-groups
  when `m >= k − 1`, and they separate points. So `G_l` acts faithfully on the rooted `l`-ary tree. Whether some such
  action is finite-state or self-similar is open, and is the natural first test for the self-similar route.
