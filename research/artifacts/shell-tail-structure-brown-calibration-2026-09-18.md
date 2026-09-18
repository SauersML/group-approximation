# Tail-structure Brown complexes for A_1 die on a calibration world, 2026-09-18

Target: `decidable-inputs-have-fp-one-singularity-shell-stabilizer` (OPEN).
Role: inverter, family calibration. Written proof, not formalized, not
independently reviewed. Verdict: a dead approach, with the step where it dies.

## 0. The reframing: A_1 is the V-absorption of its germ group

Notation is that of `research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md`:
C={0,1}^N, p=0^infinity, rows C_n=0^n 1 C, so C minus {p} is the disjoint union
of the rows. NearSym(N) is the group of bijections between cofinite subsets of N
modulo agreement off a finite set, and eta is the near index.

For a subgroup Q of NearSym(N) containing the shift tau, define the
**V-absorption** V[Q] to be the set of homeomorphisms f of C such that f(p)=p, f is
locally in V at every point other than p, and for some M and some injection
q: N_{>=M} -> N with cofinite image and germ in Q,

    f(0^n 1 z) = 0^(q(n)) 1 z      for all n >= M and all z.

Every element of E_nu fixing p with sing in {p} has a germ of this row form. This
holds for the generators hat(g) and s, and row forms are closed under composition.
By Lemma 3.1 of the reduction artifact and (4.0) there, A_1 = V[Q] with
Q=(E_nu)_p=<rho(P),tau>. The kernel of the germ map is K, the directed union of the
groups V(C minus 0^m C), and V[<tau>] = V_p.

## 1. Tail-structure stabilizers

For m >= 1, let S_m be the set of f in V[Q] that map every row C_n with n >= m onto
some row C_(q(n)) with n' >= m, by the prefix map 0^n 1 z -> 0^(q(n)) 1 z, where q
is a bijection of N_{>=m}. These are the stabilizers of the standard row structure
on the tail 0^m C. Let Q_0 = {x in Q : eta(x)=0}.

**Lemma 1.** S_m = V(C minus 0^m C) x Qtilde_m, an internal direct product, where

    Qtilde_m = {bijections q of N_{>=m} whose germ lies in Q_0},

acting by the row prefix maps and as the identity on C minus 0^m C. There is an
exact sequence 1 -> FSym(N_{>=m}) -> Qtilde_m -> Q_0 -> 1.

*Proof.*
- **Factors commute.** An element f of S_m preserves 0^m C, and hence its
  complement, which is clopen and avoids p.
  - The restriction to the complement, extended by the identity, is locally V
    everywhere, so by (F1) it lies in V(C minus 0^m C).
  - The restriction to 0^m C is a row permutation by a bijection q of N_{>=m}.
    Its germ equals germ_p(f), which lies in Q. A bijection of N_{>=m} has index 0.
- **Every such q occurs.** Given a bijection q of N_{>=m} with germ in Q_0, define
  f to act on the rows n >= m by q, to be the identity elsewhere, and to fix p.
  - f is a homeomorphism. Rows are clopen and accumulate only at p, and q moves
    rows near infinity to rows near infinity.
  - f is locally V off p, and its germ lies in Q.
  - So f lies in A_1 = V[Q] by Lemma 3.1.
- **The two factors have disjoint supports**, so the product is direct.
- **The kernel of Qtilde_m -> Q_0** is the group of finitary bijections.
- **Surjectivity.** Let a germ x in Q_0 be represented by a bijection A -> B between
  cofinite subsets of N_{>=m}.
  - Since eta(x)=0, the complements of A and B in N_{>=m} have equal finite size.
  - Extend the representative by any bijection between them.

QED.

**Lemma 2 (the shell case).** Let Q be the shell germ group. Then
Q_0 = ker(eta_R) x ker(eta_R) inside the parity fiber product
F_nu = R_nu x_Z R_nu of `shell-germ-group-has-index-two-fiber-product`.
Consequently, if Qtilde_m is finitely generated, then ker(eta_R) is finitely
generated.

*Proof.*
- **Index of a parity-preserving element.** The index of (a,b) in F_nu is
  eta(a)+eta(b)=2 eta(a).
- **Parity-swapping elements are not in Q_0.** Such an element is tau(a,b), with
  index 1+2eta(a), which is odd and hence nonzero.
- **Hence the product decomposition.** Q_0 is contained in F_nu, and there it is
  ker(eta_R) x ker(eta_R).
- **The finite-generation consequence.** A quotient of a finitely generated group
  is finitely generated. Apply this to Qtilde_m -> Q_0, and then to the projection
  onto the first factor.

QED.

So a Brown-criterion proof of finite presentation of A_1 whose vertex stabilizers are
the S_m needs two things: ker(eta_R) finitely generated (both eta and -eta in
Sigma^1 of R_nu), and Qtilde_m finitely presented. The first is strictly stronger
than the ascending gate of `shell-germ-fp-is-an-ascending-hnn-gate`, which allows a
strictly ascending union.

## 2. The calibration world: two rays

Let Q_2 be the subgroup of NearSym(N) of germs x of the following form:
- x preserves or exchanges the parity classes E (evens) and O (odds);
- near infinity, x is a translation on each class.

It contains tau.

**Lemma 3.** V[Q_2] is isomorphic to the setwise stabilizer Stab_V({p,q}), where
q=1 0^infinity. In particular V[Q_2] is finitely presented.

*Proof.*
- **Decomposition of the target.** Write C minus {p,q} as the disjoint union of the
  rows 0^j 1 C for j >= 1 and the rows 1 0^j 1 C for j >= 0.
- **Row map.** Define phi: C minus {p} -> C minus {p,q} by prefix maps on rows:

      0^(2k) 1 z -> 0^(k+1) 1 z,       0^(2k+1) 1 z -> 1 0^k 1 z.

- **Conjugating V[Q_2] into Stab_V({p,q}).** Let f be in V[Q_2]. Then
  phi f phi^-1 extends to a homeomorphism of C fixing {p,q} setwise, and it is
  locally V off {p,q}.
  - Near p and q it is a prefix map 0^a z -> 0^b z, or 1 0^a z -> 1 0^b z, or one
    of the swapped forms, because x in Q_2 translates each parity class.
  - So it is locally V everywhere, and it lies in V by (F1).
- **The converse.** Every element of Stab_V({p,q}) has germs at p and q that are
  prefix maps of those shapes. So phi^-1 v phi lies in V[Q_2]. It is a row form with
  germ in Q_2, and it is locally V off p.
- **Finite presentation.** Stab_V({p,q}) is finitely presented by
  `contracting-srn-rational-stabilizers-are-fp` (trivial self-similar group, B=V).

QED.

**Lemma 4.** For every m >= 1, the tail-structure stabilizer S_m of V[Q_2] is not
finitely presented.

*Proof.*
- **The subgroup H.** Let H be the subgroup of Qtilde_m of bijections that preserve
  parity near infinity. It has index at most 2.
- **H is Houghton's group.** Order N_{>=m} as a line Z: the evens are listed
  outward toward -infinity and the odds outward toward +infinity.
  - A parity-preserving germ of index 0 translates E by 2a and O by 2b with
    a+b=0. On the line this is a single translation.
  - So H is the group of bijections of Z that agree with one translation near both
    ends. That group is FSym(Z) x| <t>, which is H_2.
- **H is not finitely presented.** By `houghton-h2-is-not-fp2-over-q`, H is not of
  type FP_2 over Q, so it is not finitely presented.
- **Qtilde_m is not finitely presented.** Finite presentation passes to
  finite-index subgroups, and H has finite index in Qtilde_m.
- **S_m is not finitely presented.** A direct factor of a finitely presented group
  is finitely presented, being a retract, and Qtilde_m is a direct factor of S_m.

QED.

## 3. Where the approach dies

The approach is to prove that A_1 = V[Q] is finitely presented by Brown's criterion.
The group acts on a simply connected complex X, cocompactly on the 2-skeleton, with
finitely presented vertex stabilizers and finitely generated edge stabilizers. The
cells are built from tail row structures: vertices are V[Q]-translates of
(0^m C, standard rows), or finite families of them. Their stabilizers are S_m, or
groups containing some S_m with finite index.

- **It dies at the vertex-stabilizer clause.**
  - By Lemma 4, the method cannot certify even the calibration group V[Q_2], which
    is finitely presented by Lemma 3.
  - On the shell, Lemmas 1 and 2 also force ker(eta_R) to be finitely generated.
    That is a two-sided Sigma^1 condition. The one-sided gate of
    `shell-germ-fp-is-an-ascending-hnn-gate`, which is what Q FP actually
    requires, does not demand it. (Whether ker(eta_R) is finitely generated for the
    square spiral was not checked here.)
- **The invariant is the FSym-absorption Qtilde_m of the index-zero germ group.** It
  is a permutation-level (Houghton-type) group. Houghton groups gain finiteness only
  with many rays, while V[Q] absorbs both the finitary permutations and the index
  into V.
- **What this separates.** The permutation level and the V level have different
  finiteness properties: H_2 is not FP_2 over Q, while V[Q_2] is finitely presented.
- **A consequence for proofs of A_1 FP.** Any argument whose cell stabilizers
  preserve an actual row structure on a tail inherits the Houghton defect. A working
  complex must use cells whose stabilizers mix rows by V elements, as the
  Stein-Farley complexes for V do.
- **A consequence for obstructions.** An obstruction to A_1 FP cannot be read off
  at the FSym level alone, since V[Q_2] shows that level is not faithful to the
  V level.

## 4. Relation to earlier attempts

- **Brown's criterion over the germ map** (2026-09-17). That attempt lets A_1 act
  through d: A_1 -> Q, with vertex pieces d^-1(Q_v). It dies at the edge clause.
  The present complex does not factor through Q: tail stabilizers are not full
  preimages of subgroups of Q, since they only contain K partially. It dies at the
  vertex clause instead.
- **The two dead ends together.** Cells defined only by germs are too large, since
  they contain the non-finitely-generated kernel K. Cells defined by exact row
  structure are too small, since they contain FSym-absorptions. A surviving complex
  needs cells between the two: stabilizers containing V(C minus 0^m C) and mixing
  finitely many rows by V, which is V[Q]-analogue of the Stein-Farley poset of
  "finite row splittings".

## Verification boundary

This is a written proof. It uses only the ESTABLISHED claims named above, together
with (F1)-(F3) and Lemma 3.1 of the reduction artifact. No computation was used.
