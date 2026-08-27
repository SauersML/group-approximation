---
rg: 2
id: hilbert-embeddable-witness-for-kun-thom-wreath
kind: claim
title: A Hilbert embeddable weak-soficity witness for the Kun--Thom wreath
refuted_by: hilbert-embeddable-witness-impossible
distinct_from:
  weakly-sofic-not-sofic: that only needs *some* bi-invariant metric and is settled; this asks for witnesses whose lengths are conditionally negative definite, which is what converts them into unitary microstates.
  kun-thom-clifford-crossed-product-ce: that asks for Connes embeddability of a specific fermionic crossed product; this asks a finite-group, character-theoretic question about an existing weak-soficity construction and never mentions an algebra.
  kun-thom-clifford-extension-not-weak-mf: that settles an operator-norm question about the same cover in the negative; this asks a normalized-Hilbert--Schmidt question about finite-group approximations of it, and the two metrics are independent.
  kun-thom-wreath-weak-mf: that asks whether the same group is MF in the operator-norm matrix-corona sense; this asks whether its existing finite-group weak-soficity witnesses can be given conditionally negative definite lengths, which is a tracial question about finite groups and implies hyperlinearity rather than MF.
artifacts:
  - notes/NOTEPAD.md
---

**REFUTED (2026-08-15).**  The question is decided, negatively:
`hilbert-embeddable-witness-impossible` is established — no Hilbert
embeddable weak-soficity witness for `W` exists, and `W ∉ 𝒞_FU`.  The
chain: any witness would yield two-point approximation data at the marked
pair (`witness-yields-two-point-approximation`), and
`two-point-approximation-fails` is established via Kun--Thom Theorem 4.1
(with the unrefereed-preprint trust surface that entails).  This is the
outcome the final paragraph below called "a genuine obstruction of a new
kind": weak soficity and `𝒞_FU` are separated on `W`.  The body below is
retained as the record of the question as it was posed and of the
constraints that shaped the search.

---

Show that the weak-soficity witnesses for

```text
W = (directSum_(G/Gamma) Z/2Z) semidirect G
```

supplied by Glebsky's permanence theorem — or any other witnesses for `W`,
or for its Clifford cover — can be chosen with **Hilbert embeddable**
invariant lengths, in the sense of
`hilbert-embeddable-length-hyperlinearity`.

**The precise form, with the reparametrization named.**  Conditional
negative definiteness is not invariant under reparametrizing a length: on
`S_4` the Hamming length is Hilbert embeddable while its square is not, and
on `S_3` the `F_2`-rank length is not while its square root is.  So the
usable statement is not "the witnessing lengths `d_n` are Hilbert
embeddable" but

> there is **one** increasing `f` with `f(0)=0`, continuous at `0`, **not
> depending on `n`**, such that every `f o d_n` is Hilbert embeddable and
> bounded by `1`.

Defect and separation transport through any such `f`, so this is what the
criterion actually consumes, and it is strictly weaker than either fixed
choice.  Naming `f` is where the bookkeeping lives.

**The function, named, and two constraints removed.**  Take
`f(t)=1-exp(-t)`.  By `hilbert-embeddable-amplification` this single
`n`-independent choice does three things at once: it is a Bernstein
function, so it preserves conditional negative definiteness; it reproduces
the profile of Glebsky's cap `min{t,1}` within absolute constants, so it
replaces the cap without disturbing defect or separation; and its
reparametrizations `1-exp(-rt)` amplify any fixed positive separation to
`1-o(1)`, so the separation constant carries no content here.  What remains
of this claim is therefore exactly one thing: **is the uncapped
conjugation-invariant word metric of the error set conditionally negative
definite?**  Not the cap, not the separation level, not the factors.

**The target is a whole family, and any one member suffices.**  By
`kun-thom-clifford-cover-weakly-sofic`, every cover `Wtilde_S=Vtilde_S
semidirect G` in the invariant-graph family of
`invariant-graph-clifford-phase` is weakly sofic and not sofic: the lamp
group `Vtilde_S` is locally finite, hence sofic, `G` is residually finite by
Kun--Thom Theorem E, and Glebsky's permanence theorem applies to each of
them.  So the character test may be run against the witnesses for any `S`,
not only against those for `W` itself.  Since the marked word survives in
every such cover, a Hilbert embeddable witness for a single `S` answers
Question 3.4.  This is the one place where the invariant-graph freedom
survives — unlike the locality direction, which
`marked-double-coset-infinite-degree` closes.

Glebsky, *Extensions of a residually finite group by a weakly sofic group
are weakly sofic*, Rev. Mat. Iberoam. 39 (2023) 1097--1104, Theorem 1.1,
gives the witnesses; his proof runs through a characterization of weak
soficity by solvability of equations over groups, so the bi-invariant metric
is produced rather than prescribed, and its character expansion has not been
inspected.  The test is finite and mechanical: expand each witnessing length
in irreducible characters and check that every nontrivial coefficient is
nonpositive.

## Where the difficulty is not, and where it is

Glebsky's proof of Theorem 1.1 constructs no metric at all
(`glebsky-weak-soficity-is-metric-free`): it runs on the algebraic side of
his Lemma 1.2, whose clause (3) says a group is weakly sofic iff it is a
subgroup of a **quotient** of a direct product of finite groups.  So the
character question has to be asked about lengths on finite sub-products, and
about what survives the quotient.  Three facts, which together say the
obstruction cannot live in the factors.

- **The Hilbert embeddable lengths form a large cone.**  Nonnegative
  combinations of Hilbert embeddable lengths are Hilbert embeddable, and so
  is the pullback of one along any homomorphism, since conditional negative
  definiteness of a kernel is preserved by both operations.  The discrete
  length is Hilbert embeddable, realized by the regular representation.
- **Consequently the normalized support length**
  `ell(f)=|{alpha in A : f_alpha != 1}|/|A|` on a finite direct product
  `prod_(alpha in A) F_alpha` **is Hilbert embeddable**, being the average of
  the pullbacks of the discrete lengths of the factors.  For the Kun--Thom
  wreath the factors are copies of `Z/2`, which have two characters, so no
  difficulty can hide in the factors' character theory.
- **Both extremes of that cone nonetheless fail, and both fail on
  separation.**  The normalized support length dilutes: the marked
  involution is supported on two coordinates, so its length is `2/|A|`,
  which tends to zero — this is the no-dilution constraint below, in its
  sharpest form.  At the other extreme, the discrete length pulled back
  along `F_A -> F_A/proj_A(M)` makes the defect exactly zero, but its
  separation is zero too: a witness of that shape would be a genuine
  homomorphism to a finite group separating the mark, making `W` locally
  embeddable in finite groups, which it is not.

So the live question is entirely about the middle of the cone: a Hilbert
embeddable length on the finite sub-product which is small on the truncated
error set and at least `1/2` on the truncated lifts, **both of which lie
inside `proj_A(M)`**.  The quotient, not the factors, carries the whole
problem — and that is a finite design question to which the character test
of `hilbert-embeddable-length-hyperlinearity` applies directly.

Two constraints any witness must already satisfy.  Only the second is a
filter; the first was expected to be one and is not.

- **No dilution of a single lamp.**  Let `w=a_o a_(h Gamma)` be the marked
  involution and `a_o` a single lamp, so that `w = a_o * g a_o g^(-1)` for a
  suitable `g`.  A Hilbert embeddable `ell` need not itself be subadditive,
  but `sqrt(ell)` is: conditional negative definiteness says
  `ell(a^(-1)b)=||f(a)-f(b)||^2` for a map `f` into a Hilbert space, so
  `sqrt(ell)` is a conjugation-invariant pseudometric.  Applying the triangle
  inequality to `sqrt(ell)` and squaring, a witness separating `w` by `c`
  must give **every** lamp length at least `c/4`, up to the multiplicative
  defect.  A model in which individual lamps become asymptotically invisible
  cannot separate the mark.  This is the weak-soficity form of the fermionic
  amplification remark in notes/FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md §5.
  (Constant corrected from `c/2` to `c/4` in the adversarial audit: the
  earlier statement assumed subadditivity of `ell` itself.)

  **It is not a filter.**  `lamp-character-orbit-separation` computes the
  separation exactly by Clifford theory: for a nontrivial irreducible not
  inflated from the acting quotient, the normalized separation of a two-site
  element is twice the fraction of the character orbit meeting exactly one of
  the two sites, which for a generic orbit tends to `1/2`.  So the mark is
  separated by an absolute constant independent of the number of sites, and
  the `2/|A|` decay that made dilution look threatening is an artifact of
  averaging over singleton orbits — the worst generator in the cone, not a
  representative one.  The inequality above remains true and remains a
  necessary condition; it simply rejects nothing.
- **The error set must be at unbounded word distance from the mark.**  If
  `w` lies in `C_m(X)` — a product of `m` conjugates of `X^(±1)` — then
  `sqrt(ell)` is a conjugation-invariant pseudometric for any Hilbert
  embeddable `ell`, so `sqrt(ell(w)) <= m max_(x in X) sqrt(ell(x))` and

  ```text
  ell(w) <= d_X(w)^2 * max_(x in X) ell(x).
  ```

  The separation-to-defect ratio is therefore bounded by the **square of the
  word distance** from the error set to the mark, so a witness with vanishing
  defect and surviving mark forces `d_(X_n)(w) -> infinity`.  (For a genuine
  bi-invariant metric, subadditive outright, the bound improves to
  `d_X(w)`.)  This is the quantitative form of the no-dilution bullet, and it
  is the constraint that actually bites.

  cairn-scout's check of Definition 6 shows how sharply.  On the Clifford
  cover, `[a_p,a_q]=z` gives `a_p a_q a_p^(-1) = z a_q`, so
  `z = a_q * (a_p a_q a_p^(-1))` is a product of exactly **two** lamp
  conjugates: with `X` the single lamps, `d_X(z)=2` on the nose.  The mark
  does not merely satisfy the bound, it achieves it.  Since word distance is
  an integer and separation needs `n < d_X(w)`, the only admissible `n` is
  `1`, which is degenerate.  So **the single lamps cannot be the error set**,
  and the real lever is the choice of the test window `Phi`, since
  `X = Pr_1^k(Phi cap N)` is determined by it.
- **No finite-quotient witness.**  Every genuine homomorphism from `W` to a
  finite group kills `w`, because in a finite quotient the compression
  `t Gamma t^(-1) <= Gamma` becomes an equality, so the two marked cosets are
  identified.  The witnesses are therefore necessarily *approximate*
  homomorphisms, and the length must do the separating work that a quotient
  cannot.  The set-level shadow of this constraint is now mapped precisely
  (2026-08-15): the collapse is a conjugacy-closure fact, not a compression
  fact — compressor cosets stay separated in congruence quotients
  (`compressor-coset-two-point-exact`), while the marked coset `hΓ` dies in
  every finite quotient but only with logarithmic latency relative to any
  window (`congruence-transporter-girth`).  What stands between the
  congruence models and the two-point necessary condition of this claim is
  the deletion design of `marked-pair-cut-problem`; an expansion refutation
  of that problem, run at approximate-model strength, would refute
  `two-point-orbit-approximation` and close this lane negatively.

A positive answer answers Pestov's Question 3.4.  A negative answer — a
proof that no Hilbert embeddable witness exists for `W` — would be the first
evidence that `W` is not hyperlinear, and would be a genuine obstruction of a
new kind, since it would separate weak soficity from hyperlinearity on an
explicit group.
