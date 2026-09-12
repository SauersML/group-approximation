# Intrinsic sizes on the automaton monoid: retract chains, retract posets, representations

Lane `w3-simple-direct`, 2026-09-12. Target: `fg-simple-kazhdan-groups-are-surjunctive`.

By `surjunctivity-iff-automaton-monoid-directly-finite`, a group `G` is surjunctive on `A` iff
`CA(G;A)` is directly finite. For a strict `tau` with left inverse `sigma`, `e = tau o sigma` is an
idempotent automaton with `e != id`, while `sigma o tau = id`. A *size* is a function on retract
images that is constant on conjugate ones and strictly monotone along proper inclusions; a size that
is defined at `A^G` and drops on every proper retract is exactly direct finiteness.

This artifact tests the sizes built from the monoid alone, with no measure and no finite models.

Supports the Cairn claims:
- `retract-images-of-full-shifts-have-infinite-descending-chains`
- `strict-automata-copy-the-retract-poset-below-their-image`
- `directly-finite-ring-images-of-ca-monoids-kill-retracts`
- `retract-images-of-full-shifts-are-not-disjoint-unions`

Nothing here decides the target.

## 0. Conventions

- The shift is `(h.x)(g) = x(h^-1 g)`. An automaton is `tau(x)(g) = mu((x(gm))_(m in M))`, `M` finite.
- `Ret(G;A)` is the set of *retract images*: images `f(A^G)` of idempotent automata `f`. Each is a
  subshift, and `f` fixes it pointwise.
- Subshifts are *conjugate* when an equivariant homeomorphism carries one onto the other.
- `↓X` is the set of retract images contained in `X`, with inclusion and conjugacy.

## 1. Openings give infinite descending chains on every infinite group

For finite `F <= G` with `1 in F`, and `x in {0,1}^G` with support `S`, put
`gamma_F(S) = ⋃ { gF : g in G, gF <= S }` (the morphological opening by `F`).

**Lemma 1.1.** `gamma_F` is an idempotent automaton on `{0,1}^G` with memory `F^-1 F`. Its image
`X_F` is the set of configurations whose support is a union of left translates of `F`, the empty
union included.

*Proof.* `h in gamma_F(S)` iff `h = gf` with `gF <= S` for some `f in F`, iff `h f^-1 F <= S` for
some `f in F`. That reads `x` on `h F^-1 F` only, and `supp(k.x) = k supp(x)` gives equivariance.
Every `gamma_F(S)` is a union of translates, and `gamma_F(S) = S` when `S` already is one. So
`gamma_F` is idempotent with the stated image. []

**Theorem 1.2.** Let `G` be infinite and `|A| >= 2`. Then `Ret(G;A)` contains a strictly descending
chain `X_(F_0) ⊋ X_(F_1) ⊋ X_(F_2) ⊋ ...` whose members all contain the two constant configurations
`0` and `1`, with `X_(F_0) = {0,1}^G`.

*Proof.* Fix `0 != 1` in `A` and a retraction `r : A -> {0,1}`, applied sitewise. Put `F_0 = {1}`.
Given `F_n`, pick `c_n notin F_n F_n^-1`, which exists because `G` is infinite, and set
`F_(n+1) = F_n ∪ c_n F_n`. Then `c_n F_n ∩ F_n` is empty, so `|F_n| = 2^n`.
- `gamma_(F_n) o r` is idempotent, since `gamma_(F_n)` outputs `{0,1}`-configurations and `r` fixes
  them. Its image is `X_(F_n)`.
- `g F_(n+1) = g F_n ∪ (g c_n) F_n`, so every union of translates of `F_(n+1)` is one of `F_n`, and
  `X_(F_(n+1)) <= X_(F_n)`.
- The indicator of `F_n` lies in `X_(F_n)`. A translate of `F_(n+1)` has `2^(n+1)` points, so none
  fits inside `F_n`, and the only union of such translates inside `F_n` is empty. So the indicator of
  `F_n` is not in `X_(F_(n+1))`. []

**Corollary 1.3.** On every infinite group, no function from `Ret(G;A)` to a well-ordered set is
strictly monotone along proper inclusions. In particular the chain height of retract images below
`A^G` is infinite, including on `Z` and every amenable group, where surjunctivity holds. Chain-length
sizes and well-founded ranks of retract images certify nothing on any infinite host.

**Remark 1.4 (what does work over amenable groups).** Retract images are strongly irreducible: if
`f` has memory `M` and `p`, `q` are patterns of `f(A^G)` on `F_1`, `F_2` with `F_1 M ∩ F_2 M` empty,
glue preimages on `F_1 M` and `F_2 M` into one configuration `w`; then `f(w)` shows both patterns.
Over amenable groups a proper subshift of a strongly irreducible subshift has strictly smaller
topological entropy (Ceccherini-Silberstein–Coornaert; imported at statement level, not re-read, and
no node depends on it). So entropy is a real-valued size there. It is built from Følner sets, which
are finite models; it is not intrinsic to the monoid.

## 2. A strict automaton copies the whole retract poset below its image

**Theorem 2.1.** Let `sigma o tau = id` on `A^G`, and `Phi(X) = tau(X)` for `X in Ret(G;A)`.
1. `Phi(X)` is a retract image. If `X = f(A^G)`, then `tau f sigma` is idempotent and its image is
   `tau(X)`.
2. `Phi` is injective, preserves and reflects inclusion, and `tau|_X : X -> Phi(X)` is a conjugacy.
3. `Phi` maps `Ret(G;A)` onto `↓tau(A^G)`, and more generally `↓X` onto `↓tau(X)` for every `X`.

So `(Ret(G;A), ⊆, ≅)` is isomorphic to `↓tau(A^G)`, with the top `A^G` going to `tau(A^G)`.

*Proof.*
1. `(tau f sigma)^2 = tau f (sigma tau) f sigma = tau f f sigma = tau f sigma`. Since `sigma` is
   surjective, `tau f sigma (A^G) = tau f (A^G) = tau(X)`.
2. `tau` is injective, continuous and equivariant on a compact space, so it is a homeomorphism onto
   its image, and the other statements follow.
3. Let `Y = g(A^G)` be a retract image inside `tau(A^G)`. The idempotent `e = tau sigma` fixes
   `tau(A^G)` pointwise, so `e g = g`. Then `sigma g tau` is idempotent:
   `(sigma g tau)^2 = sigma g (tau sigma) g tau = sigma g (e g) tau = sigma g tau`. Its image is
   `sigma(g(tau(A^G)))`, and `g(tau(A^G)) = Y` because `g` fixes `Y` and `Y <= tau(A^G)`. So
   `sigma(Y)` is a retract image, and `tau(sigma(Y)) = e(Y) = Y`. The same computation inside `↓X`
   gives the general statement. []

**Corollary 2.2.** Let `I` be any invariant of posets carrying a conjugacy relation, and put
`d(X) = I(↓X)`. Then `d(A^G) = d(tau(A^G)) = d(tau^2(A^G)) = ...` for every strict `tau`. Every size
computed intrinsically from the retract lattice (dimension functions defined by the lattice, chain
heights, widths, lengths of maximal chains) takes equal values at the full shift and at a proper
retract whenever a strict automaton exists. Such a size separates `A^G` from its proper retracts only
on a group already known to be surjunctive, so it cannot be the input of a proof.

## 3. Representations into directly finite rings, and K-theory of the monoid algebra

Write the monoid product of `CA(G;A)` as composition.

**Proposition 3.1.** Let `S` be a directly finite ring and `rho : CA(G;A) -> (S, ·)` a monoid
homomorphism. If `sigma o tau = id`, then `rho(tau o sigma) = 1`. Hence `G` is surjunctive on `A` as
soon as some such `rho` has `rho(f) != 1` for every idempotent automaton `f != id`. Every injective
`rho` qualifies, and so does an anti-homomorphism, since `S^op` is directly finite too.

*Proof.* `rho(sigma) rho(tau) = 1`, so `rho(tau) rho(sigma) = 1`. If `tau` were strict, `f = tau o sigma`
would be an idempotent automaton different from `id` with `rho(f) = 1`. []

Directly finite targets include every ring with a faithful Sylvester rank function, for instance a rank
ultraproduct of matrix algebras. If `ab = 1`, then `ba` is idempotent and
`rk(ba) >= rk(a (ba) b) = rk(1) = 1`, so `rk(1 - ba) = 1 - rk(ba) = 0` and `ba = 1`.

**Proposition 3.2.** Let `k` be a field. In the monoid algebra `k[CA(G;A)]`, a strict pair gives the
nonzero idempotent `p = 1 - tau o sigma` with `[p] = 0` in `K_0`. Indeed `tau o sigma` and `1` are
Murray–von Neumann equivalent through `tau` and `sigma`, and `[1] = [tau o sigma] + [p]`. The
augmentation `k[CA(G;A)] -> k` sends `1 - f` to `0` for every idempotent automaton `f`, so the state it
induces never separates. A state on `(K_0, [1])` that is positive on `[1 - f]` for every idempotent
automaton `f != id` would prove surjunctivity on `A`; producing one is Proposition 3.1 at the level of
`K_0`.

**Remark 3.3 (the representations the monoid carries).** Without finite models, `CA(G;A)` acts in three
natural ways, all separating idempotents from `id`, and none lands in a directly finite ring:
- on `A^G`, by continuous self-maps of a Cantor set;
- on `C(A^G, k)` by pullback `h -> h o tau`, an anti-homomorphism into the endomorphisms of an
  infinite-dimensional space, which are not directly finite. Its multiplicative refinement at constant
  configurations is the formal Jacobian of family F. That is defined only on formalizable pairs and lands
  in `M_n(F_p[G])`, so it consumes Kaplansky stable finiteness
  (`formal-polynomial-strict-pairs-need-unstable-linearization`);
- on invariant probability measures, by pushforward through affine maps. A size there is a measure
  functional; for the uniform Bernoulli measure it is `every-injective-ca-preserves-uniform-bernoulli-measure`.

Restricted to linear automata over `F_p^n`, a separating `rho` proves `M_n(F_p[G])` directly finite, so
Proposition 3.1 is at least as strong as Kaplansky's direct finiteness at that matrix size.

## 4. Grothendieck invariants of subshifts

**Proposition 4.1.** Let `G` be infinite. No retract image of `A^G` is a disjoint union of two nonempty
subshifts.

*Proof.* Let `X = f(A^G)`, where `f` has memory `M`, and suppose `X = X_1 ⊔ X_2` with `X_1`, `X_2`
nonempty subshifts. `X_1` is clopen in `X`, so for some finite `W` and some set `P` of `W`-patterns,
`x in X_1` iff `x|_W in P`. Choose `g` with `W M ∩ g W M` empty, which `G` being infinite allows. Take
`y in X_1`, `z in X_2` and `f`-preimages `y'`, `z'`. Let `w` agree with `y'` on `W M` and with `g.z'` on
`g W M`, and put `x = f(w)`. Then `x|_W = y|_W`, so `x in X_1`. Also `x|_(gW) = (g.z)|_(gW)`, so
`(g^-1.x)|_W = z|_W`, which puts `g^-1.x`, hence `x`, in `X_2`. That is a contradiction. []

**Consequence 4.2.** In a Grothendieck group of subshifts modulo conjugacy with `[X ⊔ Y] = [X] + [Y]`,
retract images are indecomposable, so no relation writes `[A^G]` as `[f(A^G)]` plus a remainder. Every
conjugacy-invariant class, additive or multiplicative (`[X × Y] = [X][Y]`), is equal at `A^G` and at
`tau(A^G)` when `tau` is strict, because `tau` is a conjugacy onto its image. No such class can record
the drop.

## 5. Where it stops

- **Built from the monoid alone,** each candidate fails in one of three ways:
  - infinite on every infinite group: chain heights (Corollary 1.3);
  - equal at `A^G` and `tau(A^G)` whenever a strict `tau` exists: lattice invariants and conjugacy
    classes (Corollary 2.2, Consequence 4.2);
  - reduces to a representation into a directly finite ring that separates idempotents, which restates
    the problem (Propositions 3.1, 3.2).
- **The sizes on record come from outside the monoid:**
  - Følner entropy and sofic counting, which are finite models;
  - Bernoulli measure preservation, which is equivalent to the goal;
  - formal Jacobians into `M_n(F_p[G])`, which consume Kaplansky and exist only on formalizable pairs.
- **The known surjunctive nonsofic groups** (the Kun–Thom wreaths and doubles) get their size by peeling
  and local transfer into sofic or residually finite groups, i.e. from borrowed finite models. A finitely
  generated simple Kazhdan host has no finite quotient to borrow from.
- **Open, no candidate known:** for one finitely generated simple nonsofic group, a representation of
  `CA(G;A)` into a directly finite ring that separates idempotent automata from `id` and uses no finite
  models.
