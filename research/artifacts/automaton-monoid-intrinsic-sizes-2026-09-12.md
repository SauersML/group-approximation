# Intrinsic sizes on the automaton monoid: retract chains and self-similar retract posets

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
   `(sigma g tau)^2 = sigma g (tau sigma) g tau = sigma (e g) g tau = sigma g tau`. Its image is
   `sigma(g(tau(A^G)))`, and `g(tau(A^G)) = Y` because `g` fixes `Y` and `Y <= tau(A^G)`. So
   `sigma(Y)` is a retract image, and `tau(sigma(Y)) = e(Y) = Y`. The same computation inside `↓X`
   gives the general statement. []

**Corollary 2.2.** Let `I` be any invariant of posets carrying a conjugacy relation, and put
`d(X) = I(↓X)`. Then `d(A^G) = d(tau(A^G)) = d(tau^2(A^G)) = ...` for every strict `tau`. Every size
computed intrinsically from the retract lattice (dimension functions defined by the lattice, chain
heights, widths, lengths of maximal chains) takes equal values at the full shift and at a proper
retract whenever a strict automaton exists. Such a size separates `A^G` from its proper retracts only
on a group already known to be surjunctive, so it cannot be the input of a proof.

