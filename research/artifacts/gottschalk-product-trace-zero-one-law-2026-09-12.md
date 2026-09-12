# The product trace obeys a zero-one law on injective cellular automata

Lane `gk-observables`, 2026-09-12. Supports the Cairn claims
`bijective-ca-preserve-uniform-bernoulli-measure` and
`injective-ca-product-trace-zero-one-law`, and the route
`matrix-observable-extension-from-surjunctivity`.

The question for this lane was whether Kaplansky's characteristic-zero proof has
a nonlinear analogue: a faithful shift-invariant tracial state on an algebra of
observables of the full shift, compatible with the encoder, forcing a strict
isometry to be unitary. The answer recorded here is that every such trace-level
premise is a zero-one statement, equivalent to surjectivity automaton by
automaton. The quantitative content of the known proofs sits at logarithmic
scale, where a trace sees nothing.

## 1. Conventions

As in `gottschalk-quantum-compression-2026-09-07.md`: the action is
`(h.x)(g) = x(h^-1 g)`. The encoder `tau: A^G -> A^G` has memory `N` (the output at
`g` reads `gN`), a decoder `sigma` with `sigma tau = id` has memory `M`, and both
memories contain `e`. Write `X = A^G`, `mu` for the uniform product measure,
`Y = tau(X)` and `nu = tau_* mu`.

For a finite `F` and a permutation `pi` of `A^F`, the *local permutation* `pi`
is the homeomorphism of `X` that replaces `x|F` by `pi(x|F)` and fixes every
other coordinate.

With constant backgrounds `b` and `c = tau(b)`, let `C_b`, `C_c` be the finite
perturbations, `H_b = l^2(C_b)`, `H_c = l^2(C_c)`, `V|x> = |tau(x)>`, `P = VV*`,
and `Phi(O) = V* O V`. Let `A_G` be the quasilocal algebra on `H_c`, `D` its
diagonal subalgebra (multiplication operators `D_f`, `f` in `C(X)` depending on
finitely many coordinates, and their norm limits), and `tr` the product of the
normalized matrix traces. Then `tr(D_f) = int f dmu`. By Section 2 of the
compression artifact, `P` is the diagonal projection onto `Y ∩ C_c`,
`Phi(D_f) = D_(f o tau)`, and

    Phi(O*O) - Phi(O*)Phi(O) = V* O* (I - P) O V.              (C8)

**Fact 1.1.** A Borel probability measure `kappa` on `X` invariant under every
local permutation equals `mu`.

*Proof.* For patterns `p != q` on a finite `F`, the transposition of `p` and `q`
exchanges the cylinders `[p]` and `[q]`, so `kappa([p]) = kappa([q])`. Hence
`kappa([p]) = |A|^(-|F|)` for every cylinder. QED

## 2. Bijective automata preserve the uniform measure

**Theorem 1.** Let `G` be any group and `tau: A^G -> A^G` a bijective cellular
automaton. Then `tau_* mu = mu`.

*Proof.* The inverse `sigma = tau^-1` is a cellular automaton (Curtis--Hedlund--
Lyndon). Fix a local permutation `pi` on `F` and put `rho = sigma o pi o tau`, a
homeomorphism of `X`.

1. *`rho` moves only coordinates in `F M^-1`.* If `hM` misses `F`, then
   `pi(tau x)` and `tau x` agree on `hM`, so
   `rho(x)(h) = sigma(tau x)(h) = x(h)`.
2. *`rho` is read on a finite window.* For `h` in `F M^-1`, `rho(x)(h)` reads
   `pi(tau x)` on `hM`, which is inside `F M^-1 M`. That reads `tau x` on
   `F M^-1 M ∪ F`, which reads `x` on `E = (F M^-1 M ∪ F) N`. Since `e` lies in
   `M` and `N`, `E` contains `F M^-1`.
3. So `rho(x)|E = r(x|E)` for a map `r: A^E -> A^E` and `rho(x) = x` off `E`.
   If `r(q) = r(q')`, take `x, x'` agreeing off `E` with restrictions `q, q'`.
   Then `rho(x) = rho(x')`, so `q = q'`. Thus `r` is a bijection of the finite set
   `A^E`, and `rho` preserves `mu`.
4. For Borel `B`, bijectivity gives `tau^-1(pi B) = sigma(pi B) = rho(sigma B)`, so
   `tau_* mu(pi B) = mu(rho(tau^-1 B)) = mu(tau^-1 B) = tau_* mu(B)`.

By Fact 1.1, `tau_* mu = mu`. QED

No amenability is used. Over amenable groups this also follows from the
Garden-of-Eden theorem. No priority is claimed; the point here is only that it
holds over every group.

*Operator form, for countable `G`.* `V` is unitary, and Section 4 of the
compression artifact makes `Phi = Ad V*` a unital *-endomorphism of `A_G`
extending `f -> f o tau`. So `tr o Phi` is a tracial state, it equals `tr` by
uniqueness of the trace on the UHF algebra `A_G`, and restricting to `D` gives
`nu = mu`.

## 3. The zero-one law

**Theorem 2.** Let `G` be infinite and `tau: A^G -> A^G` injective.

(a) If `tau` is onto, then `nu = mu`, `P = I`, and `Phi` is a unital
    *-homomorphism of `A_G` with `tr o Phi = tr`.

(b) If `tau` is not onto, then `mu(Y) = 0` and `nu(Y) = 1`, so `nu` is singular
    to `mu`. Every state `omega` on `B(H_c)` with `omega = tr` on `A_G` has
    `omega(P) = 0`. The state `tr o Phi` restricts to `nu` on `D` and is not
    tracial.

(c) Consequently the following are equivalent:
    (i) `tau` is onto;
    (ii) `nu = mu`;
    (iii) `nu` is absolutely continuous with respect to `mu`;
    (iv) `nu` is not singular to `mu`;
    (v) `omega(P) > 0` for some state `omega` on `B(H_c)` extending `tr`;
    (vi) `omega(P) = 1` for every such state;
    (vii) `tr o Phi` is tracial on `A_G`;
    (viii) `Phi` is multiplicative on `A_G`;
    (ix) `P` commutes with `A_G`.

*Proof of (a).* Theorem 1 gives `nu = mu`. Section 2 of the compression artifact
gives `P = I`, and Section 4 gives the homomorphism; then `tr o Phi` is a trace
restricting to `mu` on `D`, and it equals `tr` (Section 2 operator form, or the
argument in (b) below).

*Proof of (b).*
1. *A Garden of Eden.* `Y` is a proper closed invariant set, so by compactness a
   pattern `p` on a finite `Omega` has `[p]` disjoint from `Y`.
2. *Disjoint translates.* Since `G` is infinite, choose `g_1, g_2, ...` with
   `g_(k+1)` outside the finite set `union_(i<=k) g_i Omega Omega^-1`. Then the
   sets `g_k Omega` are pairwise disjoint.
3. *Invariance.* Let `g.p` be the pattern on `g Omega` with `(g.p)(g w) = p(w)`.
   If `y` in `Y` carried `g.p` on `g Omega`, then `g^-1.y` would lie in `Y` and
   carry `p` on `Omega`. So `Y` misses every cylinder `[g_k.p]`.
4. *Measure.* By independence over disjoint windows,
   `mu(Y) <= (1 - |A|^(-|Omega|))^m` for every `m`, so `mu(Y) = 0`. Also
   `nu(Y) = mu(tau^-1 Y) = 1`.
5. *Range projection.* Let `e_k` in `A_G` be the diagonal projection onto the
   configurations carrying `g_k.p` on `g_k Omega`. By step 3, `P e_k = 0`. The
   `e_k` commute with each other and with `P`, so
   `P <= prod_(k<=m) (I - e_k)`. For any state `omega` extending `tr`, positivity
   and the product form of `tr` give
   `omega(P) <= tr(prod_(k<=m)(I - e_k)) = (1 - |A|^(-|Omega|))^m`, hence
   `omega(P) = 0`.
6. *`tr o Phi`.* On `D`, `tr(Phi(D_f)) = int f o tau dmu = int f dnu`. Suppose
   `tr o Phi` were tracial. For a local permutation `pi` let `u_pi` in `A_G` be the
   corresponding permutation unitary, so `u_pi D_f u_pi* = D_(f o pi^-1)`. The trace
   property makes the restriction of `tr o Phi` to `D` invariant under every
   local permutation, so it equals `mu` by Fact 1.1. Then `nu = mu`, contradicting
   step 4. This needs no uniqueness theorem and works for uncountable `G`.

*Proof of (c).*
- (i) => (ii): Theorem 1. (ii) => (iii) => (iv): trivial. (iv) => (i): by (b).
- (i) => (vi): `P = I`. (vi) => (v): extensions exist, since `tr` is a state on
  the C*-subalgebra `A_G` and states extend to `B(H_c)`. (v) => (i): by (b).
- (i) => (viii): part (a). (viii) => (vii): a unital *-homomorphism composed with
  a trace is a trace. (vii) => (i): by (b).
- (viii) <=> (ix): by (C8), `Phi(O*O) = Phi(O*)Phi(O)` exactly when
  `(I - P) O V = 0`, that is `(I - P) O P = 0`. Applying this to `O` and `O*`, the
  multiplicative domain of `Phi` is `A_G ∩ {P}'`. So `Phi` is multiplicative on
  `A_G` exactly when `P` commutes with `A_G`.
- (ix) <=> (i): `A_G` acts irreducibly on `H_c`, because a finite-region matrix
  unit sends any basis configuration to any other that differs from it on that
  region. So `P` commutes with `A_G` only if `P` is `0` or `I`. `P != 0` because
  `V` is an isometry, so (ix) says `P = I`, which is (i). QED

On the multiplicative domain `A_G ∩ {P}'`, `tr o Phi` is a tracial state
extending `nu`. That is the operator-algebraic shadow of the uniform Gibbs
structure of the image measure recorded in
`gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md`.

## 4. What this does to the tracial route

1. **The matrix-observable route is a restatement.** The route
   `gottschalk-via-matrix-observable-extension` is valid, but its open
   prerequisite `injective-ca-pullbacks-extend-to-matrix-observables` is
   equivalent to its target. Section 5 of the compression artifact gives
   extension => onto for each injective automaton, and Section 4 gives
   onto => extension. The converse half is now the route
   `matrix-observable-extension-from-surjunctivity`, and the resulting cycle is
   the house encoding of an equivalence.

2. **Every trace-level weakening is a restatement too.** Theorem 2(c) covers
   tracial compatibility of the compression, positivity of the range projection
   under any product-trace extension, multiplicativity on any subalgebra that
   is irreducible on `H_c`, and absolute continuity of the image measure. For
   each automaton each is a zero-one statement equivalent to surjectivity. No
   trace inequality can serve as an intermediate step, because in the strict
   case every such quantity is exactly `0` and in the onto case exactly `1`.

3. **Scale.** The Gromov--Weiss count compares, on a model with `n` sites, an
   image of size `|A|^(n(1 - o(1)))` with the Garden-of-Eden bound
   `|A|^n (1 - |A|^(-|Omega|))^(cn)`. As normalized traces both tend to `0`, and
   the contradiction appears only after taking `(1/n) log`. The infinite product
   trace sends both to `0` (Theorem 2(b), step 5).

   The same collapse happens over `Z`, in Myhill's count on a finite window `F`.
   Injectivity gives at least `|A|^(|F| - |dF|)` distinct output patterns on `F`,
   where `dF` is a memory boundary layer, and the Garden of Eden gives at most
   `|A|^|F| (1 - |A|^(-|Omega|))^(m(F))`, with `m(F)` the number of disjoint
   translates of `Omega` inside `F`. Normalized by `|A|^|F|` these are
   `|A|^(-|dF|)` and `(1 - |A|^(-|Omega|))^(m(F))`. Along a Følner sequence both
   tend to `0`: `|dF| -> infinity` although `|dF|/|F| -> 0`. They conflict only
   after `(1/|F|) log`, which is where Myhill's argument lives.

4. **The square hypothesis enters only logarithmically.** Rectangular sections
   `B^G -> A^G` with `|B| < |A|` (for example a pointwise inclusion of alphabets)
   satisfy every structural statement in parts 1--3 of the compression
   artifact's theorem and are never onto. An argument that cannot tell `|B|` from
   `|A|` at per-site logarithmic precision therefore cannot prove Gottschalk.
   The nonlinear analogue of the von Neumann dimension in Kaplansky's
   characteristic-zero theorem is entropy per site, not a trace.

5. **Where entropy arguments plug in.** A strict encoder is an isomorphism of
   p.m.p. `G`-systems from `(X, mu)` onto `(A^G, nu)`, with `nu` carried by a proper
   subshift and singular to `mu` (Theorem 2(b)). This is the input Seward-type
   arguments consume; see `every-group-has-positive-rokhlin-entropy-action`, from
   which Seward's Krieger II derives surjunctivity.

6. **Linearization in characteristic zero.** Put `V_0` for the mean-zero
   functions on `A` and `W_S = ⊗_(g in S) V_0`. The local functions decompose as
   `D_loc = ⊕_(finite S) W_S = C ⊕ ⊕_([S]) Ind_(K_S)^G W_S`, over `G`-orbits of
   nonempty finite `S` with finite setwise stabilizers `K_S`. So `D_loc` is a
   projective `C[G]`-module that is not finitely generated. The pullback `tau*`
   is a surjective equivariant module map that is not injective when `tau` is
   strict. It sends the finitely generated projective submodule `D^(R)` (the
   `W_S` with `S` inside a translate of the ball `B_R`) only into `D^(R+r)`,
   `r` the memory radius. Stable finiteness of `C[G]` concerns endomorphisms of
   finitely generated projective modules, and the radius growth is exactly where
   a Følner condition would be needed.

## 5. What is not claimed

Nothing here decides Gottschalk's conjecture or any specific group. Theorem 1
and Theorem 2 are elementary. The contribution is to close the trace-level
family of premises and to locate the missing mechanism at logarithmic scale.
