
## 2. The shared-prime case: what the averaging step cannot be replaced by

Throughout this section a prime `p` divides both `m` and `|H|`.

**Lemma 2 (no retraction commutes with constants).** Give `A` any group structure, written
multiplicatively. No automaton `Q : X -> X` with image inside `Y` satisfies `Q(z c) = Q(z) c` for every
configuration `z` and every constant configuration `c`.

*Proof.*
1. By Cauchy, `H` has an element `h` of order `p`, and `A` has an element `a` of order `p`.
2. Let `mu` be a rule of `Q` with memory `F`, so `Q(z)(k) = mu((z(kf))_(f in F))`. Put `F' = <h> F` and let
   `mu'` ignore the added coordinates. Then `hF' = F'`, and `f -> hf` permutes `F'` with every orbit of
   size `p`, since `hf = f` forces `h = 1`.
3. Output in `Y` means `Q(z)(kh) = Q(z)(k)`, that is,
   `mu'((z(khf))_(f in F')) = mu'((z(kf))_(f in F'))` for all `z` and `k`.
4. Fix `k`. Choose a transversal `R` of the `<h>`-orbits on `F'`. Put `z(k h^i r) = a^i` for `r in R` and
   `0 <= i < p`, and any value elsewhere. The sites `k h^i r` are distinct, and `h^p = 1 = a^p`, so `z` is
   well defined.
5. Then `z(khf) = z(kf) a` for every `f in F'`. So the window at `kh` is the window at `k` multiplied
   pointwise by the constant `a`.
6. Step 3 and equivariance under constants give `mu'(w) = mu'(w a) = mu'(w) a`, where `w` is the window at
   `k`. That forces `a = 1`, a contradiction. QED

**Corollary 3 (the splitting property fails).** Let `A` be abelian. No automaton `Q` with image in `Y`
satisfies `Q(y w) = y` for all `y in Y` and all `w` in `{z (Qz)^(-1) : z in X}`.

*Proof.* For any `z` and constant `c`, `(Qz) c` lies in `Y`, and `zc = ((Qz) c)(z (Qz)^(-1))` pointwise.
So `Q(zc) = (Qz) c`, which Lemma 2 forbids. QED

Steps 3 to 6 of Theorem 1 use only three properties of `P`: its image is `Y`, it fixes `Y`, and it has this
splitting property. Those are what make `Phi(z) = tau(Pz)(z (Pz)^(-1))` work for every `tau` at once. So at
a shared prime the extension has to depend on `tau`, or has to leave the shape "new base times old fibre
coordinate". The nonabelian case of Corollary 3 is not claimed.

**Min retraction (heuristic).** For an ordered alphabet `{0 < 1 < ... < m-1}`, the automaton
`rho(z)(k) = min_(h in H) z(kh)` has image `Y` and fixes `Y`. But the block fibre over base symbol `b`
has `(m - b)^|H| - (m - b - 1)^|H|` points. That depends on `b`, so no blockwise bijection moves the fibre
coordinate from base `b` to base `tau(rho z)(k)`. This rules out blockwise gauges only. Rules that also read
neighbouring blocks are not excluded by this count; Lemma 2 excludes the constant-equivariant ones.

**Amenable hosts (standard, not landed as a claim).**
- `Y` is a subshift of finite type: its forbidden patterns are two-cell patterns on `{k, kh}`.
- `Y` is strongly irreducible: patterns on `F_1` and `F_2` with `F_1 H ∩ F_2 H` empty glue.
- `tau(Y)` is a closed invariant subshift conjugate to `Y`, so it has the same topological entropy.
- Over an amenable group a strongly irreducible subshift has no proper subshift of full entropy
  (Ceccherini-Silberstein–Coornaert, strongly irreducible Garden of Eden theory; citation not re-read).

So `tau(Y) = Y` at every `m`, and the claim holds for amenable `G` with no coprimality. On a nonamenable
host nothing like this is available. The shared-prime case is where a finite-stabilizer coset shift might
carry strictness its host does not.
