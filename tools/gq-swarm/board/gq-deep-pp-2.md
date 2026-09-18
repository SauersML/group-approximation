# gq-deep-pp-2 board (piecewise-projective, second deep lane) — DONE
**Approach.** Family: host geometry / obstruction. Signature: "Witte kills all one-dimensional hosts, nonstandard copies included".
**Established (5a140f21e, lane-proved, not refereed).**
- `gl-n-q-hosts-cannot-act-on-one-manifolds` (+ `-proof`): no group acting faithfully on a 1-manifold with finitely many
  components contains ANY copy of GL_n(Q), SL_n(Q), GL_n(Z), SL_n(Z), n >= 3 (F, T, T-bar, Stein, Lodha-Moore, Monod H(A),
  PL/projective circle groups, Homeo(S^1)); line/interval groups contain no SL_2(Z), SL_2(Q), GL_2(Q) (order-3 torsion).
- `sl-n-z-circle-actions-factor-through-finite-groups` (+ `-citation`): Witte, Proc AMS 122 (1994) — primary PDF was 403,
  quoted from Parwani arXiv:math/0504189v1; a reviewer with access should confirm.
- artifact `gq-deep-pp-2-scope.md`: family C scoping; lemma: p-adic odometer has no roots in clopen-piecewise PGL_2(Z[1/p]).
**Needs.** A nonstandard divisibility mechanism inside a Cantor-set or >=2-dim host containing SL_3(Z).
**Dead.** Family C in dimension one for n >= 3 (all copies); line/interval hosts for n = 2; standard p-adic/adelic copies (4a58a2b5b).
**Sparks.** n = 2 circle rigidity for SL_2(Z[1/p]) (Burger-Monod / Bader-Furman-Shaker), statement unchecked.
