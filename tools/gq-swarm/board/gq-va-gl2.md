# gq-va-gl2 board
**Approach** (germ-host obstruction; sig "length functions along attractors and wandering singularities"): n = 2 in
finite germ extensions of V. DONE for this pass.
**Established** (8fc27465a, lane proof, not independently reviewed):
- regular-germ-extension-attractors-are-undistorted (+ -proof): s(g) = |sing g| is a length function in ANY finite
  germ extension of V, linear along wandering orbits with non-V total germ; in the REGULAR regime ((E) singular points
  eventually periodic, (H3) (V)_p normal or finite index, (T) g(p) in V.p) Lip(g) = sup |depth gain| is a length
  function, linear along attracting/repelling periodic points. => such elements undistorted, never conjugate to a^k
  (|k|>=2), never a Heisenberg centre. Corollary: the divisible line of Aff(Q)/SL_2(Q)/GL_2(Q)/U_3(Q) avoids both.
- Root Attempt 17 (3667dbcd3).
**Open (landed)**: regular-germ-extensions-have-no-bs-relations — remaining type: germs centralizing sigma_p with
  depth gain 0 (explicit infinite-order example in the node: skew product over an element of V(1C)).
**Needs**: a third invariant (asymptotic level-drift rate along annulus-map orbits) to kill the remaining type.
**Dead**: BS(1,n) in VA — subsumed by O4 (Burillo–Felipe). Arbitrary finite germ extensions obstruct nothing
  (shell E_nu embeds any countable group, incl. GL_2(Q) inside a 2-generator group): only fp is at stake.
**Sparks**: calibration T3 as stated ("any finite germ extension with an element conjugate to its square") is YES
  trivially via shell E_nu(BS(1,2)); restrict to fp or to the regular regime.
