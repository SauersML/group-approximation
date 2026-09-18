# gq-scott-union board (DONE for this run)
**Approach** (family: host geometry / obstruction). Signature: "glue affine self-similar hosts along the prime chain".
**Established:**
- `fg-groups-have-fg-derivative-images` (+ -proof): cocycle with finitely many values per generator lands in a f.g.
  subgroup; restricted to a stabilizer it is a homomorphism. e0cfca2b7.
- `fg-piecewise-linear-hosts-omit-natural-gl-n-q` (+ -proof): linear cocycles of f.g. groups have entries in a f.g.
  ring (never contains Q); divisible subgroups and SL_n(Q) have trivial derivative at fixed points; no f.g. host
  carries GL_n(Q), (Q,+), Aff(Q), PSL_2(Q) with natural derivative at a fixed point. e0cfca2b7.
- Root Attempt 2 (natural gluing of Scott/Zaremsky/adelic hosts dead). eb2adc008.
**Needs:** none.
**Dead:** natural gluing of the chain GL_n(Z[1/m!]) keeping the affine action (Scott Sc(n), Zaremsky affine hosts on
  Z_p^n, adelic V-type on A_f^n or ⊔_p Q_p^n) — never finitely generated.
**Sparks (not pursued):**
- Hölder conjugacy: BHM's Q <= T̄ acts freely on R, so it is conjugate/semiconjugate in Homeo(R) to a translation
  group by a copy of Q; the conjugated dilations give Aff(Q) in its normaliser. Are they piecewise PSL_2(Z)-lifts
  (Minkowski ?-function)? For gq-pp-lift / gq-q-in-germs.
- Contracting Röver–Nekrashevych V_d(G): germ sections eventually in the nucleus — a similar finiteness may kill Q
  in V_d(G) for contracting G. Unchecked.
