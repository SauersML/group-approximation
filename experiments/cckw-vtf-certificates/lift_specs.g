# lift_specs.g -- lane hl-hyperbolic-rf-2, 2026-09-14. Groups whose listed simple quotients leave only a
# central kernel of order 2 or 3 on some vertex group (gq_vtf.g results), with quasisimple covers of those
# quotients to try in lift_vtf.g.
M := function(e) return rec(name := e, kind := "matrix", expr := e); end;
SPIN := function(n) return rec(name := Concatenation("2.A", String(n)), kind := "spin", n := n, p := 3); end;
LIFTSPECS := [
  rec(infile := "cckw334_q.g", name := "G_0^{14,14,48}", tag := "g0_14_14_48", covers := [M("SL(2,7)"), SPIN(7)]),
  rec(infile := "cckw334_q.g", name := "G_1^{14,14,48}", tag := "g1_14_14_48", covers := [M("SL(2,7)"), M("SL(3,4)")]),
  rec(infile := "cckw334_q.g", name := "G_5^{14,14,48}", tag := "g5_14_14_48", covers := [SPIN(8), M("SL(3,4)")]),
  rec(infile := "cckw334_q.g", name := "G_0^{14,16,40}", tag := "g0_14_16_40", covers := [M("SL(2,49)")]),
  rec(infile := "cckw334_q.g", name := "G_1^{14,16,48}", tag := "g1_14_16_48", covers := [M("SL(2,7)")]),
  rec(infile := "cckw334_q.g", name := "G_0^{16,26,48}", tag := "g0_16_26_48", covers := [M("SL(2,13)")]),
  rec(infile := "cckw334_q.g", name := "G_0^{16,18,54}", tag := "g0_16_18_54", covers := [M("SU(3,8)")]),
  rec(infile := "cckw334_q.g", name := "G_2^{16,18,54}", tag := "g2_16_18_54", covers := [M("SU(3,8)")]),
  rec(infile := "cckw334_q.g", name := "G_0^{24,26,48}", tag := "g0_24_26_48", covers := [M("SL(2,13)"), M("SL(4,3)")]),
  rec(infile := "cckw334_q.g", name := "G_5^{26,26,48}", tag := "g5_26_26_48", covers := [M("SL(2,13)"), M("SL(4,3)")]),
  rec(infile := "cckw344_q.g", name := "G_0^{14,40,48}", tag := "g0_14_40_48", covers := [M("SL(2,49)"), SPIN(7)]),
  rec(infile := "cckw334_q.g", name := "G_0^{16,26,40}", tag := "g0_16_26_40", covers := [M("SL(2,169)")]),
  rec(infile := "cckw344_q.g", name := "G_0^{26,40,48}", tag := "g0_26_40_48", covers := [M("SL(2,169)")]),
];
