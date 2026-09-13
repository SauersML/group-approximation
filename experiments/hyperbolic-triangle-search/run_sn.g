# Complete search for homomorphisms of the four (A7,A7,A8) candidates into S_n.
# Driver prepends: NMIN := ..; NMAX := ..; CANDS := [..];
Read("tris_lib.g");
Read("cands.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
for k in CANDS do
  c := cands[k];
  VA := MakeVData(A7, c.A); VB := MakeVData(A7, c.B); VC := MakeVData(A8, c.C);
  TA := TransitiveTypes(VA, NMAX); TB := TransitiveTypes(VB, NMAX);
  for n in [NMIN..NMAX] do
    t0 := Runtime();
    res := SearchSn(VA, VB, VC, c.e, n, TA, TB);
    Print("CAND", k, " n=", n, " alphaSets=", Length(res.alphas), " stats=", res.stats,
          " homs=", Length(res.found), " ms=", Runtime() - t0, "\n");
  od;
od;
Print("RUN_SN_DONE\n");
QUIT;
