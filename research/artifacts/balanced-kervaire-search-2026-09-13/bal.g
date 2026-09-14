# Deficiency-zero Kervaire filter: classify G = <x, y | r1, r2> (H_1 = 0 already).
# Verdicts, each exact:
#   TRIVIAL n=1      coset enumeration over the trivial subgroup closes with 1 coset.
#   FINITE n=<n>     it closes with n > 1 cosets: G is finite of order n.
#   QUOTIENT idx=<k> a proper subgroup of index k <= MAXIDX exists (LowIndexSubgroups),
#                    so G acts nontrivially on its cosets: a nontrivial finite quotient.
#   SIMPLE q=<name>  an epimorphism onto the named finite simple group exists.
#   OPEN             none of the above within the budgets.
# Reads BAL_IN lines "<id> <L> <r1> <r2>" and appends "<id> <L> <r1> <r2> <verdict>" to BAL_OUT.

F := FreeGroup("x", "y");;
x := F.1;; y := F.2;;
Lt := rec(x := x, X := x^-1, y := y, Y := y^-1);;
W := function(s) local w, ch;
  w := One(F);
  for ch in s do w := w * Lt.(String([ch])); od;
  return w;
end;;

TARGETS := [ ["PSL(2,7)", PSL(2,7)], ["PSL(2,8)", PSL(2,8)], ["PSL(2,11)", PSL(2,11)],
  ["PSL(2,13)", PSL(2,13)], ["PSL(2,16)", PSL(2,16)], ["PSL(2,17)", PSL(2,17)],
  ["PSL(2,19)", PSL(2,19)], ["A6", AlternatingGroup(6)], ["A7", AlternatingGroup(7)],
  ["PSL(2,23)", PSL(2,23)], ["PSL(2,25)", PSL(2,25)], ["PSL(3,3)", PSL(3,3)],
  ["PSU(3,3)", PSU(3,3)], ["M11", MathieuGroup(11)], ["A8", AlternatingGroup(8)] ];;

Classify := function(r1, r2, maxc, maxidx) local rels, tab, G, L, k, t, e;
  rels := [W(r1), W(r2)];
  tab := CosetTableFromGensAndRels([x, y], rels, [] : max := maxc, silent := true);
  if tab <> fail then
    if Length(tab[1]) = 1 then return "TRIVIAL n=1"; fi;
    return Concatenation("FINITE n=", String(Length(tab[1])));
  fi;
  G := F / rels;
  L := LowIndexSubgroupsFpGroup(G, maxidx);
  for k in L do
    if Index(G, k) > 1 then return Concatenation("QUOTIENT idx=", String(Index(G, k))); fi;
  od;
  for t in TARGETS do
    e := GQuotients(G, t[2]);
    if Length(e) > 0 then return Concatenation("SIMPLE q=", t[1]); fi;
  od;
  return "OPEN";
end;;

RunBal := function(inpath, outpath, maxc, maxidx) local lines, ln, p, v, t0;
  lines := SplitString(StringFile(inpath), "\n");
  for ln in lines do
    if ln = "" then continue; fi;
    p := SplitString(ln, " ");
    t0 := Runtime();
    v := Classify(p[3], p[4], maxc, maxidx);
    AppendTo(outpath, p[1], " ", p[2], " ", p[3], " ", p[4], " ", v, " ms=", Runtime() - t0, "\n");
  od;
end;;
