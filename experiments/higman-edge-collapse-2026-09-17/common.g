F := FreeGroup("a","b","c","d");; a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;;
rels := [ b^a*b^-2, c^b*c^-2, d^c*d^-2, a^d*a^-2 ];;
z := Comm(a,c);;
# Collapse certificate: index of H=<a,c> in G is 1 => G = image of <a,c>, which is
# nilpotent/solvable by the added relators; G perfect (Higman quotient) => G trivial.
RunTest := function(name, extra, sub, lim)
  local T;
  T := CosetTableFromGensAndRels(GeneratorsOfGroup(F), Concatenation(rels, extra), sub : max := lim, silent := true);
  if T = fail then Print(name, " : FAIL(limit ", lim, ")\n");
  else Print(name, " : index ", Length(T[1]), "\n"); fi;
end;;
