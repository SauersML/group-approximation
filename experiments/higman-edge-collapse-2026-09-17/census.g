# Census: for short nontrivial words r in the free subgroup <a,c> of Higman's group H4,
# test whether H4/<<r>> is trivial by coset enumeration of the cyclic subgroup <a>.
# Index 1 means Q = <a> is cyclic; Q is perfect (quotient of the perfect H4), so Q = 1.
F := FreeGroup("a","b","c","d");; a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;;
rels := [ b^a*b^-2, c^b*c^-2, d^c*d^-2, a^d*a^-2 ];;
maxlen := MAXLEN;;

letters := [a, a^-1, c, c^-1];;
words := [ ];;
Canon := function(w)   # canonical representative under cyclic shift, inversion, swap a<->c
  local L, reps, v, i, e, sw, all;
  L := LetterRepAssocWord(w);
  all := [];
  for sw in [false, true] do
    for e in [1, -1] do
      v := L;
      if e = -1 then v := Reversed(List(v, x -> -x)); fi;
      if sw then v := List(v, function(x) if AbsInt(x) = 1 then return SignInt(x)*3; elif AbsInt(x)=3 then return SignInt(x)*1; else return x; fi; end); fi;
      for i in [0..Length(v)-1] do
        Add(all, Concatenation(v{[i+1..Length(v)]}, v{[1..i]}));
      od;
    od;
  od;
  return Minimum(all);
end;;
CycRed := function(L) local n; n := Length(L); return n = 0 or L[1] <> -L[n]; end;;
Rec := function(prefix, len)
  local x, L;
  if len = 0 then
    L := LetterRepAssocWord(prefix);
    if Length(L) > 0 and CycRed(L) then Add(words, Canon(prefix)); fi;
    return;
  fi;
  for x in letters do
    L := LetterRepAssocWord(prefix*x);
    if Length(L) = Length(LetterRepAssocWord(prefix)) + 1 then Rec(prefix*x, len-1); fi;
  od;
end;;
for n in [1..maxlen] do Rec(One(F), n); od;
words := Set(words);;
# drop proper powers of shorter words only if listed (keep all; cheap)
Print("# ", Length(words), " canonical cyclically reduced words of length <= ", maxlen, "\n");
lim := LIMIT;;
for L in words do
  r := AssocWordByLetterRep(FamilyObj(a), L);
  G := F/Concatenation(rels, [r]);;
  res := CALL_WITH_CATCH(function() return Index(G, Subgroup(G, [G.1]) : max := lim, silent := true); end, []);
  if res[1] = true and res[2] <> fail then
    Print(r, " : index(<a>) = ", res[2], "\n");
  else
    Print(r, " : UNDECIDED (limit ", lim, ")\n");
  fi;
od;
QUIT;
