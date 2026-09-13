# Finite targets as permutation groups (shared by run_amb.g-style drivers).
PermOf := function(G)
  return Image(SmallerDegreePermutationRepresentation(Image(IsomorphismPermGroup(G))));
end;
MakeTarget := function(name)
  if name = "Sp6_2" then return PermOf(Sp(6,2));
  elif name = "L5_2" then return PermOf(SL(5,2));
  elif name = "L6_2" then return PermOf(SL(6,2));
  elif name = "L4_4" then return PSL(4,4);
  elif name = "O8p2" then return PermOf(Omega(1,8,2));
  elif name = "O8m2" then return PermOf(Omega(-1,8,2));
  elif name = "Sp8_2" then return PermOf(Sp(8,2));
  elif name = "A9" then return AlternatingGroup(9);
  fi;
  Error("unknown target");
end;
