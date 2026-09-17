# For a vertex group H with two edge generators g1, g2 of prime orders p1, p2,
# print one line per conjugacy class of subgroups U:
#   index  classlength  c1  c2
# where c_i = number of p_i-cycles of g_i acting on the cosets H/U.
VertexData := function(name, H, g1, p1, g2, p2)
  local cls, cl, U, k, fix, out, g, p, cs, i;
  cls := ConjugacyClassesSubgroups(H);
  PrintTo(Concatenation(name, ".dat"), "");
  for cl in cls do
    U := Representative(cl);
    k := Index(H, U);
    cs := [];
    for i in [1,2] do
      g := [g1, g2][i]; p := [p1, p2][i];
      fix := Size(Centralizer(H, g)) *
             Number(Elements(ConjugacyClass(H, g)), x -> x in U) / Size(U);
      Add(cs, (k - fix) / p);
    od;
    AppendTo(Concatenation(name, ".dat"), k, " ", Size(cl), " ", cs[1], " ", cs[2], "\n");
  od;
end;

# A_7 and A_8 with 7-element edge generators (the fixed-point count of a
# 7-element is the same for both A_7-classes of 7-elements, by rationality of
# permutation characters, so any two 7-elements give the same data).
# Work in the action on 2-subsets, to avoid the natural-alternating-group
# normalizer code path (it needs the TransitiveGroups library, absent here).
Pairs := function(n, gens)
  local hom;
  hom := ActionHomomorphism(AlternatingGroup(n), Combinations([1..n], 2), OnSets);
  return Concatenation([Image(hom)], List(gens, g -> Image(hom, g)));
end;
t := Pairs(7, [(1,2,3,4,5,6,7), (1,3,5,7,2,4,6)]);
VertexData("A7", t[1], t[2], 7, t[3], 7);
t := Pairs(8, [(1,2,3,4,5,6,7), (2,3,4,5,6,7,8)]);
VertexData("A8", t[1], t[2], 7, t[3], 7);

# Coxeter triangle calibration: dihedral vertex groups D_m = <a,b | a^2,b^2,(ab)^m>
Dih := function(m)
  local a, b;
  a := PermList(List([0..m-1], i -> ((-i) mod m) + 1));
  b := PermList(List([0..m-1], i -> ((1 - i) mod m) + 1));
  return [Group(a, b), a, b];
end;
for m in [2, 3, 4, 7] do
  d := Dih(m);
  if m = 2 then
    # D_2 acting on 2 points is not faithful; use the Klein group directly
    d := [Group((1,2),(3,4)), (1,2), (3,4)];
  fi;
  VertexData(Concatenation("D", String(m)), d[1], d[2], 2, d[3], 2);
od;
QUIT;
