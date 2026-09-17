# Build an exact monomial representation of the reduced quotient H in which J acts
# by the scalar omega = exp(2 pi i/3): induce a linear character chi of a
# self-centralizing abelian normal subgroup A with chi(J) primitive.
Read("reduce.g");
MonomialCert := function(R, p, outfile)
  local H, imgs, jimg, A, C, B, Z, b, gens, ords, N, c, chi, e, T, n, i, g, out, j, a, k, tries, ph, prm;
  H := R[1]; imgs := R[2]; jimg := R[3];
  A := Centre(H);
  repeat
    C := Centralizer(H, A);
    if C = A then break; fi;
    # an element of C/A central in H/A of order p
    B := NaturalHomomorphismByNormalSubgroupNC(H, A);
    Z := Intersection(Centre(Image(B)), Image(B, C));
    b := First(Pcgs(Z), z -> not IsOne(z));
    b := b^(Order(b)/p);
    b := PreImagesRepresentative(B, b);   # lies in C since A <= C
    A := ClosureGroup(A, b);
  until false;
  Print("  |A|=", p, "^", Length(Factors(Size(A))), " abelian ", IsAbelian(A), " normal ", IsNormal(H, A), " index ", Index(H, A), "\n");
  gens := IndependentGeneratorsOfAbelianGroup(A);
  ords := List(gens, Order);
  N := Exponent(A);
  e := IndependentGeneratorExponents(A, jimg);
  tries := 0;
  repeat
    c := List(ords, o -> Random([0..o-1]));
    chi := a -> Sum([1..Length(gens)], i -> c[i]*IndependentGeneratorExponents(A, a)[i]*(N/ords[i])) mod N;
    tries := tries + 1;
  until chi(jimg) mod (N/p) = 0 and chi(jimg) <> 0;
  Print("  chi(J) = zeta_", N, "^", chi(jimg), "\n");
  T := RightTransversal(H, A); n := Length(T);
  out := OutputTextFile(outfile, false); SetPrintFormattingStatus(out, false);
  PrintTo(out, "{\"N\":", N, ",\"n\":", n, ",\"chiJ\":", chi(jimg), ",\"gens\":[");
  for k in [1..Length(imgs)] do
    g := imgs[k]; prm := []; ph := [];
    for i in [1..n] do
      j := PositionCanonical(T, T[i]*g);
      a := T[i]*g*T[j]^-1;
      Add(prm, j-1); Add(ph, chi(a));
    od;
    AppendTo(out, "{\"perm\":", prm, ",\"phase\":", ph, "}");
    if k < Length(imgs) then AppendTo(out, ","); fi;
  od;
  AppendTo(out, "]}\n");
  CloseStream(out);
end;
