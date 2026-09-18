# Faster variant of monomial.g (same mathematics): the transversal of A is indexed by
# exponents w.r.t. a modulo pcgs of H mod A, and chi is evaluated linearly on a pcgs of A.
Read("reduce.g");
MonomialCertFast := function(R, p, outfile)
  local H, imgs, jimg, A, C, B, Z, b, gens, ords, N, c, chiInd, chiP, pcA, mpc, rel, T, n,
        idx, i, g, out, j, a, k, prm, ph, e, chi, strs;
  H := R[1]; imgs := R[2]; jimg := R[3];
  A := Centre(H);
  repeat
    C := Centralizer(H, A);
    if C = A then break; fi;
    B := NaturalHomomorphismByNormalSubgroupNC(H, A);
    Z := Intersection(Centre(Image(B)), Image(B, C));
    b := First(Pcgs(Z), z -> not IsOne(z));
    b := b^(Order(b)/p);
    b := PreImagesRepresentative(B, b);
    A := ClosureGroup(A, b);
  until false;
  Print("  |A|=", p, "^", Length(Factors(Size(A))), " abelian ", IsAbelian(A), " normal ",
        IsNormal(H, A), " selfcentralizing ", Centralizer(H, A) = A, " index ", Index(H, A), "\n");
  gens := IndependentGeneratorsOfAbelianGroup(A);
  ords := List(gens, Order);
  N := Exponent(A);
  chiInd := a -> Sum([1..Length(gens)], i -> c[i]*IndependentGeneratorExponents(A, a)[i]*(N/ords[i])) mod N;
  repeat
    c := List(ords, o -> Random([0..o-1]));
  until chiInd(jimg) mod (N/p) = 0 and chiInd(jimg) <> 0;
  pcA := Pcgs(A);
  chiP := List(pcA, chiInd);
  chi := a -> (ExponentsOfPcElement(pcA, a)*chiP) mod N;
  if chi(jimg) <> chiInd(jimg) then Error("chi mismatch"); fi;
  Print("  chi(J) = zeta_", N, "^", chi(jimg), "\n");
  mpc := ModuloPcgs(H, A);            # H mod A, relative orders all p
  n := p^Length(mpc);
  T := List(Tuples([0..p-1], Length(mpc)), ex -> Product([1..Length(mpc)], i -> mpc[i]^ex[i]));
  idx := function(h)  # index (1-based) of the transversal element in the coset A*h ... right coset t with h in A t
    local ex; ex := ExponentsOfPcElement(mpc, h);
    return Sum([1..Length(ex)], i -> ex[i]*p^(Length(ex)-i)) + 1;
  end;
  # sanity: idx(T[i]) = i
  if ForAny([1..Minimum(n, 50)], i -> idx(T[i]) <> i) then Error("transversal indexing"); fi;
  out := OutputTextFile(outfile, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, "{\"N\":", N, ",\"n\":", n, ",\"chiJ\":", chi(jimg), ",\"gens\":[");
  for k in [1..Length(imgs)] do
    g := imgs[k]; prm := []; ph := [];
    for i in [1..n] do
      j := idx(T[i]*g);
      a := T[i]*g*T[j]^-1;
      Add(prm, j-1); Add(ph, chi(a));
    od;
    AppendTo(out, "{\"perm\":[", JoinStringsWithSeparator(List(prm, String), ","),
             "],\"phase\":[", JoinStringsWithSeparator(List(ph, String), ","), "]}");
    if k < Length(imgs) then AppendTo(out, ","); fi;
    Print("  gen ", k, " done\n");
  od;
  AppendTo(out, "]}\n");
  CloseStream(out);
end;
