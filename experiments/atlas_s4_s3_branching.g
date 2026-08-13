# Exact complex branching for the atlas S4 <- S3 hard extension.

G := SymmetricGroup(4);;
K := Stabilizer(G, 4);;

irrG := Irr(G);;
irrK := Irr(K);;

Print("group_orders=", [Size(G), Size(K)], "\n");
Print("S4_irrep_degrees=", List(irrG, chi -> chi[1]), "\n");
Print("S3_irrep_degrees=", List(irrK, chi -> chi[1]), "\n");
Print("restriction_rows_S4_to_S3=\n");

for chi in irrG do
  restricted := RestrictedClassFunction(chi, K);;
  multiplicities := [];;
  for psi in irrK do
    Add(multiplicities, ScalarProduct(restricted, psi));
  od;
  Print(multiplicities, "\n");
od;

regularS4 := Sum(irrG, chi -> chi[1] * chi);;
restrictedRegular := RestrictedClassFunction(regularS4, K);;
Print("restricted_regular_S4_multiplicities=",
      List(irrK, psi -> ScalarProduct(restrictedRegular, psi)), "\n");
Print("four_regular_S3_multiplicities=",
      List(irrK, psi -> 4 * psi[1]), "\n");
