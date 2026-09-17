OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("monomial.g");
R := ReduceAndVerify("Heawood", 14, heawood, 3, 3);
MonomialCert(R, 3, "heawood_p3_monomial.json");
QUIT;
