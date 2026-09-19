{ best=1e9; if($7!="None") best=2*$7+2; if($8!="None" && $8<best) best=$8;
  if(best==1e9){fail++; print "FAIL",$0; next}
  r=best/$5; if(r>mx){mx=r; arg=$0} }
END{print "classes",NR,"fail",fail+0,"max ratio",mx; print arg}
