{ best=1e9; if($7!="None") best=2*$7+2; if($8!="None" && $8<best) best=$8;
  k=($5<=2.0)?"<=2.0":(($5<=2.5)?"<=2.5":"<=3.0"); if(best>mx[k]){mx[k]=best; arg[k]=$0} }
END{for(k in mx) print k, mx[k], arg[k]}
