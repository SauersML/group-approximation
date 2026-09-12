import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeZTrace2
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_31

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeZTrace3 :
    rotationWord (word (rotationSignedWord "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ")) =
      rotationWord (word (rotationSignedWord "YxzXYZYZXZxY")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYxyxzxxzyXyxyZXZxY")) := rangeZTrace2
    _ = rotationWord (word (rotationSignedWord "YxzYxyxzXzyXyxyZXZxY")) :=
      rotationStep "YxzYxyxzxxzyXyxyZXZxY" "YxzYxyxzXzyXyxyZXZxY" "YxzYxyxz" 0 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyxZXzyXyxyZXZxY")) :=
      rotationStep "YxzYxyxzXzyXyxyZXZxY" "YxzYxyxZXzyXyxyZXZxY" "YxzYxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyxZXZyXyxyZXZxY")) :=
      rotationStep "YxzYxyxZXzyXyxyZXZxY" "YxzYxyxZXZyXyxyZXZxY" "YxzYxyxZX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyxxzxyXyxyZXZxY")) :=
      rotationStep "YxzYxyxZXZyXyxyZXZxY" "YxzYxyxxzxyXyxyZXZxY" "YxzYxyx" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyXzxyXyxyZXZxY")) :=
      rotationStep "YxzYxyxxzxyXyxyZXZxY" "YxzYxyXzxyXyxyZXZxY" "YxzYxy" 0 false
    _ = rotationWord (word (rotationSignedWord "YxzYZyxyZXZxY")) :=
      rotationStep "YxzYxyXzxyXyxyZXZxY" "YxzYZyxyZXZxY" "YxzYxy" 5 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxyZXZxY")) :=
      rotationStep "YxzYZyxyZXZxY" "YxzYzyxyZXZxY" "YxzY" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzXYZyyZXZxY")) :=
      rotationStep "YxzYzyxyZXZxY" "YxzXYZyyZXZxY" "Yxz" 6 false
    _ = rotationWord (word (rotationSignedWord "YxzXYZYZXZxY")) :=
      rotationStep "YxzXYZyyZXZxY" "YxzXYZYZXZxY" "YxzXYZ" 1 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
