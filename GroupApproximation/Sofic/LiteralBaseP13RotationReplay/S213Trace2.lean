import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S213Trace1
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O13_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s213Trace2 :
    rotationWord (word (rotationSignedWord "YxyxzxzYXYZXYXyyxyZXyZXyx")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxyXZyXZxyxzYXy")) := s213Trace1
    _ = rotationWord (word (rotationSignedWord "YxyXZyXzxyxzYXy")) :=
      rotationStep "YxyXZyXZxyxzYXy" "YxyXZyXzxyxzYXy" "YxyXZyX" 2 true
    _ = rotationWord (word (rotationSignedWord "YxyXZXZxxzYXy")) :=
      rotationStep "YxyXZyXzxyxzYXy" "YxyXZXZxxzYXy" "YxyXZy" 5 false
    _ = rotationWord (word (rotationSignedWord "YxyzxxxzYXy")) :=
      rotationStep "YxyXZXZxxzYXy" "YxyzxxxzYXy" "YxyX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxyzzYXy")) :=
      rotationStep "YxyzxxxzYXy" "YxyzzYXy" "Yxyz" 0 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "YxyzzYXy" "" "Yxy" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
