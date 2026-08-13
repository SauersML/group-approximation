import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S321Trace3

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s321Trace4 :
    rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyZxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzXYXYYzyyX")) := s321Trace3
    _ = rotationWord (word (rotationSignedWord "YxzXYXyzyyX")) :=
      rotationStep "YxzXYXYYzyyX" "YxzXYXyzyyX" "YxzXYX" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzXYXZYZyX")) :=
      rotationStep "YxzXYXyzyyX" "YxzXYXZYZyX" "YxzXYX" 4 false
    _ = rotationWord (word (rotationSignedWord "YxzXYXZxYzy")) :=
      rotationStep "YxzXYXZYZyX" "YxzXYXZxYzy" "YxzXYXZx" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzXXzxzy")) :=
      rotationStep "YxzXYXZxYzy" "YxzXXzxzy" "YxzX" 5 true
    _ = rotationWord (word (rotationSignedWord "Yxzxzxzy")) :=
      rotationStep "YxzXXzxzy" "Yxzxzxzy" "Yxz" 0 true
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "Yxzxzxzy" "" "Y" 3 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
