import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_31Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_31Trace3 :
    rotationWord (word (rotationSignedWord "YxyxzxYxzYxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "Yxzxzxzy")) := o21_31Trace2
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "Yxzxzxzy" "" "Y" 3 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
