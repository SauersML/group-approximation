import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_23Trace3 :
    rotationWord (word (rotationSignedWord "YxyxzXYxzYZXYXyyZXyx")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "yyy")) := o21_23Trace2
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "yyy" "" "" 1 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
