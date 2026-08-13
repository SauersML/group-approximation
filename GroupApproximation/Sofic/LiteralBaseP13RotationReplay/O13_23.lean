import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O13_23Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o13_23Image_eq_one :
    rotationWord (word (rotationSignedWord "xzYXYXYxzxyZXyZXyx")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := o13_23Trace1
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
