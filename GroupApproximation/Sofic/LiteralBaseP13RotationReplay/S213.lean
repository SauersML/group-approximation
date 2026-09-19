import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S213Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s213Image_eq_one :
    rotationWord (word (rotationSignedWord "YxyxzxzYXYZXYXyyxyZXyZXyx")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := s213Trace2
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
