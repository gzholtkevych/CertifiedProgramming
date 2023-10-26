Module Type SIG.
  Parameter X : Set.
  Parameter x : X.
  Definition y := true.
End SIG.

Module nat_SIG_Opaque : SIG.
  Definition X := nat.
  Definition x := 3.
  Definition y := false.
Fail End nat_SIG_Opaque.

Module nat_SIG_Opaque : SIG.
  Definition X := nat.
  Definition x := 3.
  Definition y := true.
End nat_SIG_Opaque.

Print nat_SIG_Opaque.X.
Print nat_SIG_Opaque.x.
Print nat_SIG_Opaque.y.

Import nat_SIG_Opaque.
Print X.
Print x.
Print y.

Module nat_SIG_Transparent <: SIG.
  Definition X := nat.
  Definition x := 3.
  Definition y := true.
End nat_SIG_Transparent.

Print nat_SIG_Transparent.X.
Print nat_SIG_Transparent.x.
Print nat_SIG_Transparent.y.

Import nat_SIG_Transparent.
Print X.
Print x.
Print y.