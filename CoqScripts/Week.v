Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Check day.

Definition next_working_day (d: day): day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | _ => monday
  end.

Eval compute in next_working_day wednesday.
Eval compute in next_working_day friday.

Inductive Weekend: day -> Prop:=
  | firstWeekend: forall d: day, d = saturday -> Weekend d
  | secondWeekend: forall d: day, d = sunday -> Weekend d.
Check Weekend_ind.

Lemma ex1: forall d: day, Weekend d -> d = saturday \/ d = sunday.
Proof.
  intros.
  case H.
  - intros. left. assumption.
  - intros. right. assumption.
Qed.
Print ex1.