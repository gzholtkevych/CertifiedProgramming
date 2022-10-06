Require Import Lists.List.
Import ListNotations.


(* Синтаксис простої мови типізованих виразів =============================== *)

(* Фіксуємо два типи - натуральний та булевий                                 *)
Inductive type := Nat : type | Bool : type.
(* Визначаємо також функцію D, що співставляє визначеним типам їх домени -
   множини значень                                                            *)
Check type.
Definition D : type -> Set := fun t =>
  match t with Nat => nat | Bool => bool end.
Print Term D.

(* Бінарна операція тепер параметризується трійкою типів:
   тип першого операнда, тип другого операнда і тип результату                *)
Inductive binop : type -> type -> type -> Set :=
  NPlus : binop Nat Nat Nat
| NMult : binop Nat Nat Nat
| TEq : forall t, binop t t Bool
| NLt : binop Nat Nat Bool.

(* Вираз тепер параметризується типом - типом цього виразу                    *)
Inductive expr : type -> Set :=
| Const : forall t, D t -> expr t
| Binop :
    forall t1 t2 t, binop t1 t2 t -> expr t1 -> expr t2 -> expr t.
(* Для конструктора Binop визначемо параметри операції як такі,
   які The Coq Proof Assistant має встановити шляхом самостійно за контекстом *)
Arguments Binop {t1 t2 t}.
Print Term expr. 

(* Інтерпретація простих типізованих виразів як значень відповідних типів === *)

(* Функції, що використовуються для інтерпретації --------------------------- *)
Fixpoint beq_nat (n m : nat) : bool :=
  match n,m with
    0, 0       => true
  | 0, S _     => false
  | S _, 0     => false
  | S n', S m' => beq_nat n' m'
  end. (* булев тест щодо рівностті натуральних чисел *)
Print Term beq_nat.

Definition beq_bool (b1 b2 : bool) : bool :=
  match b1, b2 with
    true, true   => true
  | false, false => true
  | _, _         => false
  end. (* булев тест щодо рівності булевих значень *)

Fixpoint blt_nat (n m : nat) : bool :=
  match n, m with
    _, 0       => false
  | 0, S _     => true
  | S n', S m' => blt_nat n' m'
  end. (* булев тест відношення меньше натуральних чисел *)

(* Інтерпретація бінарних операцій відповідними функціями з виеористаннм
   технікм визначення шляхом доведення.
   Аргументи t1 t2 t є такими, які The Coq Proof Assistant має встановити
   за контекстом                                                              *)
Definition binopDenote {t1 t2 t : type} (b : binop t1 t2 t)
: D t1 -> D t2 -> D t.
Proof.
  intros a1 a2.
  destruct b.
  - (*case NPlus*) simpl. simpl in a1, a2. exact (plus a1 a2).
  - (*case NMult*) simpl. simpl in a1, a2. exact (mult a1 a2).
  - (*case TEq*) simpl. destruct t; simpl in a1, a2.
    + (*case Nat*) exact (beq_nat a1 a2).
    + (*case Bool*) exact (beq_bool a1 a2).
  - (*case NLt*) simpl. simpl in a1, a2. exact (blt_nat a1 a2).
Defined.
Print Term binopDenote.
Eval simpl in binopDenote NPlus 3 5.
Eval simpl in binopDenote (TEq Nat) 2 2.

(* Інтерпретація типізованих виразів                                          *)
Definition exprDenote {t : type} (e : expr t) : D t.
Proof.
  induction e as [t v | t1 t2 t b e1 a1 e2 a2].
  - (*case Const*) exact v.
  - (*case Binop*) exact (binopDenote b a1 a2).
Defined.
Print Term exprDenote.
Example n2 := Const Nat 2.
Example n3 := Const Nat 3.
Example eNPlus_n2_n3 := Binop NPlus n2 n3. 
Example eNLt_n2_eNPlus_n2_n3 := Binop NLt n2 eNPlus_n2_n3.
Example bf := Const Bool false.
Fail Example eTEq_Nat_bf_n2 := Binop (TEq Nat) bf n2.
Eval simpl in exprDenote n2.
Eval simpl in exprDenote n3.
Eval simpl in exprDenote eNPlus_n2_n3.
Eval simpl in exprDenote eNLt_n2_eNPlus_n2_n3.

(* Простий стековий обчислювач з підтримкою типів =========================== *)

(* Програма як послідовність інструкцій тепер може бути некоректною не тільки
   тому, що у стані стеку з менш ніж двома елементами неможливо застосувати
   інструкцію обчислення значення бінарної операції, але й тому, що типи
   операндів можуть бути такими, що не відповідають типам значень елементів
   стеку.
   Для захисту від такої "типової некоректності" необхідно класифікувати
   стеки значень, для чого вводиться наступний тип                            *)
Definition tstack := list type.
Check tstack.

(* Інструкції стекового обчислювача тепер будемо параметризувати станом
   tstack до і після виконання інструкції.
   ЗВЕРНІТЬ УВАГУ!!! Перевірка типової коректності не потребує реальних
   обчислень. Тобто семантична задача шляхом типізації перетворюється на
   синтаксичну і це є основною метою при введенні систем типів                *)
Inductive instr : tstack -> tstack -> Set :=
  save : forall ts, forall t, D t -> instr ts (t :: ts)
| eval : forall ts, forall t1 t2 t,
           binop t1 t2 t -> instr (t1 :: t2 :: ts) (t :: ts).
Arguments save {ts}.
Arguments eval {ts} {t1 t2 t}.
Print Term instr.

(* Тип програми стекового обчислювача, безпечний за типами                    *)
Inductive prog : tstack -> tstack -> Set :=
  pNil : forall ts, prog ts ts
| pApp : forall ts1 ts2 ts, prog ts1 ts2 -> instr ts2 ts -> prog ts1 ts.
Arguments pApp {ts1 ts2 ts}.
Print Term prog.

(* Безпосереднє створення програми, використовуючи конструктори типу prog     *)
Example save2_save3_evalNPlus'
:= pApp (pApp (pApp (pNil []) (save Nat 2)) (save Nat 3)) (eval NPlus).
Check save2_save3_evalNPlus'.
Print Term save2_save3_evalNPlus'.

(* Контроль типової коректності "зашито" у визначення типу prog               *)
Fail Example save2_save3_evalBEqFail 
:= pApp (pApp (pApp (pNil []) (save Nat 2)) (save Nat 3)) (eval TEq Bool).
(* Альтернативний метод програмування стекового обчислювача                   *)
Example save2_save3_evalNPlus : prog [] [Nat].
Proof.
  pose (p0 := pNil []).
  pose (p1 := pApp p0 (save Nat 2)).
  pose (p2 := pApp p1 (save Nat 3)).
  pose (p3 := pApp p2 (eval NPlus)).
  exact p3.
Defined.
Check save2_save3_evalNPlus.
Print Term save2_save3_evalNPlus.

(* Стек значень, пов'язаний зі стеком типів
   unit - тип зі стандартної бібліотеки населений єдиним термом tt
   _ * _ - декартов добуток типів                                             *)
Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    nil => unit
  | t :: ts' => D t * vstack ts'
  end.

(* Семантика інструкцій стекового обчислювача                                 *)
Definition instrDenote {ts ts' : tstack} (i : instr ts ts')
: vstack ts -> vstack ts'.
Proof.
  destruct i as [t ts v | t1 t2 t ts b]; simpl.
  - (*case Const*) destruct t; simpl; simpl in v; intro vs; exact (v, vs).
  - (*case Binop*) destruct b; simpl; intro vs.
    + (*case NPlus*)
      destruct vs as [v1 vs']. destruct vs' as [v2 vs].
      pose (e1 := Const Nat v1).
      pose (e2 := Const Nat v2).
      pose (e := Binop NPlus e1 e2).
      exact (exprDenote e, vs).
    + (*case NMult*)
      destruct vs as [v1 vs']. destruct vs' as [v2 vs].
      pose (e1 := Const Nat v1).
      pose (e2 := Const Nat v2).
      pose (e := Binop NMult e1 e2).
      exact (exprDenote e, vs).
    + (*case TEq*) destruct t; simpl in vs.
      * (*case Nat*)
        destruct vs as [v1 vs']. destruct vs' as [v2 vs].
        pose (e1 := Const Nat v1).
        pose (e2 := Const Nat v2).
        pose (e := Binop (TEq Nat) e1 e2).
        exact (exprDenote e, vs).
      * (*case Bool*)
        destruct vs as [v1 vs']. destruct vs' as [v2 vs].
        pose (e1 := Const Bool v1).
        pose (e2 := Const Bool v2).
        pose (e := Binop (TEq Bool) e1 e2).
        exact (exprDenote e, vs).
    + (*case NLt*)
      destruct vs as [v1 vs']. destruct vs' as [v2 vs].
      pose (e1 := Const Nat v1).
      pose (e2 := Const Nat v2).
      pose (e := Binop NLt e1 e2).
      exact (exprDenote e, vs).
Defined.
Print Term instrDenote.

Definition progDenote {ts ts' : tstack} (p : prog ts ts')
: vstack ts -> vstack ts'.
Proof.
  induction p as [ts | ts ts1 ts' p' p'Denote i].
  - (*case pNil*) exact (fun v => v).
  - (*case pApp*)
    pose (iDenote := instrDenote i). intro vs.
    apply iDenote. apply p'Denote. exact vs.
Defined.
Print Term progDenote.

Eval simpl in progDenote save2_save3_evalNPlus tt.

(* Компіляція =============================================================== *)

Definition pconcat {ts ts' ts''} (p : prog ts ts')
: prog ts' ts'' -> prog ts ts''.
Proof.
  intro p'. revert ts p.
  induction p' as [ts'' | ts' ts1 ts'' p'' Hp i]; intros.
  - exact p.
  - pose (p1 := pApp (Hp ts p) i). exact p1.
Defined.
Print Term pconcat.

Definition compile {t} (e : expr t) (ts : tstack) : prog ts (t :: ts).
Proof.
  revert ts.
  induction e as [| ts1 ts2 ts b e1 Hp1 e2 Hp2]; intro ts0.
  - (* Const *) exact (pApp (pNil _) (save t d)).
  - (* Binop *)
    pose (p2 := Hp2 ts0). pose (p1 := Hp1 (ts2 :: ts0)).
    pose (p12 := pconcat p2 p1).
    exact (pApp p12 (eval b)).
Defined.
Print Term compile.
Eval simpl in progDenote (compile eNPlus_n2_n3 []) tt.

(* Correctness theorem =================================+==================== *)
Theorem correctness : forall t (e : expr t), 
  progDenote (compile e nil) tt = (exprDenote e, tt).
Abort.

Lemma pconcat_correct :
  forall ts ts' ts'' (p : prog ts ts') (p' : prog ts' ts'') (vs : vstack ts),
    progDenote (pconcat p p') vs = progDenote p' (progDenote p vs).
Proof.
  intros until p. revert ts''.
  induction p'; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.

Lemma correctness' : forall t  (e : expr t) ts (vs : vstack ts),
  progDenote (compile e ts) vs = (exprDenote e, vs).
Proof.
  induction e.
  - intros.
    destruct t; induction ts; simpl; reflexivity.
  - intros. destruct b.
    + simpl. rewrite pconcat_correct. rewrite IHe1. rewrite IHe2. reflexivity.
    + simpl. rewrite pconcat_correct. rewrite IHe1. rewrite IHe2. reflexivity.
    + destruct t; simpl; rewrite pconcat_correct;
      rewrite IHe1; rewrite IHe2; reflexivity.
    + simpl. rewrite pconcat_correct. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Theorem correctness : forall t (e : expr t), 
  progDenote (compile e nil) tt = (exprDenote e, tt).
Proof. intros. apply correctness'. Qed.

  