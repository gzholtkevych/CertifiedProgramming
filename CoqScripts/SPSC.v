Require Import Coq.Lists.List.
Import ListNotations.

(* Про цей проєкт:
   -------------------------------------------------------------------------- 
   Розглядаються арифметичні вирази з операціями додавання та множення над
   натуральними числами.
   Для цих виразів визначається синтаксична структура виразів та їх
   семантичне значення, яким є результат прямого обчислення відповідного
   виразу.

   Розглядається також простий програмований стековий обчислювач, пам'ятю
   якого є стек натуральних чисел, а команди мають наступний формат
      save n, де n є натуральне число
      eval op, де op є символ операції Plus або Mult 

   Мета прєкту: побудувати транслятор, який перетворює вираз на програму для
   простого стекового обчислювача, яка обчислює вираз
   -------------------------------------------------------------------------- *)

(* ========================================================================== *)
(* Синтаксична модель виразу  =============================================== *)
(* Припустимо, що вираз будується за допомогою бінарних операцій Plus та Mult.
   Тому визначимо тип "binop" - бінарна операція шляхом перелічення:  
     binop -> Plus | Mult                                                     *)

Inductive binop : Set := Plus | Mult.

(* Дослідження індуктивного визначення для binop ---------------------------- *)
(*   Який тип має binop?:      *) Check binop.
(*   Який визначене binop?:    *) Print binop.
(*   Який тип має Plus?:       *) Check Plus.
(*   Який тип має Mult?:       *) Check Mult.
(*   Який тип має binop_ind?:  *) Check binop_ind.
(*   Який тип має binop_rec?:  *) Check binop_rec.   
(*   Який тип має binop_rect?: *) Check binop_rect.  

(* Визнначення типу "expr" - вираз у відповідності до граматичних правил:
     expr -> 'Const' nat | 'Binop' b expr expr                                *)
Inductive expr : Set :=
  | Const : nat -> expr                    (* перше граматичне правило *)
  | Binop : binop -> expr -> expr -> expr. (* друге граматичне правило *)

(* Долслідження наперед визначеного типу nat -------------------------------- *)
(*   В якому контекстів визначений nat?: *) Locate nat.
(*   Який тип має nat?:                  *) Check nat.
(*   Як визначений nat?:                 *) Print nat.
(*   Які є індуктивні принципи для nat?: *) Check nat_ind.
                                            Check nat_rec.
                                            Check nat_rect.


(* Інтерпретація бінарних операцій як натуральнозначних функцій двох
   натуральних аргументів                                                     *)
Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    Plus => plus |
    Mult => mult
  end.

(* Дослідження функцій plus та mult з стандартної бібліотеки ---------------- *)
(*   В якому контекстів визначений plus?: *) Locate plus.
(*   Який тип має plus?:                  *) Check plus.
(*   Як визначений plus?:                 *) Print Nat.add.
(*   В якому контекстів визначений mult?: *) Locate mult.
(*   Який тип має mult?:                  *) Check mult.
(*   Як визначений mult?:                 *) Print Nat.mul.

(* Інтерпретація виразів                                                      *)
Fixpoint exprDenote (e : expr) : nat :=
  match e with
    Const n       => n |
    Binop b e1 e2 => binopDenote b (exprDenote e1) (exprDenote e2)
  end.

(* Як це працює? Приклади виразів та їх інтерпретації ----------------------- *)
Example c2 := Const 2.
Eval simpl in exprDenote c2.
Example c3 := Const 3.
Eval simpl in exprDenote c3.
Example ePlus_c2_c3 := Binop Plus c2 c3.
Eval simpl in exprDenote ePlus_c2_c3.
Example c4 := Const 4.
Eval simpl in exprDenote c4.
Example eMult_ePlus_c2_c3_c4 := Binop Mult ePlus_c2_c3 c4.
Eval simpl in exprDenote eMult_ePlus_c2_c3_c4.


(* Модель простого стекового обчислювача ==================================== *)
(* Простий стековий обчислювач має
     пам'ять, яка структурована як стек, та
     програму, яка є списком інструкцій.
   Таким чином, нам знадобиться формаліщація списку, яка забезпечується
   використанням имац list із стандартної бібліотеки.                         *)

(* Долслідження наперед визначеного типу list ------------------------------- *)
(*   В якому контекстів визначений list?: *) Locate list.
(*   Який тип має list?:                  *) Check list.
(*   Як визначений list?:                 *) Print list.
(*   Які є індуктивні принципи для list?: *) Check list_ind.
                                             Check list_rec.
                                             Check list_rect.
(*   Стандартні позначення для списків    *) Print Scope list_scope.
(*   Функція конкатенації списків app     *) Print Term app.

(* Зауважимо, що значенням кожної інструкції є перетворення стеку, яке може
   бути визначене не для всіх станів стеку, у зв'язку з чим нам знадобиться
   тип option із стандартної бібліотеки                                       *)

(* Долслідження наперед визначеного типу option ----------------------------- *)
(*   В якому контекстів визначений option?: *) Locate option.
(*   Який тип має option?:                  *) Check option.
(*   Як визначений option?:                 *) Print option.
(*   Які є індуктивні принципи для option?: *) Check option_ind.
                                               Check option_rec.
                                               Check option_rect.

Definition stack := list nat.      (* пам'ять обчислювача    *)
Inductive instr : Set :=           (* інструкції обчислювача *)
    save : nat -> instr |
    eval : binop -> instr.
Definition program := list instr.  (* програма обчислювача   *)

(* Інтерпретація інструкцій обчислювача                                       *)
Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    save n => Some (n :: s) |
    eval b => match s with
                n :: m :: s' => Some ((binopDenote b n m) :: s') |
                _            => None
              end
  end.

(* Виконання програми з певного стану стеку                                   *)
Fixpoint execute (p : program) (s : stack) : option stack :=
  match p with
    nil     => Some s |
    i :: p' => match instrDenote i s with
                 None    => None |
                 Some s' => execute p' s'
               end
  end.

(* Семантичне значення програми                                               *)
Definition programDenote (p : program) : option stack := execute p nil.


(* Компілятор виразів у програми простого програмованого стекового
   обчислювача ============================================================== *)
Fixpoint compile (e : expr) : program :=
  match e with
    Const n => save n :: nil
  | Binop b e1 e2 => (compile e2) ++ (compile e1) ++ eval b :: nil
  end.

(* Як це працює? Приклад компіляції                                           *)
Example p := compile eMult_ePlus_c2_c3_c4.
Eval compute in p.
Eval compute in programDenote p.


(* Теорема коректності процесу компіляції =================================== *)
(* Коректність процесу компіляції означає, що значення виразу і значення
   програми, отриманої в процесі компіляції цього виразу співпадають, або
   формально                                                                  *)
Theorem correctness : forall e : expr,
  Some [exprDenote e] = programDenote (compile e).
Abort.

Check forall e : expr, Some [exprDenote e] = programDenote (compile e).

Theorem correctness : forall e : expr,
  Some [exprDenote e] = programDenote (compile e).
Proof.
  intro.
  induction e.
  2: {
Abort.

Theorem correctness : forall e : expr,
  Some [exprDenote e] = programDenote (compile e).
Proof.
  intro.
  induction e.
  - unfold programDenote. simpl. reflexivity.
Abort.

(* Принцип послідовної компіляції ------------------------------------------- *)
Lemma seq_calc : forall (s : stack) (e : expr) (p : program),
  execute (compile e ++ p) s = execute p (exprDenote e :: s).
Proof.
  intros until e. revert s.
  induction e.
  - intros. simpl. reflexivity.
  - intros. simpl.
Abort.


(* Асоциативність конкатенації списків -------------------------------------- *)
(* Знайти все, де використовується ++ *) Search " ++ ".
(* Перевіремо app_assoc_reverse       *) Check app_assoc_reverse.


Lemma seq_calc : forall (s : stack) (e : expr) (p : program),
  execute (compile e ++ p) s = execute p (exprDenote e :: s).
Proof.
  intros until e. revert s.
  induction e.
  -(* індукція для Const *) intros. simpl. reflexivity.
  -(* індукція для Binop *)
    intros. simpl.
    rewrite app_assoc_reverse.
    rewrite IHe2.
    rewrite app_assoc_reverse. simpl.
    rewrite IHe1. simpl.
    reflexivity. 
Qed.

Print Term seq_calc.

Theorem correctness : forall e : expr,
  Some [exprDenote e] = programDenote (compile e).
Proof.
  intros.
  induction e.
  -(* індукція для Const *)
    simpl. unfold programDenote. simpl. reflexivity.
  -(* індукція для Binop *)
    simpl. unfold programDenote.
    repeat rewrite seq_calc. simpl.
    reflexivity.
Qed.
