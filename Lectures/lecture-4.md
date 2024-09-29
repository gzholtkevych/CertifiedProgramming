<H1><b>Тема: Конструктивна пропозиційна логіка в The Coq Proof Assistant</b></H1>

Метою цієї лекції є побудова Coq-моделі конструктивної пропозиційної логіки.

Проте ми почнемо з загальної концепції універсумів типів в The Coq Proof Assistant.

Ми досі використовували вираз " $А$ *є типом* "  неформально.
Зробимо цей вираз більш точним, за допомогою концепції ***всесвітів***, імена яких в The Coq Proof Assistant
називаються ***сортами***.

Всесвіт є типом, елементи якого є типами.

Як і в наївній теорії множин, ми могли б бажати існування всесвіту всіх типів $\mathcal{U}^{\infty}$, який включав би себе самого,
тобто $\mathcal{U}^\infty:\mathcal{U}^\infty$.

**Нагадування.**
Позначення $t:A$ означає, що $t$ має тип $A$.

Однак, як і в теорії множин, це веде до протиріччя, тобто ми можемо вивести з цього, що кожен тип, включаючи порожній тип, що представляє
пропозицію `False`, є населеним.
Використовуючи, наприклад, подання множин у вигляді дерев, ми можемо безпосередньо закодувати парадокс Рассела.

Щоб уникнути парадоксу, ми вводимо ієрархію всесвітів

```math
\mathcal{U}^{(0)}:\mathcal{U}^{(1)}:\mathcal{U}^{(2)} : · · ·
```

де кожен всесвіт $\mathcal{U}^{(i)}$ є елементом наступного всесвіту $\mathcal{U}^{(i+1)}$.<br/>
Крім того, ми припускаємо, що наші всесвіти є кумулятивними, тобто всі елементи $i$-го всесвіту також є елементами $(i+1)$-го всесвіту ,
тобто якщо $A:\mathcal{U}^{(i)}$, то також $A:\mathcal{U}^{(i+1)}$.

Це зручно, але має трохи неприємний наслідок, оскільки елементи більше не мають унікальних типів, що в певних ситуаціях може призводити до
складнощів.

Коли ми говоримо, що $A$ є типом, ми маємо на увазі, що він живе в якомусь всесвіті $\mathcal{U}^{(i)}$.
Зазвичай ми уникаємо явного згадування рівня $i$ і просто припускаємо, що The Coq Proof Assistant може призначати рівні коректно;
тому ми можемо написати $A:\mathcal{U}$ без рівня.

Таким чином ми навіть можемо написати $\mathcal{U}:\mathcal{U}$, що можна прочитати як $\mathcal{U}^{(i)}:\mathcal{U}^{(i+1)}$,
залишивши індекси неявними.

Написання всесвітів у цьому стилі називають типовою двозначністю.<br/>
Це зручно, але трохи небезпечно, оскільки дозволяє нам писати дійсні докази, які відтворюють парадокси самопосилання.
Якщо є будь-які сумніви щодо правильності аргументу, спосіб перевірити це — спробувати послідовно призначити рівні всім всесвітам, які в ньому з’являються.

Коли розглядається деякий всесвіт $\mathcal{U}$, ми можемо називати типи, що належать до $\mathcal{U}$, ***малими типами*** відносно $\mathcal{U}$.<br/>
Прицьому сам $\mathcal{U}$ не є малим типом відносно себе. 


----

(* Тріада: терм - тип - сорт, де сорт є або Set, або Prop, або Type.
   Все є терми, деякі з термів є типами.
   Сорти - це спеціальні типові константи Set, Prop та Type.
   Сорт Type насправді індексований натуральними числами
      Type_0, ..., Type_k, ..., але індекс завжди прихований.
   Кожний терм t населяє певний тип T, що позначається через t : T.
   Наприклад, Set : Type_0, Prop : Type_0, Type_k : Type_{k+1}.
   Наспроавді постулюється справедливість таких суджень:
      Set : Type_0
      Prop : Type_0
      Type_n : Type_m, якщо n < m
   та для будь-якого типу T
      T : Type_0, якщо T : Set
      T : Type_0, якщо T : Prop
      T : Type_m якщо T : T_n та n < m
*)

Check Set.
Check Prop.
Check Type.

Section SecName.
Variable T : Type.
Hypothesis tnd : forall P : Prop, P \/ ~ P.
Check T.
Check tnd.
End SecName.
Fail Check T.
Fail Check tnd.

Locate False.
Locate True.
Check False.
Print Term False.
Check False_ind.

Check True.
Print Term True.
Check True_ind.

Check bool.
Print Term bool.
Check bool_ind.

Section bool_and_Prop.
Variable X : Type.

Definition P (ch : X -> bool) : X -> Prop :=
  fun x => ch x = true.
Check P _.

Lemma P_ch_dec : forall ch x, (P ch x \/ ~ P ch x).
Proof.
  intros. unfold P.
  case (ch x).
  - (* case ch x = true *)
    left. reflexivity.
  - (* case ch x = false *)
    right. intro. discriminate H.
Qed.
End bool_and_Prop.
Check P.
Check P_ch_dec.

Check and.
Print Term and.
Check and_ind.

Section andProperties.
Variables A B C : Prop.

Lemma and_comm : A /\ B <-> B /\ A.
Proof.
  split; intro.
  - elim H. intros HA HB.
    (* pose (HBA := conj HB HA). exact HBA.   *)
    split.
    + assumption.
    + assumption.
  - elim H. intros HB HA.
    split; assumption.
Qed.

Lemma and_comm' : A /\ B <-> B /\ A.
Proof. split; intro; elim H; intros; split; assumption. Qed.

Print Term and_comm.
Print Term and_comm'.

Lemma and_assoc : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split; intro H.
  - elim H. intros. elim H0. intros. split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - elim H. intros. elim H1. intros; split; [ split; assumption | assumption ].
Qed.

Lemma and_assoc' : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split; intro H; elim H; intros; [elim H0 | elim H1];
  intros; repeat split; assumption.
Qed.

Print Term and_assoc.
Print Term and_assoc'.

End andProperties.

Check and_comm.
Check and_assoc.

Check or.
Print Term or.
Check or_ind.

Section orProperties.
Variables A B C : Prop.

Lemma or_comm : A \/ B <-> B \/ A.
Proof.
  split; intro; elim H; intro;
(*  - right. assumption.
  - left. assumption.
  - right. assumption.
  - left. assumption. *)
  (right; assumption) || (left; assumption).
Qed.

Lemma or_assoc: (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split; intro; elim H; intro; try (elim H0; intro);
  (repeat left; assumption) ||
    (repeat right; assumption) ||
    (right; left; assumption) ||
    (left; right; assumption). 
Qed.

End orProperties.

Print Term or_comm.
Print Term or_assoc.


Section PLaxioms.
Variables A B C : Prop.

Lemma ax1 (*16*) : A -> B -> A.
Admitted.

Lemma ax2 : (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  intros H1 H2 H3. apply H2.
  - assumption.
(*  - apply H1. assumption. *)
  - pose (H := H1 H3). assumption.
Qed.

Lemma ax3 (*16*) : A /\ B -> A.
Admitted.

Lemma ax4 (*16*) : A /\ B -> B.
Admitted.

Lemma ax5 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros H1 H2 H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

   Lemma ax6 (*16*) : A -> A \/ B.
Admitted.

Lemma ax7 (*16*) : B -> A \/ B.
Admitted.

   Lemma ax8 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros H1 H2 H3.
  elim H3; intro H.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax9 (*20*) : (A -> ~ B) -> B -> ~ A.
Admitted.

End PLaxioms.

