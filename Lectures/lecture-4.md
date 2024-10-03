<H1><b>Тема: Конструктивна пропозиційна логіка в The Coq Proof Assistant</b></H1>

Метою цієї лекції є побудова Coq-моделі конструктивної пропозиційної логіки.

Проте ми почнемо з загальної концепції універсумів типів в The Coq Proof Assistant.

# Універсуми типів

Ми досі використовували вираз " $А$ *є типом* "  неформально.
Зробимо цей вираз більш точним, за допомогою концепції ***всесвітів***, імена яких в The Coq Proof Assistant
називаються ***сортами***.

Всесвіт є типом, елементи якого є типами.

Як і в наївній теорії множин, ми могли б бажати існування всесвіту всіх типів $\mathcal{U}$, який включав би себе самого, тобто
$\mathcal{U}:\mathcal{U}$.

**Нагадування.**
Позначення $t:A$ означає, що $t$ має тип $A$.

Однак, як і в теорії множин, це веде до протиріччя, тобто ми можемо вивести з цього, що кожен тип, включаючи порожній тип, що представляє
пропозицію `False`, є населеним.
Використовуючи, наприклад, подання множин у вигляді дерев, ми можемо безпосередньо закодувати парадокс Рассела.

Щоб уникнути парадоксу, ми вводимо ієрархію всесвітів

```math
\mathcal{U}_0:\mathcal{U}_1:\mathcal{U}_2 : · · ·
```

де кожен всесвіт $\mathcal{U}\_i$ є елементом наступного всесвіту $\mathcal{U}\_{i+1}$.<br/>
Крім того, ми припускаємо, що наші всесвіти є кумулятивними, тобто всі елементи $i$-го всесвіту також є елементами $(i+1)$-го всесвіту ,
тобто якщо $A:\mathcal{U}\_i$, то також $A:\mathcal{U}\_{i+1}$.

Це зручно, але має трохи неприємний наслідок, оскільки елементи більше не мають унікальних типів, що в певних ситуаціях може призводити до
складнощів.

Коли ми говоримо, що $A$ є типом, ми маємо на увазі, що він живе в якомусь всесвіті $\mathcal{U}^{(i)}$.
Зазвичай ми уникаємо явного згадування рівня $i$ і просто припускаємо, що The Coq Proof Assistant може призначати рівні коректно;
тому ми можемо написати $A:\mathcal{U}$ без рівня.

Таким чином ми навіть можемо написати $\mathcal{U}:\mathcal{U}$, що можна прочитати як $\mathcal{U}\_i:\mathcal{U}\_{i+1}$,
залишивши індекси неявними.

Написання всесвітів у цьому стилі називають типовою двозначністю.<br/>
Це зручно, але трохи небезпечно, оскільки дозволяє нам писати дійсні докази, які відтворюють парадокси самопосилання.
Якщо є будь-які сумніви щодо правильності аргументу, спосіб перевірити це — спробувати послідовно призначити рівні всім всесвітам, які в ньому
з’являються.

Коли розглядається деякий всесвіт $\mathcal{U}\_i$, ми можемо називати типи, що населяють $\mathcal{U}\_i$, ***малими типами*** відносно
$\mathcal{U}\_i$.<br/>
При цьому сам $\mathcal{U}\_i$ **не є** малим типом відносно себе. 

The Coq Proof Assistant визначає два базові універсуми, які іменуються сортами `Set` та `Prop`.
При цьому

- сорт `Set` посилається на універсум, який містить типи, що населені програмними конструкціями - програмами та даними;
- сорт `Prop` посилається на універсум, який містить типи, що відпрвідають логічним твердженням (propositions) і які населені доведеннями цих
тверджень.

Сорт `Type` має, насправді, неявний натуральний індекс і посилається на всесвіти ієрархії, при чому

```math
\begin{array}{c}\mathcal{U}_{\mathtt{Set}}\\\mathcal{U}_{\mathtt{Prop}}\end{array}\ :\ \mathcal{U}_{\mathtt{Type}_0}\ :\ \mathcal{U}_{\mathtt{Type}_1}\ :\ \ldots
\ :\ \ldots\ \mathcal{U}_{\mathtt{Type}_k}\ :\ \ \mathcal{U}_{\mathtt{Type}_{k+1}}\ :\ \ldots
```

Давайте подивимося, як це працює в The Coq Proof Assistant.

Команда

```coq
Check Set.
```
повертає

```coq
Set
     : Type
```

Аналогічно, команда

```coq
Check Prop.
```

повертає

```coq
Prop
     : Type
```

І, нарешті, команда

```coq
Check Type.
```

повертає

```coq
Type
     : Type
```

# Локальні контексти

Як ми знаємо, визначити тип терма, який використовує вільні змінні є неможливим, доти доки ми не зробимо припущень
щодо типів цих вільних змінних.<br/>
Відповідна система припущень називається ***оточенням (environment)***.

The Coq Proof Assistant при завантаженні автоматично імпортує визначення, що призводить до створення **глобального оточення**.

У разі необхідності зробити додаткові прирущення, ми змушені розширити глобальне оточення, що є небажаним.
Тому The Coq Proof Assistant надає можливість секціювання - оголошення локального контексту.

Для відкриття локального контексту використовується команда

```coq
Section SecName.
```

Тут `SecName` є ім'ям секції, в якій оточення складається з глобального оточення та оголошених в цій секції припущень типізації, які
утворюють ***локальний контнкст***.

Додаємо до локального контнксту змінну `T` типу `Type`.

```coq
Variable T : Type.
```

Відповідь системи

```coq
T is declared
```

Додаємо до локального контнксту змінну `tnd` типу `forall P : Prop, P \/ ~ P`, який живе в універсумі `Prop`.

```coq
Hypothesis tnd : forall P : Prop, P \/ ~ P.
```

Відповідь системи


```coq
tnd is declared
```

Перевіримо типи цих змінних

```coq
Check T.
Check tnd.
```

Відповідь системи

```coq
T
     : Type
tnd
     : forall P : Prop, P \/ ~ P
```

Закриємо тепер секцію.

```coq
End SecName.
```

Знову перевіримо типи змінних `T` та `tnd`

```coq
Fail Check T.
Fail Check tnd.
```

Ця перевірка дає помилку, оскільки змінні `T` та `tnd` не існують поза локальним контекстом

```coq
The command has indeed failed with message:
The reference T was not found in the current environment.

The command has indeed failed with message:
The reference tnd was not found in the current environment.
```

# Конструктивна пропозиційна логіка в The Coq Proof Assistant

Побудову моделі пропозиційної логіки почнемо з наступного принущення

>Логічні конструкції (***пропозиції***) є малими типами сорту `Prop`.

## Початкові кроки

Тому, для початку, визначимо дві константні пропозиції

- `True`, яка моделює тотожньо істину пропозицію,
- `False`, яка моделює тотожньо хибну пропозицію.

Ці пропозиції вже визначені в стандартній бібліотеці `Coq.Init.Logic`.

Маємо

*Запит:*

```coq
Check False.
```

*Відповідь:*

```coq
False : Prop
```

*Запит:*

```coq
Print Term False.
```

*Відповідь:*

```coq
Inductive False : Prop :=  
```

Це визначення означає, що тип `False` є ненаселеним.

Аналогічно для `True` маємо

*Запит:*

```coq
CheckTrue.
```

*Відповідь:*

```coq
True : Prop
```

*Запит:*

```coq
Print Term True.
```

*Відповідь:*

```coq
Inductive True : Prop :=  I : True
```

Зауважимо, що стандартна бібліотека `Coq.Init.Datatypes` містить також визначення типу `bool`

*Запит:*

```coq
Check bool.
```

*Відповідь:*

```coq

bool
     : Set
```

Це малий тип сорту `Set`, який визначається так

*Запит:*

```coq
Print Term bool.
```

*Відповідь:*

```coq

Inductive bool : Set :=  true : bool | false : bool
```

Зазначимо, що ***предикат*** - функцію з якогось типу `X` у сорт `Prop`, можна побудувати за
характеристичною функцією - функція з `X` у тип `bool`, `ch`.

*Визгачення і запит.*

```coq
Section bool_and_Prop.
Variable X : Type.

Definition P (ch : X -> bool) : X -> Prop :=
  fun x => ch x = true.
Check P _.
```

*Відповідь:*

```coq
P ?ch
     : X -> Prop
where
?ch : [X : Type |- X -> bool]
```

Для побудованого предикату є вірною така властивість звана ***розв'язністю***.

```coq
Lemma P_ch_dec : forall ch x, (P ch x \/ ~ P ch x).
```

Її доведення

```coq
Proof.
  intros. unfold P.
  case (ch x).
  - (* case ch x = true *)
    left. reflexivity.
  - (* case ch x = false *)
    right. intro. discriminate H.
Qed.
End bool_and_Prop.
```

Тепер на *запит*

```coq
Check P.
Check P_ch_dec.
```

отримаємо *відповідь*

```coq
P
     : forall X : Type, (X -> bool) -> X -> Prop
P_ch_dec
     : forall (X : Type) (ch : X -> bool) (x : X), P X ch x \/ ~ P X ch x
```

Тобто, ми бачимо, що предикат побудований за хараетеристичною функцією є розв'язним, проте зворотнє
таердження **не є вірним в конструктивній логіці**.

## Кон'юнкція

В пропозиційній логіці складні твердження будуються з простих за допомогою ***пропозиційних зв'язок***

- ***кон'юнкції*** `P /\ Q`,
- ***диз'юнкції*** `P \/ Q` та
- ***імплікації*** `P -> Q`.

Крім того, використовують похідна зв'язка

- ***заперечення*** `~ P`, що означає `P -> False`.

**Зауваження.**
Імплікація моделюється конструктором функціонального типу `->`.

Таким чином, нам треба визначити основні зв'язки.
Почнемо з визначення кон'юнкції, яке міститься в стандартній бібліотеці `Coq.Init.Logic`.

*Запит.*

```coq
Check and.
Print Term and.
```

*Відповідь.*

```coq
and
     : Prop -> Prop -> Prop
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B
```

Доведемо тепер оцикувані властивості кон'юнкції.

```coq
Section andProperties.
Variables A B C : Prop.
```

Перша з цих властивостей - комутативність.

```coq
Lemma and_comm : A /\ B <-> B /\ A.
```

Доведення можна реалізувати так.

```coq
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
```

Вигляд терму доведення дає такий *запит*.

```coq
Print Term and_comm.
```

*Відповідь.*

```coq
and_comm = 
conj (fun H : A /\ B => and_ind (fun (HA : A) (HB : B) => conj HB HA) H)
  (fun H : B /\ A => and_ind (fun (HB : B) (HA : A) => conj HA HB) H)
     : A /\ B <-> B /\ A
```

Наступною властивістю є асоциативність.

```coq
Lemma and_assoc : (A /\ B) /\ C <-> A /\ (B /\ C).
```

Доведення можна реалізувати так.

```coq
Proof.
  split; intro H.
  - elim H. intros. elim H0. intros. split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - elim H. intros. elim H1. intros; split; [ split; assumption | assumption ].
Qed.
```

Подивимося як виглядає терм доведення за допомогою *запиту*.

```coq
Print Term and_assoc.
```

*Відпоідь.*

```coq
and_assoc = 
conj
  (fun H : (A /\ B) /\ C =>
   and_ind (fun (H0 : A /\ B) (H1 : C) => and_ind (fun (H2 : A) (H3 : B) => conj H2 (conj H3 H1)) H0) H)
  (fun H : A /\ B /\ C =>
   and_ind (fun (H0 : A) (H1 : B /\ C) => and_ind (fun (H2 : B) (H3 : C) => conj (conj H0 H2) H3) H1) H)
     : (A /\ B) /\ C <-> A /\ B /\ C
```
Завершимо секцію.

```coq
End andProperties.
```

## Диз'юнкція

Подивимося, як виглядає визначення диз'юнкції в стандартній бібілотеці `Coq.Init.Logic` за допомогою
*запиту*

```coq
Check or.
Print Term or.
```

*Відповідь.*

```coq
or
     : Prop -> Prop -> Prop
Inductive or (A B : Prop) : Prop :=  or_introl : A -> A \/ B | or_intror : B -> A \/ B
```

Встановимо тепер властивості диз'юнкції аналогічно з кон'юнкцією.

```coq
Section orProperties.
Variables A B C : Prop.

Lemma or_comm : A \/ B <-> B \/ A.
Proof.
  split.
  - intro. elim H.
    + intro. right. assumption.
    + intro. left. assumption.
  - intro. elim H.
    + intro. right. assumption.
    + intro. left. assumption.
Qed.

Lemma or_assoc: (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  - intro.
    elim H.
    + intro.
      elim H0.
      * intro. left. assumption.
      * intro. right. left. assumption.
    + intro. right. right. assumption.
  - intro.
    elim H.
    + intro.
      left. left. assumption.
    + intro.
      elim H0.
      * intro. left. right. assumption.
      * intro. right. assumption.
Qed.

End orProperties.
```

З'ясуємо, як виглядають отримані терми доведень.<br/>
*Запит.*

```coq
Print Term or_comm.
Print Term or_assoc.
```

*Відповідь.*

```coq
or_comm = 
fun A B : Prop =>
conj (fun H : A \/ B => or_ind (fun H0 : A => or_intror H0) (fun H0 : B => or_introl H0) H)
  (fun H : B \/ A => or_ind (fun H0 : B => or_intror H0) (fun H0 : A => or_introl H0) H)
     : forall A B : Prop, A \/ B <-> B \/ A

or_assoc = 
fun A B C : Prop =>
conj
  (fun H : (A \/ B) \/ C =>
   or_ind
     (fun H0 : A \/ B => or_ind (fun H1 : A => or_introl H1) (fun H1 : B => or_intror (or_introl H1)) H0)
     (fun H0 : C => or_intror (or_intror H0)) H)
  (fun H : A \/ B \/ C =>
   or_ind (fun H0 : A => or_introl (or_introl H0))
     (fun H0 : B \/ C => or_ind (fun H1 : B => or_introl (or_intror H1)) (fun H1 : C => or_intror H1) H0)
     H)
     : forall A B C : Prop, (A \/ B) \/ C <-> A \/ B \/ C
```

## Аксиоми конструктивної пропозиційної логіки

Перевіримо тепер, що виконуються всі аксиоми конструктивної пропозиційної логіки.

**Зауваження.**
Доведення більшості відповідних тверджень запропоновані як вправи.
У такому разі замість `Proof. ... Qed.` стоїть `Admitted.`
Для вирішення вправи треба замінити `Admitted.` на `Proof. ... Qed.`, вмістом якого є доведення відповідної леми.
Максимальна сума балів - 25.

```coq
Section PLaxioms.
Variables A B C : Prop.

Lemma ax1 : A -> B -> A.
Admitted. (* Вправа L1, оцінюється у 4 бали *)

Lemma ax2 : (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  intros H1 H2 H3. apply H2.
  - assumption.
  - apply H1. assumption.
Qed.

Lemma ax3 : A /\ B -> A.
Admitted. (* Вправа L2 у 4 бали *)

Lemma ax4 : A /\ B -> B.
Admitted. (* Вправа L3 у 4 бали *)

Lemma ax5 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros H1 H2 H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax6 : A -> A \/ B.
Admitted. (* Вправа L4 у 4 бали *)

Lemma ax7 : B -> A \/ B.
Admitted. (* Вправа L5 у 4 бали *)

Lemma ax8 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros H1 H2 H3.
  elim H3; intro H.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax9 : (A -> ~ B) -> B -> ~ A.
Admitted. (* Вправа L6 у 5 балів *)

End PLaxioms.
```

# Додаток. Опис тактик, що застосовуються

## Тактики, що завершують доведення

**Тактика** `exact`

```math
\texttt{застосування 'exact h' перетворює}\quad
\dfrac{\begin{array}{c}
\Gamma \\
h:A\end{array}}{A}\quad
\texttt{на}\quad\texttt{No more subgoals}
```

**Тактика** `assumption`

**Тактика** `exact`

```math
\texttt{застосування 'assumption' перетворює}\quad
\dfrac{\begin{array}{c}
\Gamma \\
h:A\end{array}}{A}\quad
\texttt{на}\quad\texttt{No more subgoals}
```
