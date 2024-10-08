<H1><b>Тема: Задача сертифікованої розробки простого програмованого стекового обчислювача</b></H1>

Знайомство з технологією сертифікованого програмування почнемо з мініпроєкту, що демонструє сертифіковану розробку простого програмованого стекового обчислювача.
Код, що ілюструє викладення знаходиться [тут](https://github.com/gzholtkevych/CertifiedProgramming/blob/main/CoqScripts/SPSC.v).

# Завдання мініпроєкту

**Про цей проєкт:**
Розглядаються

- арифметичні вирази з операціями додавання та множення над натуральними числами.<br/>
Для цих виразів визначається синтаксична структура виразів та їх семантичне значення, яким є результат прямого обчислення відповідного виразу;
- простий програмований стековий обчислювач, пам'ятю якого є стек натуральних чисел, а команди мають наступний формат
  - `save` $n$, де $n$ є натуральне число
  - `eval op`, де `op` є символ операції `PLUS` або `MULT`.

**Мета прєкту:** побудувати транслятор, який перетворює вираз на програму для простого стекового обчислювача, яка обчислює вираз, опис якого транслюється.

# Мова арифметичних виразів

Детальніше арифметичні вирази утворюються з натуральних констант за допомогою бінарних операцій додавання і множення.

Абстрактний синтаксис мови арифметичних виразів визначається наступними правилами

- символ бінарної операції `binop` є або `PLUS`, або `MULT`,
- `const` $n$ є арифметичним виразом, якщо $n$ є натуральним числом,
- `term bop` $e_1\ e_2$ є арифметичним виразом, якщо `bop` є представником `binop`, а $e_1$ та $e_2$ є арифметичними виразами.

Семантичним значенням арифметичного виразу $e$ будемо вважати натуральне число `denote` $e$, яке цей вираз представляє, тобто

- `denote` $e$ має семантичне значення $n$, якщо $e\equiv$ `const` $n$;
- `denote` $e$ має снмантичне значення `denote` (`denote` $e_1$) $+$ (`denote` $e_2$), якщо $e$ має вигляд `term PLUS` $e_1\ e_2$, де $e_1$ та $e_2$ є арифметичними виразами;
- `denote` $e$ має снмантичне значення `denote` (`denote` $e_1$) $\cdot$ (`denote` $e_2$), якщо $e$ має вигляд `term MULT` $e_1\ e_2$, де $e_1$ та $e_2$ є арифметичними виразами.

Спроєктуємо та специфікуємо необхідні типи даних для представлення арифметичних виразів, використовуючи The Coq Proof Assistant.

Першим нашим кроком буде специфікація типу даних `binop`, призначеного для представлення символів бінарних операцій:

```coq
Inductive binop := PLUS | MULT.
```

Це визначення вводить новий тип з іменем `biniop`, в якому живуть лише дві константи `PLUS` та `MULT`.
Формальною гарантією того, що ніякі інші сутності окрім `PLUS` та `MULT` не живуть в `biniop`, є такі твердження

```coq
binop_ind : forall P : binop -> Prop, P Plus -> P Mult -> forall b : binop, P b
binop_rec : forall P : binop -> Set, P Plus -> P Mult -> forall b : binop, P b
binop_rect : forall P : binop -> Type, P Plus -> P Mult -> forall b : binop, P b
```

Саме команда `Inductive` забезпечує автоматичне генерування цих гарантій, відомих як принципи індукції.

Тепер ми можемо представити абстрактний синтаксис арифметичних виразів, використовуючи The Coq Proof Assistant.

```coq
Inductive expr :=
  const : nat -> expr
| term : binop -> expr -> expr -> expr.
```

У цьому визначенні використовується тип `nat`, який визначений у стандартній бібліотеці `Coq.Init.Datatypes`, яка завантажується автоматично при запуску `coqide`.
Визначення `nat` у цій бібліотеці є таким

```coq
Inductive nat : Set :=  O : nat | S : nat -> nat.
```

Вілповідні гарантії відсутності зайвих мешканців у типі `nat` є в точності варіантами принципу математичної індукції:

```coq
nat_ind : forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
nat_rec : forall P : nat -> Set, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
nat_rect : forall P : nat -> Type, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
```

Наведемо тепер приклади побудови арифметичних виразів:

```coq
Example c2 := const 2.
Example c3 := const 3.
Example ePLUS_c2_c3 := term PLUS c2 c3.
Example c4 := const 4.
Example eMULT_ePLUS_c2_c3_c4 := term MULT ePLUS_c2_c3 c4.
```


```mermaid
---
title: term MULT ePLUS_c2_c3 c4
---
graph TB
  subgraph c4[const 4]
  direction TB
    G(const) --> H[4: nat]
  end
  subgraph t1[term PLUS c2 c3]
    direction TB
    subgraph c3[const 3]
    direction TB
      C(const) --> D[3: nat]
    end
    subgraph c2[const 2]
    direction TB
      A(const) -->B[2: nat];
    end
    E(term) --> F[PLUS]
    E --> c2
    E --> c3
  end
  J(term) --> K[MULT]
  J --> t1
  J --> c4    
```

Побудову семантики арифметичних виразів почнемо з інтерпретації бінарних операцій як натуральнозначних функцій двох натуральних аргументів:

```coq
Definition binopDenote (bop : binop) : nat -> nat -> nat :=
  match bop with
    PLUS => plus
  | MULT => mult
  end.
```

Це визначення інтерпретує `binopDenote PLUS` як стандартну функцію `plus` з бібліотеки `Coq.Init.Peano`, а `binopDenote MULT` як стандартну
функцію `mult` з тієї ж бібліотеки.

Зазначимо, що імена `plus` та `mult` є аліасами імен `Nat.add` та `Nat.mul` відповідно, які показують, що визначення функцій знаходяться в
модулі `Nat`, в якому зібрана більшість визначень, пов'язаних з типом `nat`.

Тепер дамо визначення семантичного значення виразів:

```coq
Fixpoint exprDenote (e : expr) : nat :=
  match e with
    const n        => n
  | term bop e1 e2 => binopDenote bop (exprDenote e1) (exprDenote e2)
  end.
```

Команда `Fixpoint` на відміну від команди `Definition` означає, що визначення є рекурсивним - у четвертому рядку визначення використовується
посилання `exprDenote`, значення якого визначається. 

Подивимося як це працює.

Вводимо:

```coq
Eval simpl in exprDenote c2.
```

Отримуємо:

```coq
= 2 : nat
```

Вводимо:

```coq
Eval simpl in exprDenote c3.
```

Отримуємо:

```coq
= 3 : nat
```

Вводимо:

```coq
Eval simpl in exprDenote ePLUS_c2_c3.
```

Отримуємо:

```coq
= 5 : nat
```

Вводимо:

```coq
Eval simpl in exprDenote eMULT_ePLUS_c2_c3_c4.
```

Отримуємо:

```coq
= 20 : nat
```

# Стековий обчислювач

Простий стековий обчислювач має

- пам'ять, яка структурована як стек, та
- механізм виконання програм, які є списками інструкцій.

Для формалізації як станів пам'яті так і програм використовується ствндартний тип список (`list`) із стандартної бібліотеки `Coq.Init.Datatypes`.

Цей тип визначається як

```coq
Inductive list (A : Type) : Type :=  nil : list A | cons : A -> list A -> list A.
```

Цей тип є поліморфним, тобто параметрично залежним від іншого (базового) типу - типу його членів.

Програма обчислювача є списком команд, кожна з яки є або

- командою `save n`, яка проштовхує `n` в стек, або
- командою `eval bop`, яка виконує операцію, що визначається значенням `bop`, над двома числами з вершини стеку, видалючі їх і натомість
проштовхуючи в стек результат обчислення.
Зрозуміло, що ця команда може виконуватися тільки у випадку, якщо у стеку зберігається не менше двох чисел.

Формалізуємо еавелений опис обчислювача.

Визначення типу для представлення пам'ті:

```coq
Definition stack := list nat.      (* тип для станів пам'яті обчислювача *)
```

Визначення типу для представлення інструкцій:

```coq
Inductive instr : Set :=           (* тип для інструкцій обчислювача *)
  | save : nat -> instr
  | eval : binop -> instr.
```

Вмзначення типу для представлення програми обчислювача:

```coq
Definition program := list instr.  (* тип для програм обчислювача   *)
```

Визнвчемо також  семантичні значення:

- інструкцій обчислювача, як перетворень станів пам'яті до виконання інструкції на стани пам'яті після її виконання
з можливою помилку виконання 

```coq
Definition instrDenote (i : instr) : stack -> option stack :=
  fun s =>
    match i with
      save n => Some (n :: s)
    | eval b => match s with
                  n :: m :: s' => Some ((binopDenote b n m) :: s')
                | _            => None
                end
    end.
```

Результат виконання програми з певного стану стеку

```coq
Fixpoint execute (p : program) : stack -> option stack :=
  fun s =>
    match p with
      nil     => Some s
    | i :: p' => match instrDenote i s with
                 | None    => None
                 | Some s' => execute p' s'
                 end
  end.
```

Семантичне значення програми є результатом її виконання з порожнього стану стеку.

```coq
Definition programDenote (p : program) : option stack := execute p nil.
```

# Задача трансляції

>Визначити функцію `compile : expr -> program`, яка перетворює вираз на програму, що має семантичне значення ***узгоджене***
з семантичним значенням виразу.<br/>
>Узгодженість формально для цієї задачі розуміється як справедливість наступної теореми коректності

```coq
Theorem correctness : forall e : expr,
  Some [exprDenote e] = programDenote (compile e).
```

Ця теорема вимагвє, щоб програма, створена функцією `compile` для будь-якого виразу, на порожньому стеку завершувалася б без
помилки і стек після її виконання містив би всього одне значення, а саме значення виразу, що компілювався.

Таким чином, задача ***сертифікованого програмування*** у цьому випадку полягає у

- розробці програми, що реалізує функцію `compile`;
- доведенні коректності цієї програми, тобто у побудові терма `correctness`, який має тип

```coq
forall e : expr, Some [exprDenote e] = programDenote (compile e). 
```

## Функція `compile`

Ми будемо будувати програму за допомогою функції конкатенації списків

```coq
app = fun A : Type =>
  fix app (l m : list A) {struct l} : list A :=
    match l with
      [] => m
    | a :: l1 => a :: app l1 m
    end
: forall A : Type, list A -> list A -> list A
```

зі стандартної бібліотеки `Coq.Init.Datatypes`.
Ця функція зазвичай використовується як інфіксний бінарний оператор

```coq
Infix "++" := app (right associativity, at level 60) : list_scope.
```

Ця операція є асоциативною

```coq
app_assoc
     : forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n
```

Це нам далі знадобиться.

Тепер давайте визначимо `compile` у такий спосіб

```coq
Fixpoint compile (e : expr) : program :=
  match e with
    const n => [save n]
  | term b e1 e2 => (compile e2) ++ (compile e1) ++ [eval b]
  end.
```

Інакше кажучи, вираз, що є константою `n : nat` транслюється у програму з однієї інструкції `save n`.<br/>
В той же час, вираз, що будується за допомогою конструктора `term`, компілюєтья у програму для другого операнда,
до якої доєднана програма для першого операнда, а до результату в кінець додана інструкція `eval b`, де `b` є
знаком операції в корені виразу.

Давайте відкомпілюємо вираз `eMULT_ePLUS_c2_c3_c4` (див. вище)

```coq
Example p := compile eMULT_ePLUS_c2_c3_c4.
```

Тоді отримаємо

```coq
Eval compute in p.
= [save 4; save 3; save 2; eval PLUS; eval MULT]
     : program
```

Ця програма в результаті виконання дає

```coq
Eval compute in programDenote p.
= Some [20]
     : option stack
```

## Створення сертифікату для функції `compile`

Як вже було зазначено для створення сертифікату необхідно довести таку теорему

```coq
Theorem correctness : forall e : expr,
  Some [exprDenote e] = programDenote (compile e).
```

Після виконання команди `Theorem` у вікні стану доведення отримаємо

```coq
1 subgoal
______________________________________(1/1)
forall e : expr, Some [exprDenote e] = programDenote (compile e)
```

Для доведення використовуються стандартні кроки доведення, які називають ***тактиками***.<br/>
Команда `Proof` розпочинає послідовність тактик, яка формує доведення.

```coq
Proof.
```

Перша тактика

```coq
  intro.
```

Знімає універсальний квантор, а зв'язану ним змінну переносить у контекст

```coq
1 subgoal
e : expr
______________________________________(1/1)
Some [exprDenote e] = programDenote (compile e)
```

Далі розумно вести індукцію за цією змінною, оскільки вона має індуктивний тип

```coq
  induction e.
```

Застовування тактики `induction` дає новий стан доведення

```coq
2 subgoals
n : nat
______________________________________(1/2)
Some [exprDenote (const n)] = programDenote (compile (const n))
______________________________________(2/2)
Some [exprDenote (term b e1 e2)] = programDenote (compile (term b e1 e2))
```

Як бачимо утворилося дві цілі доведення - по одній для кожного конструктора типа `expr`.<br/>
Перша з цих цілей легко реалізується за рахунок застосування спочатку тактики `unfold`, яка заміняє терм
його визначенням, а потім прямого обчислення терму.

```coq
  (* конструктор const *)
    unfold programDenote.
```

Це дає таку зміну для першої цілі

```coq
2 subgoals
n : nat
______________________________________(1/2)
Some [exprDenote (const n)] = execute (compile (const n)) []
______________________________________(2/2)
Some [exprDenote (term b e1 e2)] = programDenote (compile (term b e1 e2))
```

```coq
    simpl.
```

дає

```coq
2 subgoals
n : nat
______________________________________(1/2)
Some [n] = Some [n]
______________________________________(2/2)
Some [exprDenote (term b e1 e2)] = programDenote (compile (term b e1 e2))
```

Як ми бачимо, перша ціль є вірною рівністю, тому ми можемо завершити її доведення тактикою `reflexivity`.

```coq
    reflexivity.
```

дає

```coq
1 subgoal
b : binop
e1, e2 : expr
IHe1 : Some [exprDenote e1] = programDenote (compile e1)
IHe2 : Some [exprDenote e2] = programDenote (compile e2)
______________________________________(1/1)
Some [exprDenote (term b e1 e2)] = programDenote (compile (term b e1 e2))
```

Ми бачимо, що перша ціль зникла, а у контексті з'явилися припущення, які є вірними для доведення другої цілі.

Однак для того, щоб довести другу ціль, нам знадобиться таке допоміжне твердження.

----

```coq
Lemma seq_calc : forall (s : stack) (e : expr) (p : program),
  execute (compile e ++ p) s = execute p (exprDenote e :: s).
```

Для доведення цієї леми також використовується принцип індукції за стуктурою арифметичного виразу.

```coq
Proof.
  intros until e. revert s.
```

Маємо стан доведення

```coq
1 subgoal
e : expr
______________________________________(1/1)
forall (s : stack) (p0 : program), execute (compile e ++ p0) s = execute p0 (exprDenote e :: s)
```

Тепер застосовуємо індукцію по `e`.

```coq
  induction e.
```

Це дає

```coq
2 subgoals
n : nat
______________________________________(1/2)
forall (s : stack) (p0 : program),
execute (compile (const n) ++ p0) s = execute p0 (exprDenote (const n) :: s)
______________________________________(2/2)
forall (s : stack) (p0 : program),
execute (compile (term b e1 e2) ++ p0) s = execute p0 (exprDenote (term b e1 e2) :: s)
```

Перша ціль доводиться просто.

```coq
  (* індукція для const *) intros. simpl. reflexivity.
```

Тепер маємо

```coq
1 subgoal
b : binop
e1, e2 : expr
IHe1 : forall (s : stack) (p : program), execute (compile e1 ++ p) s = execute p (exprDenote e1 :: s)
IHe2 : forall (s : stack) (p : program), execute (compile e2 ++ p) s = execute p (exprDenote e2 :: s)
______________________________________(1/1)
forall (s : stack) (p0 : program),
execute (compile (term b e1 e2) ++ p0) s = execute p0 (exprDenote (term b e1 e2) :: s)
```

Тут слід зазначити, що `IHe1` та `IHe2` є припущеннями індукції, що виникають при застосуванні конструктора
`term`.

Застосування

```coq
    intros. simpl.
```

дає

```coq
1 subgoal
b : binop
e1, e2 : expr
IHe1 : forall (s : stack) (p : program), execute (compile e1 ++ p) s = execute p (exprDenote e1 :: s)
IHe2 : forall (s : stack) (p : program), execute (compile e2 ++ p) s = execute p (exprDenote e2 :: s)
s : stack
p0 : program
______________________________________(1/1)
execute ((compile e2 ++ compile e1 ++ [eval b]) ++ p0) s =
execute p0 (binopDenote b (exprDenote e1) (exprDenote e2) :: s)
```

Тепер замінимо праву частину леми `app_assoc` лівою

```coq
    rewrite <- app_assoc.
```

і отримаємо

```coq
1 subgoal
b : binop
e1, e2 : expr
IHe1 : forall (s : stack) (p : program), execute (compile e1 ++ p) s = execute p (exprDenote e1 :: s)
IHe2 : forall (s : stack) (p : program), execute (compile e2 ++ p) s = execute p (exprDenote e2 :: s)
s : stack
p0 : program
______________________________________(1/1)
execute (compile e2 ++ (compile e1 ++ [eval b]) ++ p0) s =
execute p0 (binopDenote b (exprDenote e1) (exprDenote e2) :: s)
```
Тепер замінемо ліву частину `IHe2` правою,

```coq
    rewrite IHe2.
```

що дасть

```coq
1 subgoal
b : binop
e1, e2 : expr
IHe1 : forall (s : stack) (p : program), execute (compile e1 ++ p) s = execute p (exprDenote e1 :: s)
IHe2 : forall (s : stack) (p : program), execute (compile e2 ++ p) s = execute p (exprDenote e2 :: s)
s : stack
p0 : program
______________________________________(1/1)
execute ((compile e1 ++ [eval b]) ++ p0) (exprDenote e2 :: s) =
execute p0 (binopDenote b (exprDenote e1) (exprDenote e2) :: s)
```

Ще раз використавши заміну за допомогою леми `app_assoc`

```coq
    rewrite <- app_assoc. simpl.
```

отримаємо

```coq
1 subgoal
b : binop
e1, e2 : expr
IHe1 : forall (s : stack) (p : program), execute (compile e1 ++ p) s = execute p (exprDenote e1 :: s)
IHe2 : forall (s : stack) (p : program), execute (compile e2 ++ p) s = execute p (exprDenote e2 :: s)
s : stack
p0 : program
______________________________________(1/1)
execute (compile e1 ++ [eval b] ++ p0) (exprDenote e2 :: s) =
execute p0 (binopDenote b (exprDenote e1) (exprDenote e2) :: s)
```

Тепер завершимо доведення, виконавши заміну за допомогою `IHe1` 

```coq
    rewrite IHe1. trivial. 
```

```coq
No more subgoals.
```

Збережемо доведення за допомогою команди

```coq
Qed.
```

----

Маючи лему `seq_calc`, доведемо другу ціль, що з'явилася в процесі доведення коректності.

```coq
  (* індукція для term *)
    simpl. unfold programDenote.
    repeat rewrite seq_calc. trivial.
Qed.
```

Таким чином, ми не тільки **розробили функцію** `compile`, яка транслює арифметичний вираз у програму стекового обчислювача,
що обчислює цей вираз, але й **створили сертифікат** `correctness` **цієї функції**, який гарантує її коректність.
