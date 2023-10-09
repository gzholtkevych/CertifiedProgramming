Require Import Lists.List.
Import ListNotations.

Inductive type : Set := NAT | BOOL.

Inductive opSig : Set :=
  op1 : type -> type -> opSig                |
  op2 : type -> type -> type -> opSig        |
  op3 : type -> type -> type -> type -> opSig.

Inductive opSymb : opSig -> Set :=
  NOT : opSymb (op1 BOOL BOOL)                  |
  AND : opSymb (op2 BOOL BOOL BOOL)             |
  OR  : opSymb (op2 BOOL BOOL BOOL)             |
  ADD : opSymb (op2 NAT NAT NAT)                |
  MLT : opSymb (op2 NAT NAT NAT)                |
  LT  : opSymb (op2 NAT NAT BOOL)               |
  EQ  : forall t : type, opSymb (op2 t t BOOL)  |
  ITE : forall t : type, opSymb (op3 BOOL t t t).


