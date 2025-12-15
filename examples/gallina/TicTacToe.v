From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module TicTacToe_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := O | X
Scheme Equality for Role.

Inductive Enum_0_1_2_3_4_5_6_7_8 : Type := E0 | E1 | E2 | E3 | E4 | E5 | E6 | E7 | E8.
Scheme Equality for Enum_0_1_2_3_4_5_6_7_8.

Inductive Enum_0_1_4 : Type := E0 | E1 | E4.
Scheme Equality for Enum_0_1_4.

Inductive Enum_1_3_4_5_9 : Type := E1 | E3 | E4 | E5 | E9.
Scheme Equality for Enum_1_3_4_5_9.

(* ===================== *)
(* 2) Abstract evidence  *)
(* ===================== *)

Parameter SigW : forall (r : Role) (A : Type), A -> Type.

Record Signed (r : Role) (A : Type) : Type := {
  msg : A;
  sig_ok : SigW r A msg
}.

Parameter Commitment : Role -> Type -> Type.
Parameter Opens : forall {r : Role} {A : Type}, Commitment r A -> A -> Type.

(* ===================== *)
(* 3) Action payloads    *)
(* ===================== *)

Definition P_XJoin : Type := unit.

Definition P_OJoin : Type := unit.

Record P_XMoveC1 : Type := {
  c1 : Enum_0_1_4;
}.

Record P_OMoveC1 : Type := {
  c1 : Enum_1_3_4_5_9;
}.

Record P_XMoveC2 : Type := {
  c2 : Enum_0_1_2_3_4_5_6_7_8;
}.

Record P_OMoveC2 : Type := {
  c2 : Enum_0_1_2_3_4_5_6_7_8;
}.

Record P_XMoveC3 : Type := {
  c3 : Enum_0_1_2_3_4_5_6_7_8;
}.

Record P_OMoveC3 : Type := {
  c3 : Enum_0_1_2_3_4_5_6_7_8;
}.

Record P_XMoveC4 : Type := {
  c4 : Enum_0_1_2_3_4_5_6_7_8;
}.

Record P_OMoveC4 : Type := {
  c4 : Enum_0_1_2_3_4_5_6_7_8;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_XJoin  : Type := {
  sig_XJoin : Signed X P_XJoin;
}.

Record W_OJoin (w_XJoin : W_XJoin) : Type := {
  sig_OJoin : Signed O P_OJoin;
}.

Record W_XMoveC1 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) : Type := {
  sig_XMoveC1 : Signed X P_XMoveC1;
}.

Record W_OMoveC1 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) : Type := {
  sig_OMoveC1 : Signed O P_OMoveC1;
  guard : (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_OMoveC1.(msg).(c1));
}.

Record W_XMoveC2 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) : Type := {
  sig_XMoveC2 : Signed X P_XMoveC2;
  guard : (andb (andb (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC1.(sig_OMoveC1).(msg).(c1)) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_XMoveC2.(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> sig_XMoveC2.(msg).(c2)));
}.

Record W_OMoveC2 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) : Type := {
  sig_OMoveC2 : Signed O P_OMoveC2;
  guard : (andb (andb (andb (andb (andb (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC1.(sig_OMoveC1).(msg).(c1)) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_OMoveC2.(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> sig_OMoveC2.(msg).(c2))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> sig_OMoveC2.(msg).(c2)));
}.

Record W_XMoveC3 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) : Type := {
  sig_XMoveC3 : Signed X P_XMoveC3;
  guard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC1.(sig_OMoveC1).(msg).(c1)) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_XMoveC3.(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> sig_XMoveC3.(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> sig_XMoveC3.(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> sig_XMoveC3.(msg).(c3)));
}.

Record W_OMoveC3 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) : Type := {
  sig_OMoveC3 : Signed O P_OMoveC3;
  guard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC1.(sig_OMoveC1).(msg).(c1)) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_OMoveC3.(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> sig_OMoveC3.(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> sig_OMoveC3.(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> sig_OMoveC3.(msg).(c3))) (w_XMoveC3.(sig_XMoveC3).(msg).(c3) <> sig_OMoveC3.(msg).(c3)));
}.

Record W_XMoveC4 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) (w_OMoveC3 : (W_OMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3)) : Type := {
  sig_XMoveC4 : Signed X P_XMoveC4;
  guard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC1.(sig_OMoveC1).(msg).(c1)) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_XMoveC4.(msg).(c4))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> sig_XMoveC4.(msg).(c4))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> sig_XMoveC4.(msg).(c4))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> sig_XMoveC4.(msg).(c4))) (w_XMoveC3.(sig_XMoveC3).(msg).(c3) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_XMoveC3.(sig_XMoveC3).(msg).(c3) <> sig_XMoveC4.(msg).(c4))) (w_OMoveC3.(sig_OMoveC3).(msg).(c3) <> sig_XMoveC4.(msg).(c4)));
}.

Record W_OMoveC4 (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) (w_OMoveC3 : (W_OMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3)) (w_XMoveC4 : (W_XMoveC4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3)) : Type := {
  sig_OMoveC4 : Signed O P_OMoveC4;
  guard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC1.(sig_OMoveC1).(msg).(c1)) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> w_XMoveC4.(sig_XMoveC4).(msg).(c4))) (w_XMoveC1.(sig_XMoveC1).(msg).(c1) <> sig_OMoveC4.(msg).(c4))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC2.(sig_XMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> w_XMoveC4.(sig_XMoveC4).(msg).(c4))) (w_OMoveC1.(sig_OMoveC1).(msg).(c1) <> sig_OMoveC4.(msg).(c4))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_OMoveC2.(sig_OMoveC2).(msg).(c2))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> w_XMoveC4.(sig_XMoveC4).(msg).(c4))) (w_XMoveC2.(sig_XMoveC2).(msg).(c2) <> sig_OMoveC4.(msg).(c4))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> w_XMoveC3.(sig_XMoveC3).(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> w_XMoveC4.(sig_XMoveC4).(msg).(c4))) (w_OMoveC2.(sig_OMoveC2).(msg).(c2) <> sig_OMoveC4.(msg).(c4))) (w_XMoveC3.(sig_XMoveC3).(msg).(c3) <> w_OMoveC3.(sig_OMoveC3).(msg).(c3))) (w_XMoveC3.(sig_XMoveC3).(msg).(c3) <> w_XMoveC4.(sig_XMoveC4).(msg).(c4))) (w_XMoveC3.(sig_XMoveC3).(msg).(c3) <> sig_OMoveC4.(msg).(c4))) (w_OMoveC3.(sig_OMoveC3).(msg).(c3) <> w_XMoveC4.(sig_XMoveC4).(msg).(c4))) (w_OMoveC3.(sig_OMoveC3).(msg).(c3) <> sig_OMoveC4.(msg).(c4))) (w_XMoveC4.(sig_XMoveC4).(msg).(c4) <> sig_OMoveC4.(msg).(c4)));
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | S10.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_XJoin : W_XJoin) -> State S1
| st2 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) -> State S2
| st3 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) -> State S3
| st4 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) -> State S4
| st5 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) -> State S5
| st6 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) -> State S6
| st7 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) -> State S7
| st8 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) (w_OMoveC3 : (W_OMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3)) -> State S8
| st9 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) (w_OMoveC3 : (W_OMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3)) (w_XMoveC4 : (W_XMoveC4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3)) -> State S9
| st10 : (w_XJoin : W_XJoin) (w_OJoin : (W_OJoin w_XJoin)) (w_XMoveC1 : (W_XMoveC1 w_XJoin w_OJoin)) (w_OMoveC1 : (W_OMoveC1 w_XJoin w_OJoin w_XMoveC1)) (w_XMoveC2 : (W_XMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1)) (w_OMoveC2 : (W_OMoveC2 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2)) (w_XMoveC3 : (W_XMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2)) (w_OMoveC3 : (W_OMoveC3 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3)) (w_XMoveC4 : (W_XMoveC4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3)) (w_OMoveC4 : (W_OMoveC4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4)) -> State S10
.

(* Step API *)
Definition step_xjoin_from_s0 (s : State S0) (sig : Signed X P_XJoin)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_XJoin := sig |}
  end.

Definition step_ojoin_from_s1 (s : State S1) (sig : Signed O P_OJoin)
 : State S2 :=
  match s with
  | st1 w_XJoin =>
      st2 w_XJoin {| sig_OJoin := sig |}
  end.

Definition step_xmovec1_from_s2 (s : State S2) (sig : Signed X P_XMoveC1)
 : State S3 :=
  match s with
  | st2 w_XJoin w_OJoin =>
      st3 w_XJoin w_OJoin {| sig_XMoveC1 := sig |}
  end.

Definition step_omovec1_from_s3 (s : State S3) (sig : Signed O P_OMoveC1)
  (Hguard : ((match s with st3 w_XJoin w_OJoin w_XMoveC1 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c1))) : State S4 :=
  match s with
  | st3 w_XJoin w_OJoin w_XMoveC1 =>
      st4 w_XJoin w_OJoin w_XMoveC1 {| sig_OMoveC1 := sig; guard := Hguard |}
  end.

Definition step_xmovec2_from_s4 (s : State S4) (sig : Signed X P_XMoveC2)
  (Hguard : (andb (andb ((match s with st4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end)) ((match s with st4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c2))) ((match s with st4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> sig.(msg).(c2)))) : State S5 :=
  match s with
  | st4 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 =>
      st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 {| sig_XMoveC2 := sig; guard := Hguard |}
  end.

Definition step_omovec2_from_s5 (s : State S5) (sig : Signed O P_OMoveC2)
  (Hguard : (andb (andb (andb (andb (andb ((match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end)) ((match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c2))) ((match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> sig.(msg).(c2))) ((match s with st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> sig.(msg).(c2)))) : State S6 :=
  match s with
  | st5 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 =>
      st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 {| sig_OMoveC2 := sig; guard := Hguard |}
  end.

Definition step_xmovec3_from_s6 (s : State S6) (sig : Signed X P_XMoveC3)
  (Hguard : (andb (andb (andb (andb (andb (andb (andb (andb (andb ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end)) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c3))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> sig.(msg).(c3))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> sig.(msg).(c3))) ((match s with st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> sig.(msg).(c3)))) : State S7 :=
  match s with
  | st6 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 =>
      st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 {| sig_XMoveC3 := sig; guard := Hguard |}
  end.

Definition step_omovec3_from_s7 (s : State S7) (sig : Signed O P_OMoveC3)
  (Hguard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end)) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c3))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> sig.(msg).(c3))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> sig.(msg).(c3))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> (match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> sig.(msg).(c3))) ((match s with st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end) <> sig.(msg).(c3)))) : State S8 :=
  match s with
  | st7 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 =>
      st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 {| sig_OMoveC3 := sig; guard := Hguard |}
  end.

Definition step_xmovec4_from_s8 (s : State S8) (sig : Signed X P_XMoveC4)
  (Hguard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end)) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c4))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> sig.(msg).(c4))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> sig.(msg).(c4))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> sig.(msg).(c4))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end) <> (match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end) <> sig.(msg).(c4))) ((match s with st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end) <> sig.(msg).(c4)))) : State S9 :=
  match s with
  | st8 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 =>
      st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 {| sig_XMoveC4 := sig; guard := Hguard |}
  end.

Definition step_omovec4_from_s9 (s : State S9) (sig : Signed O P_OMoveC4)
  (Hguard : (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb (andb ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end)) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC1.(sig_XMoveC1).(msg).(c1) end) <> sig.(msg).(c4))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC1.(sig_OMoveC1).(msg).(c1) end) <> sig.(msg).(c4))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC2.(sig_XMoveC2).(msg).(c2) end) <> sig.(msg).(c4))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC2.(sig_OMoveC2).(msg).(c2) end) <> sig.(msg).(c4))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC3.(sig_XMoveC3).(msg).(c3) end) <> sig.(msg).(c4))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end) <> (match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_OMoveC3.(sig_OMoveC3).(msg).(c3) end) <> sig.(msg).(c4))) ((match s with st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 => w_XMoveC4.(sig_XMoveC4).(msg).(c4) end) <> sig.(msg).(c4)))) : State S10 :=
  match s with
  | st9 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 =>
      st10 w_XJoin w_OJoin w_XMoveC1 w_OMoveC1 w_XMoveC2 w_OMoveC2 w_XMoveC3 w_OMoveC3 w_XMoveC4 {| sig_OMoveC4 := sig; guard := Hguard |}
  end.

End TicTacToe_Protocol.
