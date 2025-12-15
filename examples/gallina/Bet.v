From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module Bet_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := Gambler
Scheme Equality for Role.

Inductive Enum_1_2_3 : Type := E1 | E2 | E3.
Scheme Equality for Enum_1_2_3.

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

Definition P_RaceJoin : Type := unit.

Record P_GamblerJoinBet : Type := {
  bet : Enum_1_2_3;
}.

Record P_RaceMoveWinner : Type := {
  winner : Enum_1_2_3;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_RaceJoin  : Type := {
  sig_RaceJoin : Signed Race P_RaceJoin;
}.

Record W_GamblerJoinBet (w_RaceJoin : W_RaceJoin) : Type := {
  sig_GamblerJoinBet : Signed Gambler P_GamblerJoinBet;
}.

Record W_RaceMoveWinner (w_RaceJoin : W_RaceJoin) (w_GamblerJoinBet : (W_GamblerJoinBet w_RaceJoin)) : Type := {
  sig_RaceMoveWinner : Signed Race P_RaceMoveWinner;
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_RaceJoin : W_RaceJoin) -> State S1
| st2 : (w_RaceJoin : W_RaceJoin) (w_GamblerJoinBet : (W_GamblerJoinBet w_RaceJoin)) -> State S2
| st3 : (w_RaceJoin : W_RaceJoin) (w_GamblerJoinBet : (W_GamblerJoinBet w_RaceJoin)) (w_RaceMoveWinner : (W_RaceMoveWinner w_RaceJoin w_GamblerJoinBet)) -> State S3
.

(* Step API *)
Definition step_racejoin_from_s0 (s : State S0) (sig : Signed Race P_RaceJoin)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_RaceJoin := sig |}
  end.

Definition step_gamblerjoinbet_from_s1 (s : State S1) (sig : Signed Gambler P_GamblerJoinBet)
 : State S2 :=
  match s with
  | st1 w_RaceJoin =>
      st2 w_RaceJoin {| sig_GamblerJoinBet := sig |}
  end.

Definition step_racemovewinner_from_s2 (s : State S2) (sig : Signed Race P_RaceMoveWinner)
 : State S3 :=
  match s with
  | st2 w_RaceJoin w_GamblerJoinBet =>
      st3 w_RaceJoin w_GamblerJoinBet {| sig_RaceMoveWinner := sig |}
  end.

End Bet_Protocol.
