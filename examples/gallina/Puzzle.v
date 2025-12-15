From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module Puzzle_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := A | Q
Scheme Equality for Role.

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

Record P_QJoinX : Type := {
  x : Z;
}.

Record P_AJoinPQ : Type := {
  p : Z;
  q : Z;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_QJoinX  : Type := {
  sig_QJoinX : Signed Q P_QJoinX;
}.

Record W_AJoinPQ (w_QJoinX : W_QJoinX) : Type := {
  sig_AJoinPQ : Signed A P_AJoinPQ;
  guard : (andb (andb (true (* expr not supported yet: Mul(l=Field(field=A.p), r=Field(field=A.q)) *) = w_QJoinX.(sig_QJoinX).(msg).(x)) (sig_AJoinPQ.(msg).(p) <> 1%Z)) (sig_AJoinPQ.(msg).(q) <> 1%Z));
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_QJoinX : W_QJoinX) -> State S1
| st2 : (w_QJoinX : W_QJoinX) (w_AJoinPQ : (W_AJoinPQ w_QJoinX)) -> State S2
.

(* Step API *)
Definition step_qjoinx_from_s0 (s : State S0) (sig : Signed Q P_QJoinX)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_QJoinX := sig |}
  end.

Definition step_ajoinpq_from_s1 (s : State S1) (sig : Signed A P_AJoinPQ)
  (Hguard : (andb (andb (true = (match s with st1 w_QJoinX => w_QJoinX.(sig_QJoinX).(msg).(x) end)) (sig.(msg).(p) <> 1%Z)) (sig.(msg).(q) <> 1%Z))) : State S2 :=
  match s with
  | st1 w_QJoinX =>
      st2 w_QJoinX {| sig_AJoinPQ := sig; guard := Hguard |}
  end.

End Puzzle_Protocol.
