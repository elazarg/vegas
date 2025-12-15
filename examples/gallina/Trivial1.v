From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module Trivial1_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := A
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

Definition P_AJoin : Type := unit.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_AJoin  : Type := {
  sig_AJoin : Signed A P_AJoin;
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_AJoin : W_AJoin) -> State S1
.

(* Step API *)
Definition step_ajoin_from_s0 (s : State S0) (sig : Signed A P_AJoin)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_AJoin := sig |}
  end.

End Trivial1_Protocol.
