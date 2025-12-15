From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module Prisoners_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := A | B
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

Definition P_BJoin : Type := unit.

Record P_ACommitC : Type := {
  com_c : Commitment A bool;
}.

Record P_BCommitC : Type := {
  com_c : Commitment B bool;
}.

Record P_ARevealC : Type := {
  c : bool;
}.

Record P_BRevealC : Type := {
  c : bool;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_AJoin  : Type := {
  sig_AJoin : Signed A P_AJoin;
}.

Record W_BJoin (w_AJoin : W_AJoin) : Type := {
  sig_BJoin : Signed B P_BJoin;
}.

Record W_ACommitC (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) : Type := {
  sig_ACommitC : Signed A P_ACommitC;
}.

Record W_BCommitC (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) : Type := {
  sig_BCommitC : Signed B P_BCommitC;
}.

Record W_ARevealC (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) : Type := {
  sig_ARevealC : Signed A P_ARevealC;
  opening_c : Opens w_ACommitC.(sig_ACommitC).(msg).(com_c) sig_ARevealC.(msg).(c);
}.

Record W_BRevealC (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) : Type := {
  sig_BRevealC : Signed B P_BRevealC;
  opening_c : Opens w_BCommitC.(sig_BCommitC).(msg).(com_c) sig_BRevealC.(msg).(c);
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_AJoin : W_AJoin) -> State S1
| st2 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) -> State S2
| st3 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) -> State S3
| st4 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) -> State S4
| st5 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) -> State S5
| st6 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) (w_ARevealC : (W_ARevealC w_AJoin w_BJoin w_ACommitC w_BCommitC)) -> State S6
| st7 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) (w_BRevealC : (W_BRevealC w_AJoin w_BJoin w_ACommitC w_BCommitC)) -> State S7
| st8 : (w_AJoin : W_AJoin) (w_BJoin : (W_BJoin w_AJoin)) (w_ACommitC : (W_ACommitC w_AJoin w_BJoin)) (w_BCommitC : (W_BCommitC w_AJoin w_BJoin)) (w_ARevealC : (W_ARevealC w_AJoin w_BJoin w_ACommitC w_BCommitC)) (w_BRevealC : (W_BRevealC w_AJoin w_BJoin w_ACommitC w_BCommitC)) -> State S8
.

(* Step API *)
Definition step_ajoin_from_s0 (s : State S0) (sig : Signed A P_AJoin)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_AJoin := sig |}
  end.

Definition step_bjoin_from_s1 (s : State S1) (sig : Signed B P_BJoin)
 : State S2 :=
  match s with
  | st1 w_AJoin =>
      st2 w_AJoin {| sig_BJoin := sig |}
  end.

Definition step_acommitc_from_s2 (s : State S2) (sig : Signed A P_ACommitC)
 : State S3 :=
  match s with
  | st2 w_AJoin w_BJoin =>
      st3 w_AJoin w_BJoin {| sig_ACommitC := sig |}
  end.

Definition step_bcommitc_from_s2 (s : State S2) (sig : Signed B P_BCommitC)
 : State S4 :=
  match s with
  | st2 w_AJoin w_BJoin =>
      st4 w_AJoin w_BJoin {| sig_BCommitC := sig |}
  end.

Definition step_bcommitc_from_s3 (s : State S3) (sig : Signed B P_BCommitC)
 : State S5 :=
  match s with
  | st3 w_AJoin w_BJoin w_ACommitC =>
      st5 w_AJoin w_BJoin w_ACommitC {| sig_BCommitC := sig |}
  end.

Definition step_acommitc_from_s4 (s : State S4) (sig : Signed A P_ACommitC)
 : State S5 :=
  match s with
  | st4 w_AJoin w_BJoin w_BCommitC =>
      st5 w_AJoin w_BJoin {| sig_ACommitC := sig |} w_BCommitC
  end.

Definition step_arevealc_from_s5 (s : State S5) (sig : Signed A P_ARevealC)

  (Hopen_c : Opens (match s with st5 w_AJoin w_BJoin w_ACommitC w_BCommitC => w_ACommitC.(sig_ACommitC).(msg).(com_c) end) sig.(msg).(c)) : State S6 :=
  match s with
  | st5 w_AJoin w_BJoin w_ACommitC w_BCommitC =>
      st6 w_AJoin w_BJoin w_ACommitC w_BCommitC {| sig_ARevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_brevealc_from_s5 (s : State S5) (sig : Signed B P_BRevealC)

  (Hopen_c : Opens (match s with st5 w_AJoin w_BJoin w_ACommitC w_BCommitC => w_BCommitC.(sig_BCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S7 :=
  match s with
  | st5 w_AJoin w_BJoin w_ACommitC w_BCommitC =>
      st7 w_AJoin w_BJoin w_ACommitC w_BCommitC {| sig_BRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_brevealc_from_s6 (s : State S6) (sig : Signed B P_BRevealC)

  (Hopen_c : Opens (match s with st6 w_AJoin w_BJoin w_ACommitC w_BCommitC w_ARevealC => w_BCommitC.(sig_BCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S8 :=
  match s with
  | st6 w_AJoin w_BJoin w_ACommitC w_BCommitC w_ARevealC =>
      st8 w_AJoin w_BJoin w_ACommitC w_BCommitC w_ARevealC {| sig_BRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_arevealc_from_s7 (s : State S7) (sig : Signed A P_ARevealC)

  (Hopen_c : Opens (match s with st7 w_AJoin w_BJoin w_ACommitC w_BCommitC w_BRevealC => w_ACommitC.(sig_ACommitC).(msg).(com_c) end) sig.(msg).(c)) : State S8 :=
  match s with
  | st7 w_AJoin w_BJoin w_ACommitC w_BCommitC w_BRevealC =>
      st8 w_AJoin w_BJoin w_ACommitC w_BCommitC {| sig_ARevealC := sig; opening_c := Hopen_c |} w_BRevealC
  end.

End Prisoners_Protocol.
