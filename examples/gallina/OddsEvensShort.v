From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module OddsEvensShort_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := Even | Odd
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

Record P_OddCommitC : Type := {
  com_c : Commitment Odd bool;
}.

Record P_EvenCommitC : Type := {
  com_c : Commitment Even bool;
}.

Record P_OddRevealC : Type := {
  c : bool;
}.

Record P_EvenRevealC : Type := {
  c : bool;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_OddCommitC  : Type := {
  sig_OddCommitC : Signed Odd P_OddCommitC;
}.

Record W_EvenCommitC  : Type := {
  sig_EvenCommitC : Signed Even P_EvenCommitC;
}.

Record W_OddRevealC (w_OddCommitC : W_OddCommitC) (w_EvenCommitC : W_EvenCommitC) : Type := {
  sig_OddRevealC : Signed Odd P_OddRevealC;
  opening_c : Opens w_OddCommitC.(sig_OddCommitC).(msg).(com_c) sig_OddRevealC.(msg).(c);
}.

Record W_EvenRevealC (w_OddCommitC : W_OddCommitC) (w_EvenCommitC : W_EvenCommitC) : Type := {
  sig_EvenRevealC : Signed Even P_EvenRevealC;
  opening_c : Opens w_EvenCommitC.(sig_EvenCommitC).(msg).(com_c) sig_EvenRevealC.(msg).(c);
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3 | S4 | S5 | S6.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_OddCommitC : W_OddCommitC) -> State S1
| st2 : (w_EvenCommitC : W_EvenCommitC) -> State S2
| st3 : (w_OddCommitC : W_OddCommitC) (w_EvenCommitC : W_EvenCommitC) -> State S3
| st4 : (w_OddCommitC : W_OddCommitC) (w_EvenCommitC : W_EvenCommitC) (w_OddRevealC : (W_OddRevealC w_OddCommitC w_EvenCommitC)) -> State S4
| st5 : (w_OddCommitC : W_OddCommitC) (w_EvenCommitC : W_EvenCommitC) (w_EvenRevealC : (W_EvenRevealC w_OddCommitC w_EvenCommitC)) -> State S5
| st6 : (w_OddCommitC : W_OddCommitC) (w_EvenCommitC : W_EvenCommitC) (w_OddRevealC : (W_OddRevealC w_OddCommitC w_EvenCommitC)) (w_EvenRevealC : (W_EvenRevealC w_OddCommitC w_EvenCommitC)) -> State S6
.

(* Step API *)
Definition step_oddcommitc_from_s0 (s : State S0) (sig : Signed Odd P_OddCommitC)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_OddCommitC := sig |}
  end.

Definition step_evencommitc_from_s0 (s : State S0) (sig : Signed Even P_EvenCommitC)
 : State S2 :=
  match s with
  | st0 =>
      st2 {| sig_EvenCommitC := sig |}
  end.

Definition step_evencommitc_from_s1 (s : State S1) (sig : Signed Even P_EvenCommitC)
 : State S3 :=
  match s with
  | st1 w_OddCommitC =>
      st3 w_OddCommitC {| sig_EvenCommitC := sig |}
  end.

Definition step_oddcommitc_from_s2 (s : State S2) (sig : Signed Odd P_OddCommitC)
 : State S3 :=
  match s with
  | st2 w_EvenCommitC =>
      st3 {| sig_OddCommitC := sig |} w_EvenCommitC
  end.

Definition step_oddrevealc_from_s3 (s : State S3) (sig : Signed Odd P_OddRevealC)

  (Hopen_c : Opens (match s with st3 w_OddCommitC w_EvenCommitC => w_OddCommitC.(sig_OddCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S4 :=
  match s with
  | st3 w_OddCommitC w_EvenCommitC =>
      st4 w_OddCommitC w_EvenCommitC {| sig_OddRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_evenrevealc_from_s3 (s : State S3) (sig : Signed Even P_EvenRevealC)

  (Hopen_c : Opens (match s with st3 w_OddCommitC w_EvenCommitC => w_EvenCommitC.(sig_EvenCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S5 :=
  match s with
  | st3 w_OddCommitC w_EvenCommitC =>
      st5 w_OddCommitC w_EvenCommitC {| sig_EvenRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_evenrevealc_from_s4 (s : State S4) (sig : Signed Even P_EvenRevealC)

  (Hopen_c : Opens (match s with st4 w_OddCommitC w_EvenCommitC w_OddRevealC => w_EvenCommitC.(sig_EvenCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S6 :=
  match s with
  | st4 w_OddCommitC w_EvenCommitC w_OddRevealC =>
      st6 w_OddCommitC w_EvenCommitC w_OddRevealC {| sig_EvenRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_oddrevealc_from_s5 (s : State S5) (sig : Signed Odd P_OddRevealC)

  (Hopen_c : Opens (match s with st5 w_OddCommitC w_EvenCommitC w_EvenRevealC => w_OddCommitC.(sig_OddCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S6 :=
  match s with
  | st5 w_OddCommitC w_EvenCommitC w_EvenRevealC =>
      st6 w_OddCommitC w_EvenCommitC {| sig_OddRevealC := sig; opening_c := Hopen_c |} w_EvenRevealC
  end.

End OddsEvensShort_Protocol.
