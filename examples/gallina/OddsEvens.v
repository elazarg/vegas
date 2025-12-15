From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module OddsEvens_Protocol.

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

Definition P_OddJoin : Type := unit.

Definition P_EvenJoin : Type := unit.

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

Record W_OddJoin  : Type := {
  sig_OddJoin : Signed Odd P_OddJoin;
}.

Record W_EvenJoin  : Type := {
  sig_EvenJoin : Signed Even P_EvenJoin;
}.

Record W_OddCommitC (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) : Type := {
  sig_OddCommitC : Signed Odd P_OddCommitC;
}.

Record W_EvenCommitC (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) : Type := {
  sig_EvenCommitC : Signed Even P_EvenCommitC;
}.

Record W_OddRevealC (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) : Type := {
  sig_OddRevealC : Signed Odd P_OddRevealC;
  opening_c : Opens w_OddCommitC.(sig_OddCommitC).(msg).(com_c) sig_OddRevealC.(msg).(c);
}.

Record W_EvenRevealC (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) : Type := {
  sig_EvenRevealC : Signed Even P_EvenRevealC;
  opening_c : Opens w_EvenCommitC.(sig_EvenCommitC).(msg).(com_c) sig_EvenRevealC.(msg).(c);
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_OddJoin : W_OddJoin) -> State S1
| st2 : (w_EvenJoin : W_EvenJoin) -> State S2
| st3 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) -> State S3
| st4 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) -> State S4
| st5 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) -> State S5
| st6 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) -> State S6
| st7 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) (w_OddRevealC : (W_OddRevealC w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC)) -> State S7
| st8 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) (w_EvenRevealC : (W_EvenRevealC w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC)) -> State S8
| st9 : (w_OddJoin : W_OddJoin) (w_EvenJoin : W_EvenJoin) (w_OddCommitC : (W_OddCommitC w_OddJoin w_EvenJoin)) (w_EvenCommitC : (W_EvenCommitC w_OddJoin w_EvenJoin)) (w_OddRevealC : (W_OddRevealC w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC)) (w_EvenRevealC : (W_EvenRevealC w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC)) -> State S9
.

(* Step API *)
Definition step_oddjoin_from_s0 (s : State S0) (sig : Signed Odd P_OddJoin)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_OddJoin := sig |}
  end.

Definition step_evenjoin_from_s0 (s : State S0) (sig : Signed Even P_EvenJoin)
 : State S2 :=
  match s with
  | st0 =>
      st2 {| sig_EvenJoin := sig |}
  end.

Definition step_evenjoin_from_s1 (s : State S1) (sig : Signed Even P_EvenJoin)
 : State S3 :=
  match s with
  | st1 w_OddJoin =>
      st3 w_OddJoin {| sig_EvenJoin := sig |}
  end.

Definition step_oddjoin_from_s2 (s : State S2) (sig : Signed Odd P_OddJoin)
 : State S3 :=
  match s with
  | st2 w_EvenJoin =>
      st3 {| sig_OddJoin := sig |} w_EvenJoin
  end.

Definition step_oddcommitc_from_s3 (s : State S3) (sig : Signed Odd P_OddCommitC)
 : State S4 :=
  match s with
  | st3 w_OddJoin w_EvenJoin =>
      st4 w_OddJoin w_EvenJoin {| sig_OddCommitC := sig |}
  end.

Definition step_evencommitc_from_s3 (s : State S3) (sig : Signed Even P_EvenCommitC)
 : State S5 :=
  match s with
  | st3 w_OddJoin w_EvenJoin =>
      st5 w_OddJoin w_EvenJoin {| sig_EvenCommitC := sig |}
  end.

Definition step_evencommitc_from_s4 (s : State S4) (sig : Signed Even P_EvenCommitC)
 : State S6 :=
  match s with
  | st4 w_OddJoin w_EvenJoin w_OddCommitC =>
      st6 w_OddJoin w_EvenJoin w_OddCommitC {| sig_EvenCommitC := sig |}
  end.

Definition step_oddcommitc_from_s5 (s : State S5) (sig : Signed Odd P_OddCommitC)
 : State S6 :=
  match s with
  | st5 w_OddJoin w_EvenJoin w_EvenCommitC =>
      st6 w_OddJoin w_EvenJoin {| sig_OddCommitC := sig |} w_EvenCommitC
  end.

Definition step_oddrevealc_from_s6 (s : State S6) (sig : Signed Odd P_OddRevealC)

  (Hopen_c : Opens (match s with st6 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC => w_OddCommitC.(sig_OddCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S7 :=
  match s with
  | st6 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC =>
      st7 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC {| sig_OddRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_evenrevealc_from_s6 (s : State S6) (sig : Signed Even P_EvenRevealC)

  (Hopen_c : Opens (match s with st6 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC => w_EvenCommitC.(sig_EvenCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S8 :=
  match s with
  | st6 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC =>
      st8 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC {| sig_EvenRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_evenrevealc_from_s7 (s : State S7) (sig : Signed Even P_EvenRevealC)

  (Hopen_c : Opens (match s with st7 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC w_OddRevealC => w_EvenCommitC.(sig_EvenCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S9 :=
  match s with
  | st7 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC w_OddRevealC =>
      st9 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC w_OddRevealC {| sig_EvenRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_oddrevealc_from_s8 (s : State S8) (sig : Signed Odd P_OddRevealC)

  (Hopen_c : Opens (match s with st8 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC w_EvenRevealC => w_OddCommitC.(sig_OddCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S9 :=
  match s with
  | st8 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC w_EvenRevealC =>
      st9 w_OddJoin w_EvenJoin w_OddCommitC w_EvenCommitC {| sig_OddRevealC := sig; opening_c := Hopen_c |} w_EvenRevealC
  end.

End OddsEvens_Protocol.
