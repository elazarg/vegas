From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module ThreeWayLotteryShort_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := Alice | Bob | Issuer
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

Record P_IssuerCommitC : Type := {
  com_c : Commitment Issuer Enum_1_2_3;
}.

Record P_AliceCommitC : Type := {
  com_c : Commitment Alice Enum_1_2_3;
}.

Record P_BobCommitC : Type := {
  com_c : Commitment Bob Enum_1_2_3;
}.

Record P_IssuerRevealC : Type := {
  c : Enum_1_2_3;
}.

Record P_AliceRevealC : Type := {
  c : Enum_1_2_3;
}.

Record P_BobRevealC : Type := {
  c : Enum_1_2_3;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_IssuerCommitC  : Type := {
  sig_IssuerCommitC : Signed Issuer P_IssuerCommitC;
}.

Record W_AliceCommitC  : Type := {
  sig_AliceCommitC : Signed Alice P_AliceCommitC;
}.

Record W_BobCommitC  : Type := {
  sig_BobCommitC : Signed Bob P_BobCommitC;
}.

Record W_IssuerRevealC (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) : Type := {
  sig_IssuerRevealC : Signed Issuer P_IssuerRevealC;
  opening_c : Opens w_IssuerCommitC.(sig_IssuerCommitC).(msg).(com_c) sig_IssuerRevealC.(msg).(c);
}.

Record W_AliceRevealC (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) : Type := {
  sig_AliceRevealC : Signed Alice P_AliceRevealC;
  opening_c : Opens w_AliceCommitC.(sig_AliceCommitC).(msg).(com_c) sig_AliceRevealC.(msg).(c);
}.

Record W_BobRevealC (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) : Type := {
  sig_BobRevealC : Signed Bob P_BobRevealC;
  opening_c : Opens w_BobCommitC.(sig_BobCommitC).(msg).(com_c) sig_BobRevealC.(msg).(c);
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | S10 | S11 | S12 | S13 | S14.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_IssuerCommitC : W_IssuerCommitC) -> State S1
| st2 : (w_AliceCommitC : W_AliceCommitC) -> State S2
| st3 : (w_BobCommitC : W_BobCommitC) -> State S3
| st4 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) -> State S4
| st5 : (w_IssuerCommitC : W_IssuerCommitC) (w_BobCommitC : W_BobCommitC) -> State S5
| st6 : (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) -> State S6
| st7 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) -> State S7
| st8 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_IssuerRevealC : (W_IssuerRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S8
| st9 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_AliceRevealC : (W_AliceRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S9
| st10 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_BobRevealC : (W_BobRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S10
| st11 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_IssuerRevealC : (W_IssuerRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) (w_AliceRevealC : (W_AliceRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S11
| st12 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_IssuerRevealC : (W_IssuerRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) (w_BobRevealC : (W_BobRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S12
| st13 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_AliceRevealC : (W_AliceRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) (w_BobRevealC : (W_BobRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S13
| st14 : (w_IssuerCommitC : W_IssuerCommitC) (w_AliceCommitC : W_AliceCommitC) (w_BobCommitC : W_BobCommitC) (w_IssuerRevealC : (W_IssuerRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) (w_AliceRevealC : (W_AliceRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) (w_BobRevealC : (W_BobRevealC w_IssuerCommitC w_AliceCommitC w_BobCommitC)) -> State S14
.

(* Step API *)
Definition step_issuercommitc_from_s0 (s : State S0) (sig : Signed Issuer P_IssuerCommitC)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_IssuerCommitC := sig |}
  end.

Definition step_alicecommitc_from_s0 (s : State S0) (sig : Signed Alice P_AliceCommitC)
 : State S2 :=
  match s with
  | st0 =>
      st2 {| sig_AliceCommitC := sig |}
  end.

Definition step_bobcommitc_from_s0 (s : State S0) (sig : Signed Bob P_BobCommitC)
 : State S3 :=
  match s with
  | st0 =>
      st3 {| sig_BobCommitC := sig |}
  end.

Definition step_alicecommitc_from_s1 (s : State S1) (sig : Signed Alice P_AliceCommitC)
 : State S4 :=
  match s with
  | st1 w_IssuerCommitC =>
      st4 w_IssuerCommitC {| sig_AliceCommitC := sig |}
  end.

Definition step_bobcommitc_from_s1 (s : State S1) (sig : Signed Bob P_BobCommitC)
 : State S5 :=
  match s with
  | st1 w_IssuerCommitC =>
      st5 w_IssuerCommitC {| sig_BobCommitC := sig |}
  end.

Definition step_issuercommitc_from_s2 (s : State S2) (sig : Signed Issuer P_IssuerCommitC)
 : State S4 :=
  match s with
  | st2 w_AliceCommitC =>
      st4 {| sig_IssuerCommitC := sig |} w_AliceCommitC
  end.

Definition step_bobcommitc_from_s2 (s : State S2) (sig : Signed Bob P_BobCommitC)
 : State S6 :=
  match s with
  | st2 w_AliceCommitC =>
      st6 w_AliceCommitC {| sig_BobCommitC := sig |}
  end.

Definition step_issuercommitc_from_s3 (s : State S3) (sig : Signed Issuer P_IssuerCommitC)
 : State S5 :=
  match s with
  | st3 w_BobCommitC =>
      st5 {| sig_IssuerCommitC := sig |} w_BobCommitC
  end.

Definition step_alicecommitc_from_s3 (s : State S3) (sig : Signed Alice P_AliceCommitC)
 : State S6 :=
  match s with
  | st3 w_BobCommitC =>
      st6 {| sig_AliceCommitC := sig |} w_BobCommitC
  end.

Definition step_bobcommitc_from_s4 (s : State S4) (sig : Signed Bob P_BobCommitC)
 : State S7 :=
  match s with
  | st4 w_IssuerCommitC w_AliceCommitC =>
      st7 w_IssuerCommitC w_AliceCommitC {| sig_BobCommitC := sig |}
  end.

Definition step_alicecommitc_from_s5 (s : State S5) (sig : Signed Alice P_AliceCommitC)
 : State S7 :=
  match s with
  | st5 w_IssuerCommitC w_BobCommitC =>
      st7 w_IssuerCommitC {| sig_AliceCommitC := sig |} w_BobCommitC
  end.

Definition step_issuercommitc_from_s6 (s : State S6) (sig : Signed Issuer P_IssuerCommitC)
 : State S7 :=
  match s with
  | st6 w_AliceCommitC w_BobCommitC =>
      st7 {| sig_IssuerCommitC := sig |} w_AliceCommitC w_BobCommitC
  end.

Definition step_issuerrevealc_from_s7 (s : State S7) (sig : Signed Issuer P_IssuerRevealC)

  (Hopen_c : Opens (match s with st7 w_IssuerCommitC w_AliceCommitC w_BobCommitC => w_IssuerCommitC.(sig_IssuerCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S8 :=
  match s with
  | st7 w_IssuerCommitC w_AliceCommitC w_BobCommitC =>
      st8 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_IssuerRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_alicerevealc_from_s7 (s : State S7) (sig : Signed Alice P_AliceRevealC)

  (Hopen_c : Opens (match s with st7 w_IssuerCommitC w_AliceCommitC w_BobCommitC => w_AliceCommitC.(sig_AliceCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S9 :=
  match s with
  | st7 w_IssuerCommitC w_AliceCommitC w_BobCommitC =>
      st9 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_AliceRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_bobrevealc_from_s7 (s : State S7) (sig : Signed Bob P_BobRevealC)

  (Hopen_c : Opens (match s with st7 w_IssuerCommitC w_AliceCommitC w_BobCommitC => w_BobCommitC.(sig_BobCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S10 :=
  match s with
  | st7 w_IssuerCommitC w_AliceCommitC w_BobCommitC =>
      st10 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_BobRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_alicerevealc_from_s8 (s : State S8) (sig : Signed Alice P_AliceRevealC)

  (Hopen_c : Opens (match s with st8 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC => w_AliceCommitC.(sig_AliceCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S11 :=
  match s with
  | st8 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC =>
      st11 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC {| sig_AliceRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_bobrevealc_from_s8 (s : State S8) (sig : Signed Bob P_BobRevealC)

  (Hopen_c : Opens (match s with st8 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC => w_BobCommitC.(sig_BobCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S12 :=
  match s with
  | st8 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC =>
      st12 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC {| sig_BobRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_issuerrevealc_from_s9 (s : State S9) (sig : Signed Issuer P_IssuerRevealC)

  (Hopen_c : Opens (match s with st9 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC => w_IssuerCommitC.(sig_IssuerCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S11 :=
  match s with
  | st9 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC =>
      st11 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_IssuerRevealC := sig; opening_c := Hopen_c |} w_AliceRevealC
  end.

Definition step_bobrevealc_from_s9 (s : State S9) (sig : Signed Bob P_BobRevealC)

  (Hopen_c : Opens (match s with st9 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC => w_BobCommitC.(sig_BobCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S13 :=
  match s with
  | st9 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC =>
      st13 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC {| sig_BobRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_issuerrevealc_from_s10 (s : State S10) (sig : Signed Issuer P_IssuerRevealC)

  (Hopen_c : Opens (match s with st10 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_BobRevealC => w_IssuerCommitC.(sig_IssuerCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S12 :=
  match s with
  | st10 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_BobRevealC =>
      st12 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_IssuerRevealC := sig; opening_c := Hopen_c |} w_BobRevealC
  end.

Definition step_alicerevealc_from_s10 (s : State S10) (sig : Signed Alice P_AliceRevealC)

  (Hopen_c : Opens (match s with st10 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_BobRevealC => w_AliceCommitC.(sig_AliceCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S13 :=
  match s with
  | st10 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_BobRevealC =>
      st13 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_AliceRevealC := sig; opening_c := Hopen_c |} w_BobRevealC
  end.

Definition step_bobrevealc_from_s11 (s : State S11) (sig : Signed Bob P_BobRevealC)

  (Hopen_c : Opens (match s with st11 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC w_AliceRevealC => w_BobCommitC.(sig_BobCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S14 :=
  match s with
  | st11 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC w_AliceRevealC =>
      st14 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC w_AliceRevealC {| sig_BobRevealC := sig; opening_c := Hopen_c |}
  end.

Definition step_alicerevealc_from_s12 (s : State S12) (sig : Signed Alice P_AliceRevealC)

  (Hopen_c : Opens (match s with st12 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC w_BobRevealC => w_AliceCommitC.(sig_AliceCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S14 :=
  match s with
  | st12 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC w_BobRevealC =>
      st14 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_IssuerRevealC {| sig_AliceRevealC := sig; opening_c := Hopen_c |} w_BobRevealC
  end.

Definition step_issuerrevealc_from_s13 (s : State S13) (sig : Signed Issuer P_IssuerRevealC)

  (Hopen_c : Opens (match s with st13 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC w_BobRevealC => w_IssuerCommitC.(sig_IssuerCommitC).(msg).(com_c) end) sig.(msg).(c)) : State S14 :=
  match s with
  | st13 w_IssuerCommitC w_AliceCommitC w_BobCommitC w_AliceRevealC w_BobRevealC =>
      st14 w_IssuerCommitC w_AliceCommitC w_BobCommitC {| sig_IssuerRevealC := sig; opening_c := Hopen_c |} w_AliceRevealC w_BobRevealC
  end.

End ThreeWayLotteryShort_Protocol.
