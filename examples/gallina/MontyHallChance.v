From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module MontyHallChance_Protocol.

(* ===================== *)
(* 1) Roles, Types       *)
(* ===================== *)

Inductive Role : Type := Guest
Scheme Equality for Role.

Inductive Enum_0_1_2 : Type := E0 | E1 | E2.
Scheme Equality for Enum_0_1_2.

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

Definition P_HostJoin : Type := unit.

Definition P_GuestJoin : Type := unit.

Record P_HostCommitCar : Type := {
  com_car : Commitment Host Enum_0_1_2;
}.

Record P_GuestMoveD : Type := {
  d : Enum_0_1_2;
}.

Record P_HostMoveGoat : Type := {
  goat : Enum_0_1_2;
}.

Record P_GuestMoveSwitch : Type := {
  switch : bool;
}.

Record P_HostRevealCar : Type := {
  car : Enum_0_1_2;
}.

(* ===================== *)
(* 4) Witnesses          *)
(* ===================== *)

Record W_HostJoin  : Type := {
  sig_HostJoin : Signed Host P_HostJoin;
}.

Record W_GuestJoin (w_HostJoin : W_HostJoin) : Type := {
  sig_GuestJoin : Signed Guest P_GuestJoin;
}.

Record W_HostCommitCar (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) : Type := {
  sig_HostCommitCar : Signed Host P_HostCommitCar;
}.

Record W_GuestMoveD (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) : Type := {
  sig_GuestMoveD : Signed Guest P_GuestMoveD;
}.

Record W_HostMoveGoat (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) : Type := {
  sig_HostMoveGoat : Signed Host P_HostMoveGoat;
  guard : (andb (sig_HostMoveGoat.(msg).(goat) <> w_GuestMoveD.(sig_GuestMoveD).(msg).(d)) (sig_HostMoveGoat.(msg).(goat) <> w_HostRevealCar.(sig_HostRevealCar).(msg).(car)));
}.

Record W_GuestMoveSwitch (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) (w_HostMoveGoat : (W_HostMoveGoat w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD)) : Type := {
  sig_GuestMoveSwitch : Signed Guest P_GuestMoveSwitch;
}.

Record W_HostRevealCar (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) (w_HostMoveGoat : (W_HostMoveGoat w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD)) (w_GuestMoveSwitch : (W_GuestMoveSwitch w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat)) : Type := {
  sig_HostRevealCar : Signed Host P_HostRevealCar;
  opening_car : Opens w_HostCommitCar.(sig_HostCommitCar).(msg).(com_car) sig_HostRevealCar.(msg).(car);
}.

(* ===================== *)
(* 5) Typed runtime/ESM  *)
(* ===================== *)

Inductive Stage : Type :=
S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7.

Inductive State : Stage -> Type :=
| st0 : State S0
| st1 : (w_HostJoin : W_HostJoin) -> State S1
| st2 : (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) -> State S2
| st3 : (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) -> State S3
| st4 : (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) -> State S4
| st5 : (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) (w_HostMoveGoat : (W_HostMoveGoat w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD)) -> State S5
| st6 : (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) (w_HostMoveGoat : (W_HostMoveGoat w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD)) (w_GuestMoveSwitch : (W_GuestMoveSwitch w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat)) -> State S6
| st7 : (w_HostJoin : W_HostJoin) (w_GuestJoin : (W_GuestJoin w_HostJoin)) (w_HostCommitCar : (W_HostCommitCar w_HostJoin w_GuestJoin)) (w_GuestMoveD : (W_GuestMoveD w_HostJoin w_GuestJoin w_HostCommitCar)) (w_HostMoveGoat : (W_HostMoveGoat w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD)) (w_GuestMoveSwitch : (W_GuestMoveSwitch w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat)) (w_HostRevealCar : (W_HostRevealCar w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat w_GuestMoveSwitch)) -> State S7
.

(* Step API *)
Definition step_hostjoin_from_s0 (s : State S0) (sig : Signed Host P_HostJoin)
 : State S1 :=
  match s with
  | st0 =>
      st1 {| sig_HostJoin := sig |}
  end.

Definition step_guestjoin_from_s1 (s : State S1) (sig : Signed Guest P_GuestJoin)
 : State S2 :=
  match s with
  | st1 w_HostJoin =>
      st2 w_HostJoin {| sig_GuestJoin := sig |}
  end.

Definition step_hostcommitcar_from_s2 (s : State S2) (sig : Signed Host P_HostCommitCar)
 : State S3 :=
  match s with
  | st2 w_HostJoin w_GuestJoin =>
      st3 w_HostJoin w_GuestJoin {| sig_HostCommitCar := sig |}
  end.

Definition step_guestmoved_from_s3 (s : State S3) (sig : Signed Guest P_GuestMoveD)
 : State S4 :=
  match s with
  | st3 w_HostJoin w_GuestJoin w_HostCommitCar =>
      st4 w_HostJoin w_GuestJoin w_HostCommitCar {| sig_GuestMoveD := sig |}
  end.

Definition step_hostmovegoat_from_s4 (s : State S4) (sig : Signed Host P_HostMoveGoat)
  (Hguard : (andb (sig.(msg).(goat) <> (match s with st4 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD => w_GuestMoveD.(sig_GuestMoveD).(msg).(d) end)) (sig.(msg).(goat) <> true (* future/hidden field Host.car *)))) : State S5 :=
  match s with
  | st4 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD =>
      st5 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD {| sig_HostMoveGoat := sig; guard := Hguard |}
  end.

Definition step_guestmoveswitch_from_s5 (s : State S5) (sig : Signed Guest P_GuestMoveSwitch)
 : State S6 :=
  match s with
  | st5 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat =>
      st6 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat {| sig_GuestMoveSwitch := sig |}
  end.

Definition step_hostrevealcar_from_s6 (s : State S6) (sig : Signed Host P_HostRevealCar)

  (Hopen_car : Opens (match s with st6 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat w_GuestMoveSwitch => w_HostCommitCar.(sig_HostCommitCar).(msg).(com_car) end) sig.(msg).(car)) : State S7 :=
  match s with
  | st6 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat w_GuestMoveSwitch =>
      st7 w_HostJoin w_GuestJoin w_HostCommitCar w_GuestMoveD w_HostMoveGoat w_GuestMoveSwitch {| sig_HostRevealCar := sig; opening_car := Hopen_car |}
  end.

End MontyHallChance_Protocol.
