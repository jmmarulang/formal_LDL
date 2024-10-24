From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals ereal signed topology derive.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Check ess_sup.

Locate Probability.type. 

Check Measure.type.

Print "`| x |".

Section essential_supremum.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context d {T : semiRingOfSetsType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types f : T -> R.

Definition ess_sup f :=
  ereal_inf (EFin @` [set r | mu (f @^-1` `]r, +oo[) = 0]).

Lemma ess_sup_ge0 f : 0 < mu [set: T] -> (forall t, 0 <= f t)%R ->
  0 <= ess_sup f.
Proof.
move=> muT f0. apply: lb_ereal_inf => _ /= [r /eqP rf <-]. rewrite leNgt.
apply/negP => r0. apply/negP : rf. rewrite gt_eqF// (_ : _ @^-1` _ = setT)//.
by apply/seteqP; split => // x _ /=; rewrite in_itv/= (lt_le_trans _ (f0 x)).
Qed.

End essential_supremum.

Section extended_essential_supremum.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context d {T : semiRingOfSetsType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types f : T -> \bar R.

Definition ess_supe f :=
  ereal_inf ([set r | mu (f @^-1` `]r, +oo[) = 0]).

Lemma ess_supe_ge0 f : 0 < mu [set: T] -> (forall t, 0%E <= f t) ->
  0 <= ess_supe f.
Proof. 
  move=> H H0. apply: lb_ereal_inf. move => r /= /eqP H1. 
  case r eqn:H2; rewrite leNgt; apply/negP => r0; apply/negP : H1;
  rewrite gt_eqF// (_ : f @^-1` _ = setT)//=; (*???*)
  apply/seteqP; split => // x _ /=; rewrite in_itv/= (lt_le_trans _ (H0 x)) //.
Qed.

End extended_essential_supremum.


Section Lmean.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context 
    {d} 
    {T : measurableType d} 
    {R : realType} 
    (P : probability T R).

Definition lne (x : \bar R) :=
  match x with
  | x'%:E => (ln x')%:E
  | +oo => 1
  | -oo => 0
  end.

Definition geo_mean (g : T -> \bar R) := 
expeR (\int[P]_x (lne (g x)))%E.

Definition Lmean 
(p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => (if p == 0%R then
              geo_mean f
            else
              (\int[P]_x (`|f x| `^ p)) `^ p^-1)%E
  | +oo%E => (if P [set: T] > 0 then ess_supe P (abse \o f) else 0)%E
  | -oo%E => 0%E
  end.

End Lmean.