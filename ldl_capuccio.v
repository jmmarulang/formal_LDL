From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
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

Reserved Notation "{[ e ]}" (format "{[  e  ]}").
Reserved Notation "[[ e ]]_B" (at level 10, format "[[  e  ]]_B").
Reserved Notation "[[ e ]]_ l" (at level 10, format "[[ e ]]_ l").
Reserved Notation "nu .-[[ e ]]_stle" (at level 10, format "nu .-[[ e ]]_stle").
Reserved Notation "nu .-[[ e ]]_stl" (at level 10, format "nu .-[[ e ]]_stl").
Reserved Notation "[[ e ]]_dl2e" (at level 10, format "[[ e ]]_dl2e").
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").

Inductive ldl_type :=
| Real_T
| Const_T
| Vector_T of nat
| Index_T of nat
| Fun_T of nat & nat.

Inductive comparison : Type := cmp_le | cmp_eq. (*does it exist for capucci? -J*)
Inductive linear : Type :=  non_l | add_l | mul_l.
Inductive polarity : Type := pos_p | neg_p. 

Section expr.
Context {R : realType}.

Inductive expr : ldl_type -> Type :=
    (* base expressions *)
    | ldl_real : R -> expr Real_T
    | ldl_const : linear -> polarity -> expr Const_T
    | ldl_idx : forall n, 'I_n -> expr (Index_T n) (*Like the fin type?*)
    | ldl_vec : forall n, n.-tuple R -> expr (Vector_T n)
    (* connectives *)
    | ldl_and : expr Const_T  -> expr Const_T  -> expr Const_T 
    | ldl_or  : expr Const_T  -> expr Const_T  -> expr Const_T 
    | ldl_dual :expr Const_T  -> expr Const_T 
    | ldl_sum : expr Const_T  -> expr Const_T  -> expr Const_T 
    | ldl_prod : expr Const_T  -> expr Const_T  -> expr Const_T 
    (* comparisons *)
    | ldl_cmp : comparison -> expr Real_T  -> expr Real_T  -> expr Const_T 
    (* networks and applications *)
    | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m) (*what is all this? _J*)
    | ldl_app : forall n m, expr (Fun_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
    | ldl_lookup : forall n, expr (Vector_T n) -> expr (Index_T n) -> expr Real_T .

End expr.

Notation ldl_true := (ldl_const non_l neg_p). 
Notation ldl_false := (ldl_const non_l pos_p). 
Notation ldl_one := (ldl_const mul_l pos_p). 
Notation ldl_zero := (ldl_const add_l neg_p). 
Notation ldl_top := (ldl_const add_l pos_p). 
Notation ldl_bot := (ldl_const mul_l neg_p). 

Declare Scope ldl_scope.

Notation "a `/\ b" := (ldl_and a b) (at level 45).
Notation "a `\/ b" := (ldl_or a b) (at level 45).
Notation "a `+ b" := (ldl_sum a b) (at level 45).
Notation "a `* b" := (ldl_prod a b) (at level 45).
Notation "`~ a"    := (ldl_dual a) (at level 75). (* is the DUAL operator NOT negation -J*)
Notation "a `~* b" := (`~ (`~ a `* `~ b)) (at level 45).
Notation "a `~+ b" := (`~ (`~ a `+ `~ b)) (at level 45).
Notation "a `=> b" := (`~ a `~* b ) (at level 55).

Local Open Scope ldl_scope.

Notation "a `<= b" := (ldl_cmp cmp_le a b) (at level 70).
Notation "a `== b" := (ldl_cmp cmp_eq a b) (at level 70).
Notation "a `!= b" := (`~ (a == b)) (at level 70).
Notation "a `< b"  := (a `<= b /\ a `!= b) (at level 70).
Notation "a `>= b" := (b `<= a) (at level 70).
Notation "a `> b"  := (b `< a) (at level 70).

Local Close Scope ldl_scope.

Section type_translation.
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Const_T => \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
end.

Definition bool_type_translation (t : ldl_type) : Type :=
  match t with
  | Const_T => bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
  end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint bool_translation {t} (e : @expr R t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | ldl_true => true
  | ldl_false => false
  | ldl_one => true
  | ldl_zero => false
  | ldl_top => true
  | ldl_bot => false
  | ldl_real r => r%R
  | ldl_idx n i => i
  | ldl_vec n t => t

  | a `/\ b =>  << a >> && << b >>
  | a `\/ b => << a >> || << b >> 
  | `~ a => ~~ << a >>
  | a `+ b => << a >> || << b >>
  | a `* b => << a >> || << b >> 

  | E1 `== E2 => << E1 >> == << E2 >>
  | E1 `<= E2 => << E1 >> <= << E2 >>

  | ldl_fun n m f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

End bool_translation.

Notation "[[ e ]]_B" := (bool_translation e) : ldl_scope.

Section fuzzy_translation.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint translation {t} (e : @expr R t) {struct e} : type_translation t := (*what is struct? -J*)
  match e in expr t return type_translation t with 
  | ldl_true => +oo
  | ldl_false => 0
  | ldl_one => 1
  | ldl_zero => 0
  | ldl_top => +oo
  | ldl_bot => 1
  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | a `/\ b =>  mine << a >> << b >>
  | a `\/ b => maxe << a >> << b >>
  | `~ a => 
    if << a >> is v%:E then 
      if v == 0 %R then +oo 
      else v^-1%:E 
    else 0
  | a `+ b => adde << a >> << b >>
  | a `* b => mule << a >> << b >>

  | a `== b => (- `| << a >> - << b >>|)%:E (*???*)
  | a `<= b => (<< b >> - << a >>)%:E (*???*)

  | ldl_fun n m f => f 
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
   end
   where "<< e >>" := (translation e).
End fuzzy_translation.

Section shadow_lifting.
Local Open Scope ring_scope.

Definition shadow_lifting {R : realType} n (f : 'rV_n.+1 -> R) :=
  forall p, p > 0 -> forall i, ('d f '/d i) (const_mx p) > 0.

End shadow_lifting.