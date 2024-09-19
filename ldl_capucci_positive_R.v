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

Section ldl_type.
Context {R : realType}.

Inductive ldl_type :=
| Fuzzy_T
| Real_T
| Vector_T of nat
| Index_T of nat
| Fun_T of nat & nat.

End ldl_type. 

Section constant.
Context {R : realType}.

Inductive constant := 
  | fuzzy_c of {nonneg \bar R} 
  | true_c | false_c 
  | one_c | zero_c 
  | top_c | bot_c.

End constant. 

Section expr.
Context {R : realType}.

Inductive expr : ldl_type -> Type :=
    (* base expressions *)
    | ldl_const :  @constant R -> expr Fuzzy_T
    | ldl_real : R -> expr Real_T
    | ldl_idx : forall n, 'I_n -> expr (Index_T n) (*Like the fin type? -J*)
    | ldl_vec : forall n, n.-tuple R -> expr (Vector_T n)
    (* connectives *)
    | ldl_and : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_or  : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_dual : expr Fuzzy_T  -> expr Fuzzy_T
    | ldl_sum : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_prod : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    (* networks and applications *)
    | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m) (*what is all this? _J*)
    | ldl_app : forall n m, expr (Fun_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
    | ldl_lookup : forall n, expr (Vector_T n) -> expr (Index_T n) -> expr Real_T .

End expr.

Declare Scope ldl_scope.

Notation ldl_true := (ldl_const true_c). 
Notation ldl_false := (ldl_const false_c). 
Notation ldl_one := (ldl_const one_c). 
Notation ldl_zero := (ldl_const zero_c).
Notation ldl_top := (ldl_const top_c). 
Notation ldl_bot := (ldl_const bot_c). 
Notation ldl_fuzzy r := (ldl_const (fuzzy_c r)).

Notation "a `/\ b" := (ldl_and a b) (at level 45).
Notation "a `\/ b" := (ldl_or a b) (at level 45).
Notation "a `+ b" := (ldl_sum a b) (at level 45).
Notation "a `* b" := (ldl_prod a b) (at level 45).
Notation "`~ a"    := (ldl_dual a) (at level 75). (* is the DUAL operator NOT negation -J*)
Notation "a `~* b" := (`~ (`~ a `* `~ b)) (at level 45).
Notation "a `~+ b" := (`~ (`~ a `+ `~ b)) (at level 45).
Notation "a `=> b" := (`~ a `~* b ) (at level 55).

Local Open Scope ldl_scope.

Lemma expr_ind' (R : realType) :
  forall P : forall s : ldl_type, expr s -> Prop, 
    (forall s : @constant R, P Fuzzy_T (ldl_const s)) -> 
    (forall s : R, P Real_T (ldl_real s) ) ->
    (forall n (o : 'I_n), P (Index_T n) (ldl_idx o)) -> 
    (forall n (t : n.-tuple R), P (Vector_T n) (ldl_vec t)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T (s `/\ n)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T (s `\/ n)) ->
    (forall s : expr Fuzzy_T, P Fuzzy_T (`~ s)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T (s `+ n)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T (s `* n)) ->
    (forall (n m : nat) (t : n.-tuple R -> m.-tuple R), P (Fun_T n m) (ldl_fun t)) ->
    (forall (n m : nat) (e : expr (Fun_T n m)),
     P (Fun_T n m) e ->
     forall e0 : expr (Vector_T n), P (Vector_T n) e0 -> P (Vector_T m) (ldl_app e e0)) ->
    (forall (n : nat) (e : expr (Vector_T n)),
     P (Vector_T n) e ->
     forall e0 : expr (Index_T n), P (Index_T n) e0 -> P Real_T (ldl_lookup e e0)) ->
  forall (s : ldl_type) (e : expr s), P s e. 
Proof. 
move => P H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 s e.
revert e.
revert s. 
fix F1 2.
intros.  
destruct e. 
  - apply H.
  - apply H0.
  - apply H1.
  - apply H2. 
  - apply H3. 
  - apply H4. 
  - apply H5. 
  - apply H6. 
  - apply H7. 
  - apply H8. 
  - apply H9; eauto.
  - apply H10; eauto.
Qed.  
Local Close Scope ldl_scope.


Section type_translation.
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Fuzzy_T => {nonneg \bar R}
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
end.

Definition bool_type_translation (t : ldl_type) : Type :=
  match t with
  | Fuzzy_T => bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
  end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope ereal_dual_scope.
Context {R : realType}.

Fixpoint bool_translation {t} (e : @expr R t) : bool_type_translation t := (*????*)
  match e in expr t return bool_type_translation t with
  | ldl_true => true
  | ldl_false => false
  | ldl_one => true
  | ldl_zero => false
  | ldl_top => true
  | ldl_bot => false
  | ldl_fuzzy r => if (r%:num < 1) then false else true
  | ldl_real r => r 
  | ldl_idx n i => i
  | ldl_vec n t => t

  | a `/\ b =>  << a >> && << b >>
  | a `\/ b => << a >> || << b >> 
  | `~ a => ~~ << a >>
  | a `+ b => << a >> || << b >>
  | a `* b => << a >> || << b >> 

  | ldl_fun n m f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

End bool_translation.

Notation "[[ e ]]_B" := (bool_translation e) : ldl_scope.

Section fuzzy_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope ereal_scope.
Context {R : realType}.

Fixpoint translation {t} (e : @expr R t) {struct e} : type_translation t := (*what is struct? -J*)
  match e in expr t return type_translation t with 
  | ldl_true => +oo%:nng
  | ldl_false => 0%:nng
  | ldl_one => 1%:nng
  | ldl_zero => 0%:nng
  | ldl_top => +oo%:nng
  | ldl_bot => 1%:nng
  | ldl_fuzzy r => r

  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | a `/\ b =>  mine << a >> << b >>
  | a `\/ b => maxe << a >> << b >>
  | `~ a => 
    if << a >>%:num%:E is (v%:E) then 
      if v == 0 %R then 
        +oo%:nng 
      else inv v
    else 0%:nng
  | a `+ b => (<< a >>%:num + << b >>%:num)%:nng
  | a `* b => (<< a >>%:num + << b >>%:num)%:nng

  | ldl_fun n m f => f 
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
   end
   where "<< e >>" := (translation e).

End fuzzy_translation.

Notation "[[ e ]]_C" := (translation e) : ldl_scope.

Section shadow_lifting.
Local Open Scope ring_scope.

Definition shadow_lifting {R : realType} n (f : 'rV_n.+1 -> R) :=
  forall p, p > 0 -> forall i, ('d f '/d i) (const_mx p) > 0.

End shadow_lifting.