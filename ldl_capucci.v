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
  | fuzzy_c of R
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
    | ldl_ten : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    (* networks and applications *)
    | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m) 
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
Notation "a `* b" := (ldl_ten a b) (at level 45).
Notation "`~ a"    := (ldl_dual a) (at level 75). (* is the DUAL operator NOT negation -J*)
Notation "a `~* b" := (`~ (`~ a `* `~ b)) (at level 45).
Notation "a `~+ b" := (`~ (`~ a `+ `~ b)) (at level 45).
Notation "a `=> b" := (`~ a `~* b ) (at level 55).

Notation "\ldl_or_ ( i <- s )" := (\big[ldl_or/(@ldl_false)]_(i <- s) i).

Notation "\ldl_or_ ( i <- r | P ) F" := 
(\big[ldl_or/ldl_false]_(i <- r | P) F ) (at level 45).

Notation "\ldl_or_ ( i <- r ) F" := 
(\big[ldl_or/@ldl_false]_(i <- r) F ) (at level 45).

Local Open Scope ldl_scope.

Lemma expr_ind' (R : realType) :
  forall P : forall s : ldl_type, expr s -> Prop, 
    (forall s : @constant R, P Fuzzy_T (ldl_const s)) -> 
    (forall s : R, P Real_T (ldl_real s) ) ->
    (forall n (o : 'I_n), P (Index_T n) (ldl_idx o)) -> 
    (forall n (t : n.-tuple R), P (Vector_T n) (ldl_vec t)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T s -> P Fuzzy_T n -> P Fuzzy_T (s `/\ n)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T s -> P Fuzzy_T n -> P Fuzzy_T (s `\/ n)) ->
    (forall s : expr Fuzzy_T, P Fuzzy_T s -> P Fuzzy_T (`~ s)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T s -> P Fuzzy_T n -> P Fuzzy_T (s `+ n)) ->
    (forall s n : expr Fuzzy_T, P Fuzzy_T s -> P Fuzzy_T n -> P Fuzzy_T (s `* n)) ->
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
    - apply H3; apply F1; apply F1.   
    - apply H4; apply F1; apply F1. 
    - apply H5; apply F1. 
    - apply H6; apply F1; apply F1.
    - apply H7; apply F1; apply F1.
    - apply H8. 
    - apply H9; apply F1. 
    - apply H10; apply F1. 
Qed.  
Local Close Scope ldl_scope.

Section type_translation.
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Fuzzy_T => \bar R
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
  | ldl_fuzzy r => ~~ (r < 1) %R 
  | ldl_real r => r 
  | ldl_idx n i => i
  | ldl_vec n t => t

  | a `/\ b =>  << a >> && << b >>
  | a `\/ b => << a >> || << b >> 
  | `~ a => ~~ << a >>
  | a `+ b => << a >> || << b >>
  | a `* b => << a >> && << b >> 

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
  | ldl_true => +oo
  | ldl_false => 0%:E
  | ldl_one => 1%:E
  | ldl_zero => 0%:E
  | ldl_top => +oo
  | ldl_bot => 1%:E
  | ldl_fuzzy r => `| r | %:E

  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | a `/\ b =>  mine << a >> << b >>
  | a `\/ b => maxe << a >> << b >>
  | `~ a =>
    if << a >> is (v%:E) then
      if v == 0 %R then +oo
      else (v^-1%:E )
    else 0
  | a `+ b => << a >> + << b >>
  | a `* b => << a >> * << b >>

  | ldl_fun n m f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
   end
   where "<< e >>" := (translation e).

End fuzzy_translation.

Notation "<< e >>" := (translation e) : ldl_scope.

Section some_properties. 
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Lemma total_cap : forall x : @expr R Fuzzy_T, exists y : \bar R, y = << x >>. 
Proof. 
  dependent induction x.
  - eapply ex_intro. auto. 
  - eapply ex_intro. auto. 
  - eapply ex_intro. auto. 
  - eapply ex_intro. auto. 
  - eapply ex_intro. auto. 
  - eapply ex_intro. auto. 
Qed. 

Lemma or_mine : forall x1 x2 : \bar R, mine x1 x2 = x1 \/  mine x1 x2 = x2.
Proof. 
  move => x1 x2. elim x1.
  - move => a1. elim x2.
    -- move => a2. unfold mine. simpl. induction (a1%:E < a2%:E).
      --- left. reflexivity.
      --- right. reflexivity.
    -- unfold mine. rewrite (ltry a1). left. reflexivity.
    -- unfold mine. simpl. right. reflexivity.
  - elim x2. 
    -- move => a2. unfold mine. simpl. right. reflexivity.
    -- unfold mine. simpl. left. reflexivity.
    -- unfold mine. simpl. right. reflexivity.
  - elim x2.
    -- move => a2. unfold mine. rewrite (ltNyr a2). left. reflexivity.
    -- unfold mine. simpl. left. reflexivity.
    -- unfold mine. simpl. left. reflexivity.
Qed.

Lemma or_maxe : forall x1 x2 : \bar R, maxe x1 x2 = x1 \/  maxe x1 x2 = x2.
Proof. 
  move => x1 x2. elim x1.
  - move => a1. elim x2.
    -- move => a2. unfold maxe. simpl. induction (a1%:E < a2%:E).
      --- right. reflexivity.
      --- left. reflexivity.
    -- unfold maxe. rewrite (ltry a1). right. reflexivity.
    -- unfold maxe. simpl. left. reflexivity.
  - elim x2. 
    -- move => a2. unfold maxe. simpl. left. reflexivity.
    -- unfold maxe. simpl. right. reflexivity.
    -- unfold maxe. simpl. left. reflexivity.
  - elim x2.
    -- move => a2. unfold maxe. rewrite (ltNyr a2). right. reflexivity.
    -- unfold maxe. simpl. right. reflexivity.
    -- unfold maxe. simpl. right. reflexivity.
Qed.

Lemma nneg_cap : forall x : @expr R Fuzzy_T, 0%:E <= << x >>.
Proof.  
  dependent destruction x using expr_ind'. 
  (* ldl_const s *)
  - case s. 
    -- simpl. unfold Order.le. simpl. auto. 
    -- simpl. unfold Order.le. simpl. auto.
    -- simpl. unfold Order.le. simpl. auto.
    -- simpl. unfold Order.le. simpl. auto.
    -- simpl. unfold Order.le. simpl. auto.
    -- simpl. unfold Order.le. simpl. auto.
    -- simpl. unfold Order.le. simpl. auto.
  - (* x1 `/\ x2*)
  assert (H : 0%:E <= << x1 >>). {apply (IHx1 x1). reflexivity. auto. }
  move : IHx1. move => _. 
  assert (H0 : 0%:E <= << x2 >>). {apply (IHx2 x2). reflexivity. auto. }
  move : IHx2. move => _.  
  simpl. 
  destruct (total_cap x1) as [y1 H1]. 
  destruct (total_cap x2) as [y2 H2].
  rewrite <- H1. rewrite <- H2. 
  rewrite <- H1 in H. rewrite <- H2 in H0.
  destruct y1. 
    -- destruct y2. 
      --- destruct (or_mine s%:E s0%:E) as [H3 | H3].
        ---- rewrite H3. apply H.
        ---- rewrite H3. apply H0.
      --- unfold mine. rewrite (ltry s). apply H.
      --- unfold mine. simpl. apply H0.
    -- destruct y2.
      --- unfold mine. simpl. apply H0.
      --- unfold mine. simpl. apply H.
      --- unfold mine. simpl. apply H0.  
    -- destruct y2.
      --- unfold mine. unfold Order.lt. simpl. assert (H4 : s \is Num.real). { auto. } rewrite H4. apply H.
      --- unfold mine. simpl. apply H.
      --- unfold mine. simpl. apply H.
  - (* x1 `\/ x2*)
  assert (H : 0%:E <= << x1 >>). {apply (IHx1 x1). reflexivity. auto. }
  move : IHx1. move => _. 
  assert (H0 : 0%:E <= << x2 >>). {apply (IHx2 x2). reflexivity. auto. }
  move : IHx2. move => _.  
  simpl. 
  destruct (total_cap x1) as [y1 H1]. 
  destruct (total_cap x2) as [y2 H2].
  rewrite <- H1. rewrite <- H2. 
  rewrite <- H1 in H. rewrite <- H2 in H0.
  destruct y1. 
    -- destruct y2. 
      --- destruct (or_maxe s%:E s0%:E) as [H3 | H3].
        ---- rewrite H3. apply H.
        ---- rewrite H3. apply H0.
      --- unfold maxe. rewrite (ltry s). apply H0.
      --- unfold maxe. simpl. apply H.
    -- destruct y2.
      --- unfold maxe. simpl. apply H.
      --- unfold maxe. simpl. apply H0.
      --- unfold maxe. simpl. apply H.  
    -- destruct y2.
      --- 
      unfold maxe. unfold Order.lt. simpl. 
      assert (H4 : s \is Num.real). { auto. } 
      rewrite H4. apply H0.
      --- unfold maxe. simpl. apply H0.
      --- unfold maxe. simpl. apply H0.
  - (*`~ x*)
  assert (H : 0%:E <= << x >>). {apply (IHx x). reflexivity. auto. }
  move : IHx. move => _.
  simpl. destruct << x >>.
    -- destruct (s == 0%R).
      --- apply (le0y ).
      --- 
      unfold Order.le. simpl. 
      rewrite (invr_ge0 s).
      unfold Order.le in H; simpl in H.
      apply H.
    -- unfold Order.le. simpl. auto.
    -- unfold Order.le. simpl. auto.
  - (* x1 `+ x2 *)
  assert (H : 0%:E <= << x1 >>). {apply (IHx1 x1). reflexivity. auto. }
  move : IHx1. move => _. 
  assert (H0 : 0%:E <= << x2 >>). {apply (IHx2 x2). reflexivity. auto. }
  move : IHx2. move => _.
  simpl.
  apply (lee_paddr H0 H).
  -- (* x1 `* x2 *)
  assert (H : 0%:E <= << x1 >>). {apply (IHx1 x1). reflexivity. auto. }
  move : IHx1. move => _. 
  assert (H0 : 0%:E <= << x2 >>). {apply (IHx2 x2). reflexivity. auto. }
  move : IHx2. move => _.
  simpl.
  apply (mule_ge0 H H0).
Qed.

Lemma mulyn0 : forall x : \bar R, 0%:E < x -> +oo * x = +oo.
Proof. 
  move=> x H. destruct x.
  -  destruct (s%:E == 0%:E) eqn:H0.
    -- 
    assert (H1 : s%:E = 0). {apply (eqP H0). }
    rewrite lt0e in H. 
    destruct (predD1P H) as [H2 H3]. (*could not find a simpler one*)
    unfold not in H2. contradiction.
    -- 
    unfold "*".
    rewrite H0.
    rewrite H.
    reflexivity.
  -
  unfold "*".
  simpl. 
  rewrite H.
  reflexivity.
  -
  unfold Order.lt in H. 
  simpl in H. 
  exfalso. 
  apply Bool.diff_false_true. 
  apply H.
Qed.

(*
Lemma eqe_imp_lee : forall x1 x2 : \bar R, x1 == x2 -> x1 <= x2.
Proof. 
  move => x1 x2 H. rewrite (eqP H). destruct x2.
  -
  unfold Order.le. simpl. auto.
  -
  unfold Order.le. simpl. auto.
  -
  unfold Order.le. simpl. auto.
Qed.
*)

Lemma id_maxe : forall x : \bar R, maxe x x = x.
Proof. 
  move => x. destruct (or_maxe x x) as [H0 | H0].
  - by rewrite H0.
  - by rewrite H0.
Qed.

Lemma eqF : forall x y : \bar R, x != y -> x == y = false.
Proof. 
  move=> x y H. 
  apply : (contra_neqF _ H). move => H1. apply (eqP H1). 
Qed.

(*
Lemma lte_not_lee : forall x1 x2 : \bar R, x1 < x2 -> ~ x2 <= x1.
Proof.
  move => x1 x2 H.  apply : (contra_lt_not _ H). move => H0. apply H0. 
Qed.
*)

Lemma maxeMr_nneg : forall k x1 x2 : \bar R, 
0%:E <= k -> 0%:E <= x1 -> 0%:E <= x2 ->
k * (maxe x1 x2) = maxe (k * x1) (k * x2).
Proof. 
  move => k x1 x2 H H0 H1.
  rewrite le_eqVlt in H.
  rewrite le_eqVlt in H0.
  rewrite le_eqVlt in H1.
  destruct (orP H) as [H2 | H2].
    - (*0%:E == k*) 
    rewrite <- (eqP H2).
    rewrite !mul0e.
    by rewrite id_maxe.
    - (*0%:E < k*)
    destruct k.
      -- (* k = s%:E*)
      assert (H4 : -oo < s%:E < +oo). 
        {apply/andP. split. apply (ltNyr s).  apply (ltry s). }
      apply fin_real in H4.
      apply (maxeMr x1 x2 H4). apply H2.
      -- (*k = +oo*)
      destruct (orP H0) as [H3 | H3].
        --- (*0%:E == x1*)
        rewrite <- (eqP H3).
        rewrite mule0.
        destruct (orP H1) as [H4 | H4].
          ---- (*0%:E == x2 *)
          rewrite <- (eqP H4).
          rewrite mule0.
          rewrite id_maxe.
          by rewrite mule0.
          ---- (*0%:E < x2*)
          rewrite (mulyn0 H4). 
          unfold maxe. 
          rewrite lt0y.
          rewrite H4.
          unfold "*".
          rewrite lt0y.
          rewrite H4.
          rewrite lt0e in H4.
          destruct (andP H4) as [H5 H6].
          simpl. apply eqF in H5. rewrite H5.
          destruct x2. 
            ----- (*x2 = s%:E*)
            reflexivity. 
            ----- (*x2 = +oo*)
            reflexivity.
            ----- (*x2 = -oo*)
            unfold Order.le in H6. 
            simpl in H6. 
            exfalso. 
            apply (Bool.diff_false_true H6).
        --- (*0%:E < x1*)
        destruct (orP H1) as [H4 | H4].
          ---- (*0%:E == x2*)
          rewrite <- (eqP H4).
          rewrite mule0.
          destruct x1.
            ----- (*x1 = s%:E*)
            destruct (s%:E == 0%:E) eqn:H5.
              ------ (*(s%:E == 0%:E) = true*)
              rewrite (eqP H5).
              rewrite mule0.
              rewrite !id_maxe.
              by rewrite mule0.
              ------ (*(s%:E == 0%:E) = false*)
              rewrite (mulyn0 H3).
              destruct (or_maxe s%:E 0%:E) as [H6 | H6].
                ------- (*maxe s%:E 0%:E = s%:E*)
                rewrite H6.
                unfold maxe; simpl.
                unfold "*". 
                rewrite H5.
                by rewrite H3.
                ------- (* maxe s%:E 0%:E = 0%:E*)
                rewrite maxC in H6.
                unfold maxe in H6.
                rewrite H3 in H6.
                remember (negbT H5) as H7.
                move : HeqH7. move => _.
                rewrite <- contra.Internals.eqType_neqP in H7.
                contradiction.
            ----- (*x1 = +oo*)
            rewrite mulyn0.
            rewrite maxC.
            unfold maxe.
            by rewrite lt0y. 
            rewrite maxC.
            unfold maxe.
            rewrite !lt0y.
            auto.
            ----- (*x1 = -oo*)
            unfold maxe.
            unfold "*".
            simpl.
            rewrite lt0y.
            rewrite ltNy0.
            simpl.
            (unfold "0"%E).
            simpl.
            unfold "0".
            assert (H5 : 
              (GRing.isNmodule.zero (Real.class R))%:E 
              == 
              (GRing.isNmodule.zero (Real.class R))%:E = true). 
              {auto. }
            rewrite H5. reflexivity.
          ---- (*0%:E < x2*)
          rewrite (mulyn0 H3); rewrite (mulyn0 H4).
          rewrite id_maxe.
          destruct (or_maxe x1 x2) as [H5 | H5].
            ----- (*maxe x1 x2 = x1*)
            by rewrite H5; rewrite (mulyn0 H3).
            ----- (*maxe x1 x2 = x2*) 
            by rewrite H5; rewrite (mulyn0 H4).
      -- (*k = -oo*)       
      destruct (orP H0) as [H3 | H3].
        --- (*0%:E == x1*)
        destruct (orP H1) as [H4 | H4].
          ---- (*0%:E == x2*)
          rewrite <- (eqP H3); rewrite <- (eqP H4).
          by rewrite id_maxe; rewrite mule0; rewrite id_maxe.
          ---- (*0%:E < x2*)
          rewrite <- (eqP H3); rewrite mule0.
          unfold maxe; rewrite H4.
          unfold "*".
          rewrite H4.
          apply lt_eqF in H4 as H5.
          by rewrite eq_sym; rewrite H5; rewrite H2.
        --- (*0%:E < x1*)
        destruct (orP H1) as [H4 | H4].
          ---- (*0%:E == x2*)
          rewrite <- (eqP H4).
          rewrite mule0.
          rewrite maxC. rewrite (maxC (-oo * x1)).
          unfold maxe.
          rewrite H3.
          rewrite (gt0_mulNye H3).
          by rewrite H2.
          ---- (*0%:E < x2*)
          rewrite (gt0_mulNye H3).
          rewrite (gt0_mulNye H4).
          rewrite id_maxe.
          destruct (or_maxe x1 x2) as [H5 | H5].
            ----- (* maxe x1 x2 = x1*)
            by rewrite H5; rewrite (gt0_mulNye H3).
            ----- (* maxe x1 x2 = x2*)
            by rewrite H5; rewrite (gt0_mulNye H4).
Qed.

Lemma ldl_ten_dor : forall k a b : @expr R Fuzzy_T, 
<< k `* (a `\/ b) >> = << (k `* a ) `\/ (k `* b ) >>.
Proof.
    move => k a b. simpl. rewrite maxeMr_nneg. reflexivity.
      - by rewrite nneg_cap.
      - by rewrite nneg_cap.
      - by rewrite nneg_cap.
Qed.

Lemma ldl_ten_big_dor : forall s : seq (@expr R Fuzzy_T), forall k : @expr R Fuzzy_T, 
<< k `* (\ldl_or_ ( i <- s ) i) >> = << \ldl_or_ ( i <- s) (k `* i) >>.
Proof. 
  move => s k.
  elim s.
    - 
    by rewrite unlock; simpl; rewrite mule0.
    -
    move => a l H.
    rewrite !big_cons.
    rewrite ldl_ten_dor //=. 
    by rewrite <- H; simpl.
Qed.

Lemma ldl_tenC : forall x1 x2 : @expr R Fuzzy_T, << x1 `* x2 >> = << x2 `* x1 >>.
Proof.
  by move => x1 x2 /=; rewrite muleC.
Qed.

Lemma ldl_tenA : forall x1 x2 x3 : @expr R Fuzzy_T, << (x1 `* x2) `* x3 >> = << x1 `* (x2 `* x3) >>.
Proof.
  by move => x1 x2 x3 //=; rewrite muleA.
Qed.

Lemma ldl_ten1 : forall y x :@ expr R Fuzzy_T,  (*multiplicative identities*) (* how do I make 'y' an explicit argument?*)
<< y >> = 1 -> << x `* y >> = << x >> /\ << y `* x >> = << x >>.
Proof.
  move => x y H //=. split.
    - (* prove <<x>> * <<y>> = <<x>> *)
    by rewrite H; rewrite mule1.
    - (* prove <<y>> * <<x>> = <<x>>*)
    by rewrite H; rewrite muleC; rewrite mule1.
Qed.

Lemma ldl_ten_1_is_unit : forall u : @expr R Fuzzy_T, (*unit elements*)
<< u >> = 1 ->  exists v : @expr R Fuzzy_T, << u `* v >> = 1 /\ << v `* u >> = 1.
Proof.
  move => u H. 
  exists ldl_one. 
  simpl. 
  rewrite mule1. 
  rewrite muleC; rewrite mule1.
  rewrite H //=. 
Qed.

Lemma ldl_ten_unitary : exists u : @expr R Fuzzy_T, exists v : @expr R Fuzzy_T, 
<< u `* v >> = 1 /\ << v `* u >> = 1.
Proof.
  exists ldl_one. exists ldl_one. 
  simpl. 
  by rewrite mule1 //=.
Qed.

Lemma lt_EFin : forall a : \bar R, 0%R <= a < +oo -> exists s : R, a = s%:E.
Proof.
  move => a H. 
  destruct (andP H) as [H0 H1].
  destruct a eqn:H2.
    - (*a = s%:E*)
    exists s. reflexivity.
    - (*a = +oo*)
    rewrite ltey in H1. 
    rewrite <- contra.Internals.eqType_neqP in H1. 
    contradiction.
    - (*a = -oo*)
    remember (@ltNy0 R) as H3. 
    move : HeqH3; move => _.
    simpl in H3.
    apply ltW in H3.
    remember (@le_anti_ereal R (0%R : \bar R) (-oo : \bar R) H0) as H4.
    move : HeqH4; move => _.
    rewrite <- H4. by exists 0%R. 
Qed.

Lemma aku : forall a b : @expr R Fuzzy_T, 
0 < << a >> < +oo /\ 0 < << b >> < +oo -> 
<< `~ (a `* b) >> = << (`~ a) `* (`~ b) >>.
Proof. 
  move => a b H.
  destruct H as [H H0].
  destruct (andP H) as [H1 H2].
  destruct (andP H0) as [H3 H4].
  apply ltW in H1 as H5.
  apply ltW in H3 as H6.
  assert (H7 : 0%R <= <<a>> < +oo). 
  {apply/andP. split. apply H5. apply H2. }
  assert (H8 : 0%R <= <<b>> < +oo). 
  {apply/andP. split. apply H6. apply H4. }
  remember (lt_EFin H7) as H9; move : HeqH9; move => _.
  remember (lt_EFin H8) as H10; move : HeqH10; move => _.
  destruct H9 as [s H9].
  destruct H10 as [v H10].
  simpl. rewrite H9. rewrite H10.


(*
Lemma ldl_dual_le : forall a b c : @expr R Fuzzy_T, << a `* b >> <= << `~ c >> <-> << a >> <= << `~ (b `* c) >>.
Proof.
  move => a b c. split.
    - (*prove <<a `* b>> <= <<`~ c>> -> <<a>> <= <<b `* c>>*)
    admit.
    - (*prove <<a>> <= <<`~ b `* c>> -> <<a `* b>> <= <<`~ c>>*)
    move => H //=.
    destruct << c >> eqn:H0.
      -- (*<<c>> = s%:E*)
      destruct (s == 0%R) eqn:H1.
        --- (*(s == 0%R) = true*)
        rewrite leey //=.
        --- (*(s == 0%R) = false*)
*)

End some_properties.