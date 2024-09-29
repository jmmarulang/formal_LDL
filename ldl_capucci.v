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

(*
Reserved Notation "{[ e ]}" (format "{[  e  ]}").
Reserved Notation "[[ e ]]_B" (at level 10, format "[[  e  ]]_B").
*)

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

Section some_properties. 
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Notation "<< e >>" := (@translation R _ e) : ldl_scope.
Notation "[[ e ]]" := (@bool_translation R _ e) : ldl_scope.

Lemma total_cap : forall x : expr Fuzzy_T, exists y : \bar R, y = << x >>. 
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

Lemma nneg_cap : forall x : expr Fuzzy_T, 0%:E <= << x >>.
Proof.  
  dependent induction x. 
  - (* ldl_const s *)
  case c; by rewrite /= /Order.le /=.
  - (* x1 `/\ x2*)
  by rewrite /= le_min IHx1 // IHx2. 
  - (* x1 `\/ x2*)
  by rewrite /= le_max IHx1 // IHx2.
  - (*`~ x*)
  have /= := IHx x erefl JMeq_refl. 
  by case : << x >> => // r; case : ifP => H; rewrite ?leey // !lee_fin invr_ge0.
  - (* x1 `+ x2 *)
  rewrite /= lee_paddr //. rewrite IHx2 //. rewrite IHx1 //.
  -- (* x1 `* x2 *)
  rewrite /= mule_ge0 //. rewrite IHx1 //. rewrite IHx2 //.
Qed.

Lemma maxe_id : forall x : \bar R, maxe x x = x.
Proof. 
  by move => x; destruct (or_maxe x x) as [H0 | H0]; rewrite !H0.
Qed.

Lemma eqF : forall x y : R, x != y -> x == y = false.
Proof. 
  move=> x y H. 
  apply : (contra_neqF _ H). move => H1. apply (eqP H1). 
Qed.

Lemma EFin_fin_num : forall s : R, s%:E \is a fin_num.
Proof. 
  move => s. 
  apply fin_real. 
  apply/andP. split. 
  apply (ltNyr s).  
  apply (ltry s).
Qed. 

Lemma maxeMr_nneg : forall k x1 x2 : \bar R, 
0%:E <= k -> 0%:E <= x1 -> 0%:E <= x2 ->
k * (maxe x1 x2) = maxe (k * x1) (k * x2).
Proof. 
  move => k x1 x2 H H0 H1.
  rewrite le_eqVlt in H;
  rewrite le_eqVlt in H0;
  rewrite le_eqVlt in H1.
  destruct (orP H) as [H2 | H2].
    - (*0%:E == k*) 
    by rewrite <- (eqP H2); rewrite !mul0e maxe_id.
    - (*0%:E < k*)
    destruct k.
      -- (* k = s%:E*)
      apply/maxeMr. apply/EFin_fin_num. apply/H2. 
      -- (*k = +oo*)
      destruct (orP H0) as [H3 | H3].
        --- (*0%:E == x1*)
        rewrite <- (eqP H3); rewrite mule0.
        destruct (orP H1) as [H4 | H4].
          ---- (*0%:E == x2 *)
          rewrite <- (eqP H4); by rewrite mule0 maxe_id mule0.
          ---- (*0%:E < x2*)
          rewrite !gt0_mulye /maxe. by rewrite lt0y //.
          by rewrite H4. 
          by rewrite H4. 
        --- (*0%:E < x1*)
        destruct (orP H1) as [H4 | H4].
          ---- (*0%:E == x2*)
          rewrite <- (eqP H4). 
          by rewrite mule0 !gt0_mulye //= maxC /maxe H3 H3.
          ---- (*0%:E < x2*)
          rewrite !gt0_mulye // lt_max. 
          by apply/orP; left. 
      -- (*k = -oo*)    
      by [].
Qed.

Lemma ldl_ten_dor : forall k a b : expr Fuzzy_T, 
<< k `* (a `\/ b) >> = << (k `* a ) `\/ (k `* b ) >>.
Proof.
    move => k a b. simpl. rewrite maxeMr_nneg. reflexivity.
      - by rewrite nneg_cap.
      - by rewrite nneg_cap.
      - by rewrite nneg_cap.
Qed.

Lemma ldl_ten_big_dor : forall s : seq (expr Fuzzy_T), forall k : expr Fuzzy_T, 
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

Lemma ldl_tenC : forall x1 x2 : expr Fuzzy_T, << x1 `* x2 >> = << x2 `* x1 >>.
Proof.
  by move => x1 x2 /=; rewrite muleC.
Qed.

Lemma ldl_tenA : forall x1 x2 x3 : expr Fuzzy_T, << (x1 `* x2) `* x3 >> = << x1 `* (x2 `* x3) >>.
Proof.
  by move => x1 x2 x3 //=; rewrite muleA.
Qed.

Lemma ldl_ten1 : forall y x : expr Fuzzy_T,  (*multiplicative identities*) (* how do I make 'y' an explicit argument?*)
<< y >> = 1 -> << x `* y >> = << x >> /\ << y `* x >> = << x >>.
Proof.
  move => x y H //=. split.
    - (* prove <<x>> * <<y>> = <<x>> *)
    by rewrite H; rewrite mule1.
    - (* prove <<y>> * <<x>> = <<x>>*)
    by rewrite H; rewrite muleC; rewrite mule1.
Qed.

Lemma ldl_ten_1_is_unit : forall u : expr Fuzzy_T, (*unit elements*)
<< u >> = 1 ->  exists v : expr Fuzzy_T, << u `* v >> = 1 /\ << v `* u >> = 1.
Proof.
  move => u H. 
  exists ldl_one. 
  simpl. 
  rewrite mule1. 
  rewrite muleC; rewrite mule1.
  rewrite H //=. 
Qed.

Lemma ldl_ten_unitary : exists u : expr Fuzzy_T, exists v : expr Fuzzy_T, 
<< u `* v >> = 1 /\ << v `* u >> = 1.
Proof.
  exists ldl_one. exists ldl_one. 
  simpl. 
  by rewrite mule1 //=.
Qed.

Lemma le0e_lte0_EFin : forall a : \bar R, 0%R <= a < +oo -> exists s : R, a = s%:E.
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

Lemma ldl_dual_dten : forall a b : expr Fuzzy_T, 
0 < << a >> < +oo /\ 0 < << b >> < +oo -> 
<< `~ (a `* b) >> = << (`~ a) `* (`~ b) >>.
Proof. 
  move => a b H.
  destruct H as [H H0].
  destruct (andP H) as [H1 H2].
  destruct (andP H0) as [H3 H4].
  assert (H5 : exists s : R, << a >> = s%:E). 
  {apply/le0e_lte0_EFin. apply/andP. split. apply (ltW H1). apply H2. }
  assert (H6 : exists s : R, << b >> = s%:E). 
  {apply/le0e_lte0_EFin. apply/andP. split. apply (ltW H3). apply H4. }
  destruct H5 as [s H5].
  destruct H6 as [v H6].
  rewrite //= H5 H6. 
  rewrite H6 in H3.
  case (s == 0%R) eqn:H7. 
    - (*s == 0%R = true*)
    rewrite (eqP H7) mul0e /= eq_refl.
    case (v == 0%R) eqn:H8. 
      -- (*v == 0%R = true*)
      by rewrite mulyy. 
      -- (*v == 0%R = false*)
      rewrite /Order.lt /= in H3.
      by rewrite gt0_mulye //= /Order.lt /= invr_gt0 H3. 
    - (*s == 0%R = false*)
    rewrite [v == _]eq_sym.
    apply lt_eqF in H3 as H8.
    rewrite eqe in H8.
    rewrite //= H8. 
    rewrite eqF.
    rewrite invrM' /mule //.
    (*prove s != 0%R*)
    rewrite H7 //.
    (*prove (s * v)%R != 0%R*)
    rewrite mulf_neq0 //=.
    (*prove s != 0%R*)
    by rewrite H7.
    (*prove v != 0%R*)
    by rewrite eq_sym H8.
Qed. 

Lemma ldl_dual_le : forall a b c : expr Fuzzy_T, 
<< a `* b >> <= << `~ c >> <-> << a >> <= << `~ (b `* c) >>.
Proof. 
  move => a b c /=. 
  have a_nneg := nneg_cap a. 
  have b_nneg := nneg_cap b. 
  have c_nneg := nneg_cap c. 
  case << c >> eqn:H.
  - (*<<c>> = s%:E*)
  case (s == 0%R) eqn:H0.
    -- (*(s == 0%R) = true*)
    by rewrite (eqP H0) /= leey mule0 /= eq_refl leey.
    -- (*(s == 0%R) = false*)
    case << b >> eqn:H1.
      --- (*<<b>> = s0%:E*)
      rewrite /=.
      case (s0 == 0%R) eqn:H2.
        ---- (*(s0 == 0%R) = true*)
        rewrite (eqP H2) mule0 mul0r eq_refl leey /Order.le /= invr_ge0 //.
        ---- (*(s0 == 0%R) = false*)
        rewrite eqF. rewrite <- (lee_pdivlMr << a >> ). 
        rewrite muleC invrM' /mule //=. 
        (*prove s0 != 0%R*)
        by rewrite H2.
        (*prove (0 < s0)%R*)
        rewrite lt_neqAle.
        apply/andP. split. 
          ----- (*prove 0%R != s0*)
          by rewrite eq_sym H2.
          ----- (*prove 0%R <= s0*)
          apply /b_nneg. 
        (*prove (s0 * s)%R != 0%R*)
        apply /mulf_neq0.
        (*prove s0 != 0%R*)
        by rewrite H2.
        (*prove s != 0%R*)
        by rewrite H0.
    -- (*(s == 0%R) = false*)
    case (<< a >> == 0%R) eqn:H2.
      --- (*(<<a>> == 0%R) = true*)
      unfold "*". unfold "==". simpl. 
      rewrite //= lt0y H0 !lt_neqAle (eq_sym 0 s%:E). 
      unfold "==". simpl. rewrite H0 //= c_nneg a_nneg.
      by rewrite (eqP H2) //= eq_refl le_refl /Order.le //= invr_ge0.
      --- (*(<<a>> == 0%R) = false*)
      assert (H3 : 0 < << a >> ). 
      {rewrite lt_neqAle. apply/andP. split. rewrite eq_sym H2 //. rewrite a_nneg //. }
      rewrite (gt0_muley H3).
      unfold "*". unfold "==". simpl.
      rewrite H0 lt_neqAle. unfold "!=". simpl. unfold "==". simpl. 
      rewrite eq_sym H0 c_nneg //=.
      rewrite {1}/Order.le //=.
      apply lt_geF in H3 as H4. rewrite H4 //.
      --- (*<<b>> = -oo *)
      by [].
  - (*<<c>> = +oo*)
  case (<< b >> == 0%R) eqn:H0.
    -- (*(<<b>> == 0%R) = true*)
    by rewrite (eqP H0) mule0 mul0e /= eq_refl le_refl leey.
    -- (*(<<b>> == 0%R) = false*)
    assert (H1 : 0 < << b >> ). 
    {rewrite lt_neqAle. apply/andP. split. rewrite eq_sym H0 //. rewrite b_nneg //. }
    rewrite (gt0_muley H1). 
    case (<< a >> == 0%R) eqn:H2.
      --- (*(<<a>> == 0%R) = true*)
      rewrite (eqP H2) mul0e //=.
      --- (*(<<a>> == 0%R) = false*)
      assert (H3 : 0 < << a >> ). 
      {rewrite lt_neqAle. apply/andP. split. rewrite eq_sym H2 //. rewrite a_nneg //. }
      rewrite (lt_geF H3).
      rewrite lt_geF //.
      (*prove 0%R < <<a>> * <<b>>*)
      rewrite (mule_gt0 H3 H1) //.
  - (*<<c>> = +oo*)
  by [].
Qed.

Lemma ldl_cap_sound_left : forall e : expr Fuzzy_T, forall b : constant, 
<< e >> != 1 -> << e >> = << ldl_const b >> -> [[ e ]] = [[ ldl_const b ]].
Proof. 
Admitted.
End some_properties.