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
  | Fun_T of nat & nat
  | FFun_T.

End ldl_type. 

Section expr.

Context {R : realType} {I : realType}. (*How do I specify that 'I' must be a measure space? *)

Inductive expr : ldl_type -> Type :=
    (* fuzzy base expressions *)
    (*| ldl_bool : bool -> expr Fuzzy_T*)
    (* base expressions *)
    | ldl_real : R -> expr Real_T
    | ldl_idx : forall n, 'I_n -> expr (Index_T n) (*Like the fin type? -J*)
    | ldl_vec : forall n, n.-tuple R -> expr (Vector_T n)
    (* fuzzy connectives *)
    | ldl_and : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_or  : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_dual : expr Fuzzy_T  -> expr Fuzzy_T
    | ldl_sum : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_ten : expr Fuzzy_T  -> expr Fuzzy_T  -> expr Fuzzy_T 
    | ldl_scm : expr Fuzzy_T -> expr Fuzzy_T -> expr Fuzzy_T
    (* fuzzy networks and applications *)
    | ldl_ffun : (I -> \bar R) -> expr FFun_T
    | ldl_fapp : expr FFun_T -> I -> expr Fuzzy_T
    (* networks and applications *)
    | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m) 
    | ldl_app : forall n m, expr (Fun_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
    | ldl_lookup : forall n, expr (Vector_T n) -> expr (Index_T n) -> expr Real_T .

End expr.

Declare Scope ldl_scope.

Notation ldl_fuzzy r := (ldl_fapp (ldl_ffun (fun _ => r)) 0).
Notation ldl_true := (ldl_fuzzy +oo%E).
Notation ldl_false := (ldl_fuzzy 0%R).
Notation ldl_one := (ldl_fuzzy 1%E).
Notation ldl_zero := (ldl_fuzzy 0%E).
Notation ldl_top := (ldl_fuzzy +oo%E).
Notation ldl_bot := (ldl_fuzzy 1%E).

Notation "` f [ a ]" := (ldl_fapp f a) (at level 75).
Notation "a `/\ b" := (ldl_and a b) (at level 45).
Notation "a `\/ b" := (ldl_or a b) (at level 45).
Notation "a `+ b" := (ldl_sum a b) (at level 45).
Notation "a `* b" := (ldl_ten a b) (at level 45).
Notation "`~ a"    := (ldl_dual a) (at level 75). (* is the DUAL operator NOT negation -J*)
Notation "k `° a" := (ldl_scm k a) (at level 75).
Notation "a `~* b" := (`~ (`~ a `* `~ b)) (at level 45).
Notation "a `~+ b" := (`~ (`~ a `+ `~ b)) (at level 45).
Notation "a `-o b" := (`~ a `~* b ) (at level 55). (*division / implication / <= ?*)

Notation "\ldl_or_ ( i <- r ) F" := 
(\big[ldl_or/(ldl_false)]_(i <- r) F ) (at level 45).

Section type_translation.
Context {R : realType} {I : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Fuzzy_T => \bar R
  | FFun_T => I -> \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
end.

Definition bool_type_translation (t : ldl_type) : Type :=
  match t with
  | Fuzzy_T => bool
  | FFun_T => I -> \bar R
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
Context {R : realType} {I : realType}.

Fixpoint bool_translation {t} (e : @expr R I t) : bool_type_translation t := (*????*)
  match e in expr t return bool_type_translation t with
  | `f [a] => `| << f >> a | == +oo (*???*)
  | k `° a => << a >>  (*????*) 
  | a `/\ b =>  << a >> && << b >>
  | a `\/ b => << a >> || << b >> 
  | `~ a => ~~ << a >>
  | a `+ b => << a >> || << b >> 
  | a `* b => << a >> || << b >> 

  | ldl_ffun f => f  
  | ldl_fun n m f => f 
  | ldl_real r => r 
  | ldl_idx n i => i
  | ldl_vec n t => t
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

End bool_translation.

Notation "[[ e ]]_B" := (bool_translation e) : ldl_scope. 

Section sc_mod. 
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope ereal_scope.
Context {R : realType}.
Implicit Types (k : R) (a : \bar R).

Definition poweR' a k := if (a == 0%R) then 0%R else (a `^ k)%E.

End sc_mod. 

Section fuzzy_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope ereal_scope.
Context {R : realType} {I : realType}.

Fixpoint translation {t} (e : @expr R I t) {struct e} : type_translation t := 
  match e in expr t return type_translation t with 
  | `f [a] => `| << f >> a |(*???*)
  | a `/\ b =>  mine << a >> << b >>
  | a `\/ b => maxe << a >> << b >>
  | `~ a =>
    if << a >> is (v%:E) then
      if v == 0 %R then +oo
      else (v^-1%:E )
    else 0
  | a `+ b => << a >> + << b >>
  | a `* b => << a >> * << b >>
  | k `° a => 
    if << k >> is v%:E then 
      poweR' << a >> v 
    else +oo * << a >>

  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t
  | ldl_ffun f => f  
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
Context {R : realType} {I : realType}.

Notation "<< e >>" := (@translation R I _ e) : ldl_scope.
Notation "[[ e ]]" := (@bool_translation R I _ e) : ldl_scope.

Lemma total_cap : forall x : expr Fuzzy_T, exists y : \bar R, y = << x >>. 
Proof. 
  dependent induction x; eapply ex_intro; auto.
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

Lemma poweR'_ge0 : forall (x : \bar R) (r : R) ,  0 <= poweR' x r.
Proof. 
  by move => x r; rewrite /poweR'; case (x == 0) eqn:H; rewrite H //= ?poweR_ge0.
Qed.

Lemma nneg_cap : forall x : expr Fuzzy_T, 0%:E <= << x >>.
Proof.  
  dependent induction x. 
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
  -- (* <<x1 `° x2>> *)
  by rewrite //=; case << x1 >> eqn:H; rewrite ?poweR'_ge0 // mule_ge0 // IHx2. 
  -- (* ` x [i] *)
  by rewrite abse_ge0 //.
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
    by rewrite //= unlock //= normr0 mule0. 
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
  by move => u H; exists ldl_one; rewrite //= normr1 mule1 muleC mule1 H.
Qed.

Lemma ldl_ten_unitary : exists u : expr Fuzzy_T, exists v : expr Fuzzy_T, 
<< u `* v >> = 1 /\ << v `* u >> = 1.
Proof.
  exists ldl_one. exists ldl_one. 
  simpl. 
  by rewrite normr1 mule1 //=.
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

Definition is_cap b (x : \bar R) := if b then x == +oo else x == 0.

Lemma ldl_cap_sound : forall e : expr Fuzzy_T, forall b : bool, 
is_cap b << e >> -> [[ e ]] = b. 
Proof. 


Definition is_cap_range b (x : \bar R) := if b then 1 <= x else x < 1.

Lemma ldl_cap_sound_range : forall e : expr Fuzzy_T, forall b : bool, 
is_cap_range b << e >> -> [[ e ]] = b. 
Proof. 
  move => e. dependent induction e; rewrite //=; move => b. 
    - (*and*)
    case b eqn:H0;
    have H1 := IHe1 _ erefl JMeq_refl b; rewrite H0 //= in H1; 
    have H2 := IHe2 _ erefl JMeq_refl b; rewrite H0 //= in H2;
    rewrite //=; rewrite //= ?le_min ?gt_min; move => H3. 
      -- (*true*)
      destruct (andP H3) as [H4 H5]; rewrite (H1 H4) (H2 H5) //.
      -- (*false*)
      destruct (orP H3) as [H4 | H4];
      rewrite ?(H1 H4) //= ?(H2 H4) Bool.andb_comm //=.
    - (*or*)
    case b eqn:H0;
    have H1 := IHe1 _ erefl JMeq_refl b; rewrite H0 //= in H1; 
    have H2 := IHe2 _ erefl JMeq_refl b; rewrite H0 //= in H2;
    rewrite //=; rewrite //= ?le_max ?gt_max; move => H3.
      -- (*true*)
      destruct (orP H3) as [H4 | H4]; rewrite ?(H1 H4) //= ?(H2 H4) orbC //=.
      -- (*false*)
      destruct (andP H3) as [H4 H5]; rewrite ?(H1 H4) //= ?(H2 H5) //=.
    - (*neg*)
    admit.
    (*
    case b eqn:H0;
    have H1 := IHe _ erefl JMeq_refl (~~ b); rewrite H0 //= in H1; 
    rewrite //=.
      -- (*true*)
      case << e >> eqn:H2.
        --- (*<<e>> = s%:E*)
        case (s == 0%R) eqn:H3.
          ---- (*(s == 0%R) = true*)
          rewrite (eqP H3) lte01 //= in H1.
          rewrite H1 //. 
          ---- (*(s == 0%R) = true*)
          move => H4. 
          assert (H5 : 1 <= (s^-1)%:E * 1). {rewrite mule1. apply H4. } (*???*)
          rewrite lee_pdivlMl in H5. rewrite mule1 in H5.
          have H6 := (lt_def s%:E 1). (*impossible to assert s != 1*)
          *)
      - (*add*)
      admit. (*not sound*)
      - (*mul*)
      

          
(*
  move => e b. case b eqn:H; rewrite /=.
  - (*b = true*)
  dependent induction e; rewrite /=.
    -- (*and*) 
    have H1 := IHe1 _ erefl JMeq_refl _ erefl; 
    have H2 := IHe2 _ erefl JMeq_refl _ erefl.
    rewrite le_min; move => H0.
    destruct (andP H0) as [H3 H4]; rewrite (H1 H3) (H2 H4) //.
    -- (*or*)
    have H1 := IHe1 _ erefl JMeq_refl _ erefl; 
    have H2 := IHe2 _ erefl JMeq_refl _ erefl.
    rewrite le_max; move => H0.
    destruct (orP H0) as [H3 | H4]; rewrite ?(H1 H3) //= ?(H2 H4) orbC //=.
    -- (*not*)
    have H1 := IHe _ erefl JMeq_refl _ erefl.
    case << e >> eqn:H2. 
      --- (*<<e>> = s%:E*)
      case (s == 0%R) eqn:H3.
      ---- (*true*)

    Search "orbC".
*)
    
Admitted.

Search "expR".
End some_properties.
