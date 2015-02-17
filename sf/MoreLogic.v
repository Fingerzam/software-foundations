(** * More Logic *)

Require Export "Prop".

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* There exists a natural number n such that (S n) is beautiful. *)

(*
*)
(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros X P H. unfold not. intros He. inversion He as [x Hx].
  apply Hx. apply H. Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros EM.
  intros X P He. unfold not in He. unfold excluded_middle in EM.
  intros x.
  assert (HEM: P x \/ ~(P x)). apply EM. inversion HEM.
  Case "left". apply H.
  Case "right". unfold not in H. assert (H': exists x : X, P x -> False).
    exists x. apply H. apply He in H'. inversion H'. Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  Case "->". intros Ex. inversion Ex as [x Hx].
    inversion Hx.
    SCase "left". left. exists x. apply H.
    SCase "right". right. exists x. apply H.
  Case "<-". intros EPx_or_EQx. inversion EPx_or_EQx.
    SCase "left". inversion H as [x Hx]. exists x.
      left. apply Hx.
    SCase "right". inversion H as [x HQx].
      exists x. right. apply HQx. Qed.
(** [] *)

(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 
*)

(** *** *)
(** 
It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)
*) 

(** *** *)
(** 
Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2".
    reflexivity.
  Case "k1 <> k2".
    reflexivity. Qed.
(** [] *)






(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_empty : all X P []
  | all_cons : forall (x : X) (l : list X), all X P l -> P x -> all X P (x :: l).


(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Definition pred_to_prop {X : Type} (test : X -> bool) : X -> Prop :=
  (fun x => test x = true).

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_specification : forall (X : Type) (test : X -> bool)
                                       (l : list X),
  forallb test l = true -> all X (pred_to_prop test) l.
Proof.
  intros X test l H. induction l as [| x l'].
  Case "[]". apply all_empty.
  Case "x :: l'". simpl in H.
    destruct (test x) eqn: Htest.
    SCase "true". simpl in H. apply IHl' in H. apply all_cons.
      apply H.
      unfold pred_to_prop. apply Htest.
    SCase "false". inversion H. Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive in_order_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | iom_empty : in_order_merge [] [] []
  | iom_list1 : forall (l l1 l2 : list X) (x : X),
                  in_order_merge l l1 l2 -> in_order_merge (x :: l) (x :: l1) l2
  | iom_list2 : forall (l l1 l2 : list X) (x : X),
                  in_order_merge l l1 l2 -> in_order_merge (x :: l) l1 (x :: l2).

Theorem filter_specification : forall (X : Type) (l : list X) (test : X -> bool),
  in_order_merge l (filter test l) (filter (complement test) l).
Proof.
  intros X l test. induction l as [| x l'].
  Case "[]". apply iom_empty.
  Case "x :: l'". destruct (test x) eqn:Hx.
    SCase "test x = true". simpl. rewrite -> Hx.
      assert (H': complement test x = false). unfold complement. rewrite -> Hx.
        reflexivity.
      rewrite -> H'. apply iom_list1. apply IHl'.
    SCase "test x = false". simpl. rewrite -> Hx.
      assert (H': complement test x = true). unfold complement. rewrite -> Hx.
        reflexivity.
      rewrite -> H'. apply iom_list2. apply IHl'. Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

Print subsequence.

Inductive subsequence' (X : Type) : list X -> list X -> Prop :=
    s_empty : forall l : list X, subsequence' X [] l
  | s_head : forall (n1 n2 : X) (l1 l2 : list X),
             n1 = n2 ->
             subsequence' X l1 l2 -> subsequence' X (n1 :: l1) (n2 :: l2)
  | s_add : forall (n : X) (l1 l2 : list X),
            subsequence' X l1 l2 -> subsequence' X l1 (n :: l2).

Theorem filter_specification2 : forall (X : Type) (l l': list X) (test : X -> bool),
  subsequence' X l' l -> forallb test l' = true -> subsequence' X l' (filter test l).
Proof.
  intros X l. induction l as [| x l''].
  Case "l = []". intros l' test Hsubs Htest.
    inversion Hsubs. simpl. apply s_empty.
  Case "l = x :: l''". intros l' test Hsubs Htest. destruct (test x) eqn: Hx.
    SCase "test x = true". simpl. rewrite -> Hx. inversion Hsubs.
      SSCase "l' = []". apply s_empty.
      SSCase "s_head". apply s_head. apply H2.
        Abort.
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs. induction xs as [| x' xs'].
  Case "xs = []". intros ys x assumption.
    simpl in assumption. right. apply assumption.
  Case "xs = x' :: xs'". intros ys x assumption.
    inversion assumption.
    SCase "ai_here". left. apply ai_here.
    SCase "ai_later". apply IHxs' in H0. inversion H0.
      SSCase "left". left. apply ai_later. apply H2.
      SSCase "right". right. apply H2. Qed.

Lemma appears_in__appears_in_app : forall (X : Type) (xs ys : list X) (x:X),
  appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs. induction xs as [| x' xs'].
  Case "xs = []". intros ys x assumption.
    simpl. apply assumption.
  Case "xs = x' :: xs'". intros ys x assumption.
    simpl. apply ai_later. apply IHxs'. apply assumption. Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs. induction xs as [| x' xs'].
  Case "xs = []". intros ys x assumption.
    simpl. inversion assumption.
    SCase "left". inversion H.
    SCase "right". apply H.
  Case "xs = x' :: xs'". intros ys x assumption. simpl. inversion assumption.
    SCase "left". inversion H.
      SSCase "ai_here". apply ai_here.
      SSCase "ai_later". apply ai_later. apply IHxs'. left. apply H1.
    SCase "right". apply ai_later. apply appears_in__appears_in_app.
      apply H. Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | dis_empty_left : forall l2 : list X, disjoint [] l2
  | dis_empty_right : forall l1 : list X, disjoint l1 []
  | dis_add_left : forall (l1 l2 : list X) (x : X), ~(appears_in x l2) ->
                                                    disjoint l1 l2 ->
                                                    disjoint (x :: l1) l2
  | dis_add_right : forall (l1 l2 : list X) (x : X), ~(appears_in x l1) ->
                                                     disjoint l1 l2 ->
                                                     disjoint l1 (x :: l2).

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats {X:Type} : list X -> Prop :=
  | nr_empty : no_repeats []
  | nr_add : forall (x:X) (l : list X), no_repeats l ->
                                        ~(appears_in x l) ->
                                        no_repeats (x :: l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)


Lemma disj_cons : forall (X:Type) (x : X) (l1 l2 : list X),
  disjoint (x::l1) l2 -> disjoint l1 l2.
Proof.
  intros X x l1. induction l1 as [| x' l1'].
  Case "l1 = []". intros l2 Hd. inversion Hd.
    apply dis_empty_left. apply dis_empty_left. apply dis_empty_left.
  Case "l1 = x' :: l1'". intros l2. induction l2 as [| x2 l2'].
    SCase "l2 = []". intros Hdisj. apply dis_empty_right.
    SCase "l2 = x2 :: l2'". intros Hdisj. inversion Hdisj.
      apply H3. apply dis_add_right. intros Hassumption.
        apply ai_later with (b:=x) in Hassumption. apply H2 in Hassumption.
        inversion Hassumption.
      apply IHl2'. apply H3. Qed.

Lemma app_empty : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  intros X l. induction l as [| x l'].
  Case "[]". reflexivity.
  Case "x :: l'". simpl. apply f_equal. apply IHl'. Qed.

Lemma disj_cons2 : forall (X:Type) (x : X) (l1 l2 : list X),
  disjoint l1 (x::l2) -> disjoint l1 l2.
Proof.
  intros X x l1 l2. generalize dependent l1. induction l2 as [| x2 l2].
  Case "l2 = []". intros l1 Hdisj. apply dis_empty_right.
  Case "l2 = x2 :: l2'". intros l1. induction l1 as [| x1 l1'].
    SCase "l1 = []". intros Hdisj. apply dis_empty_left.
    SCase "l1 = x1 :: l1'". intros Hdisj. inversion Hdisj.
      apply dis_add_left. intros contra. apply ai_later with (b:=x) in contra.
      apply H1 in contra. inversion contra.
      apply IHl1'. apply H3.
      apply H3. Qed.

Lemma disj_cons__not_appears : forall (X:Type) (x:X) (l1 l2 : list X),
  disjoint (x :: l1) l2 -> ~(appears_in x l2).
Proof.
  intros X x l1 l2. generalize dependent l1. induction l2 as [| x2 l2'].
  Case "l2 = []". intros l1 Hdisj. intros contra. inversion contra.
  Case "l2 = x2 :: l2'". intros l1 Hdisj. intros contra.
    inversion Hdisj. apply disj_cons2 in Hdisj. apply IHl2' in Hdisj.
    apply H1 in contra. inversion contra.
    apply disj_cons2 in Hdisj. apply IHl2' in Hdisj. inversion contra.
    SCase "ai_here". rewrite <- H5 in H2. assert (H' : appears_in x (x :: l1)).
      SSCase "assert". apply ai_here.
      apply H2 in H'. inversion H'.
    SCase "ai_later".
      apply Hdisj in H5. inversion H5. Qed.

Theorem no_repeats_disjoint_app_no_repeats : forall (X:Type) (l1 l2 : list X),
  no_repeats l1 -> no_repeats l2 -> disjoint l1 l2 -> no_repeats (l1 ++ l2).
Proof.
  intros X l1 l2. intros Hnr1 Hnr2 Hd.
  induction l1 as [| x l1'].
  Case "l1 = []".
    simpl. apply Hnr2.
  Case "l1 = x :: l1'".
    simpl. apply nr_add. apply IHl1'. inversion Hnr1. apply H1.
    inversion Hd. apply dis_empty_right. apply H3. apply dis_add_right.
      unfold not in H. unfold not. intros Happears.
      apply ai_later with (b:=x) in Happears. apply H in Happears.
      inversion Happears. apply disj_cons in H0. apply H0.
    intros contra. inversion Hd. rewrite <- H0 in contra.
      rewrite -> app_empty in contra. inversion Hnr1.
      apply H4 in contra. inversion contra.
      apply appears_in_app in contra. inversion contra.
      SCase "left". inversion Hnr1. apply H8 in H4. inversion H4.
      SCase "right". apply H1 in H4. inversion H4.
      rewrite <- H2 in contra. apply appears_in_app in contra.
      inversion contra. 
      SCase "left". inversion Hnr1. apply H7 in H3. inversion H3.
      SCase "right". apply disj_cons__not_appears in H0. inversion H3.
        SSCase "ai_here". assert (H': appears_in x0 (x :: l1')).
          SSSCase "assertion". rewrite <- H5. apply ai_here.
          apply H in H'. inversion H'.
        SSCase "ai_later". rewrite <- H6 in H3. rewrite <- H6 in H2.
          rewrite <- H6 in H0. rewrite <- H6 in contra. rewrite <- H6 in H5.
          apply H0 in H5. inversion H5. Qed.

Theorem disj_comm : forall (X:Type) (l1 l2 : list X),
  disjoint l1 l2 -> disjoint l2 l1.
Proof.
  intros X l1. induction l1 as [| x1 l1].
  Case "l1 = []". intros l2 Hdisj. apply dis_empty_right.
  Case "l1 = x1 :: l1'". intros l2 Hdisj. apply dis_add_right.
    intros contra. apply disj_cons__not_appears in Hdisj.
    apply Hdisj in contra. inversion contra. apply IHl1.
    apply disj_cons in Hdisj. apply Hdisj. Qed.
      
(** [] *)


(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  | nos_empty : nostutter []
  | nos_singleton : forall n : nat, nostutter [n]
  | nos_add : forall (n1 n2 : nat) (l : list nat), nostutter (n2 :: l) ->
                                                   n1 <> n2 ->
                                                   nostutter (n1 :: n2 :: l).


(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof.
  apply nos_add. apply nos_add. apply nos_add.
  apply nos_add. apply nos_add. apply nos_singleton.
  intros contra. inversion contra.
  intros contra. inversion contra.
  intros contra. inversion contra.
  intros contra. inversion contra.
  intros contra. inversion contra. Qed.

(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof.
  apply nos_empty. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. apply nos_singleton. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  intros contra. inversion contra. inversion H1. unfold not in H8.
  assert (H': 1 = 1). reflexivity. apply H8 in H'. inversion H'. Qed.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros X l1 l2. induction l1 as [| x1 l1'].
  Case "l1 = []". simpl. reflexivity.
  Case "l1 = x1 :: l1'". simpl. rewrite -> IHl1'. reflexivity.
    Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l. induction l as [| x' l'].
  Case "l = []". intros Ha. inversion Ha.
  Case "l = x' l'". intros Ha. inversion Ha.
    SCase "x = x'". exists []. exists l'.
      simpl. reflexivity.
    SCase "x <> x'". apply IHl' in H0. inversion H0 as [l1].
      inversion H2 as [l2]. exists (x' :: l1). exists l2.
      rewrite -> H3. simpl. reflexivity. Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_new : forall (x : X) (l : list X), appears_in x l ->
                                               repeats (x :: l)
  | repeats_add : forall (x : X) (l : list X), repeats l -> repeats (x :: l).


(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
  intros X l1. induction l1 as [|x l1'].
  Case "l1 = []".
    intros l2 EM Hlabels Hlen. inversion Hlen.
  Case "l1 = x1 :: l1'".
    intros l2 EM Hlabels Hlen.
    assert (H: appears_in x l1' \/ ~(appears_in x l1')). apply EM.
    inversion H as [HA | HnA].
    SCase "left".
      apply repeats_new. apply HA.
    SCase "right".
      unfold not in HnA.
      apply repeats_add.
      apply IHl1' with l2 in EM.
      apply EM.
      intros x' Ha. apply ai_later with (b:=x) in Ha. apply Hlabels in Ha.
      apply Ha.
      inversion Hlen. Abort.
      
    
(** [] *)

(* FILL IN HERE *)


(* $Date: 2014-02-22 09:43:41 -0500 (Sat, 22 Feb 2014) $ *)
