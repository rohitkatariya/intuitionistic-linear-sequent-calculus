(* Add LoadPath ".".  *)
(* Require Import Maps. *)
(* Compute examplemap "Church". *)
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
(* Require Export Coq.Strings.String. *)
(* From Coq Require Import Logic.FunctionalExtensionality. *)
From Coq Require Import Lists.List.
Import ListNotations.

Inductive P : Type :=
    (** Base symbols*)
    | one : P (** 1 *)
    | zero : P  (** 0 *)
    | top : P (** T *)
    | bot :P (** _|_*)
    
    (** Variable proposition*)
    | pvar : nat -> P  (* A *)

    (** Linear implication *)
    | imp:  P -> P -> P (** A --o B*)
    
    (** Conjunctions *)
    | tns: P->P->P (** A (x) B*)
    | amp : P->P->P (** A & B*)
    
    (** Disjunction *)
    | pls : P->P->P (** A (+) B*)
    | par : P->P->P (** A &' B*)

    (** Exponentials *)
    | bng : P -> P (** !A *)
    | whn : P -> P (** ?A*)
    .

Fixpoint eqP (p1 p2 : P) : bool :=
    (** required for exchange rule*)
    match p1, p2 with
    | one,one => true
    | zero,zero  => true
    | top,top  => true
    | bot,bot  => true
    
    (** Variable proposition*)
    | (pvar n1), (pvar n2) => n1 =? n2

    (** Linear implication *)
    | (imp A1 B1),(imp A2 B2) => andb (eqP A1 A2)  (eqP B1 B2)
    
    (** Conjunctions *)
    | (tns A1 B1),(tns A2 B2) => andb (eqP A1 A2)  (eqP B1 B2)
    | (amp A1 B1),(amp A2 B2) => andb (eqP A1 A2)  (eqP B1 B2)
    
    (** Disjunction *)
    | (pls A1 B1),(pls A2 B2) => andb (eqP A1 A2)  (eqP B1 B2)
    | (par A1 B1),(par A2 B2) => andb (eqP A1 A2)  (eqP B1 B2)
    
    (** Exponentials *)
    | (bng A), (bng B) => eqP A B
    | (whn A), (whn B) => eqP A B

    | _, _ => false
    end.


Notation "A --o B" := (imp A B) (at level 98, left associativity).
Notation "A (x) B" := (tns A B) (at level 98, left associativity).
Notation "A & B" := (amp A B) (at level 98, left associativity).
Notation "A (+) B" := (pls A B) (at level 98, left associativity).
Notation "A &' B" := (par A B) (at level 98, left associativity).
Notation "! A" := (bng A) (at level 98, left associativity).
Notation "? A" := (whn A) (at level 98, left associativity).

Definition seq := list P.
(** Intutionistic Sequent calculus*)

Fixpoint inGammaSeq (A:P) (G:seq): bool :=
    match G with 
    | [] => false
    | h::t => if (eqP h A) 
                then true
                else inGammaSeq A t
    end.

Fixpoint removeFromGammaSeq (A:P) (G:seq): seq :=
    match G with
    | [] => []
    | h::t => if eqP h A
        then t
        else h::(removeFromGammaSeq A t)
    end.


Fixpoint CompareGammaSeq (G1:seq) (G2:seq): bool:=
    (** compares sequents ignoring reordering*)
    match G1 with
        | [] => match G2 with
                |[] => true
                | _ => false
        end
        | h1::t1 => match (inGammaSeq h1 G2) with
            | false => false
            | true => (CompareGammaSeq t1 (removeFromGammaSeq h1 G2))
        end
    end.

Fixpoint checkAllBangSeq (G1:seq) : bool:=
    (* checks that all the elements in G are bang elements *)
    match G1 with
        | [] => true
        | h::t => match h with
            | bng _ => (checkAllBangSeq t)
            | _ => false
        end
    end.

Inductive toSeqRules : seq -> P -> Prop :=
    | seq_id_rule : forall (A: P) ,
        toSeqRules ([ A ]) A  

    | seq_exch_rule : forall (gamma delta: seq) ( C: P) ,
        (CompareGammaSeq gamma delta) =true -> 
        toSeqRules gamma  C ->
        toSeqRules delta C

    | seq_cut_rule : forall (gamma delta: seq)  ( A B: P) ,
        toSeqRules gamma A ->
        toSeqRules (A::delta) B ->
        toSeqRules (gamma ++ delta) B

   


    | seq_rule1R:
        toSeqRules [] one
        
     | seq_rule1L : forall (gamma : seq)  ( A: P) ,
        toSeqRules gamma   A ->
        toSeqRules ( one::gamma )  A 
    
    | seq_ruletensorR : forall (gamma delta : seq)  ( A B: P) ,
        toSeqRules gamma  A ->
        toSeqRules delta  B ->
        toSeqRules (gamma++delta)  (A (x) B) 
    
    | seq_ruletensorL : forall (gamma : seq) (A B C: P) ,
        toSeqRules ( A::B::gamma)  C ->
        toSeqRules ( (A (x) B)::gamma ) C

    | seq_ruleimpliesR : forall (gamma : seq)  ( A B C: P) ,
        toSeqRules ( A::gamma) B ->
        toSeqRules gamma (A --o B)
    
    | seq_ruleimpliesL : forall (gamma delta : seq) ( A B C: P) ,
        toSeqRules gamma A ->
        toSeqRules ( B::delta) C ->
        toSeqRules ( (A--oB)::gamma ++ delta ) C
    
    | seq_ruleampR : forall (gamma : seq)  ( A B : P) ,
        toSeqRules gamma A ->
        toSeqRules gamma B ->
        toSeqRules gamma (A & B)


    | seq_ruleampLl : forall (gamma : seq) ( A B C: P) ,
        toSeqRules (A::gamma)  C ->
        toSeqRules ((A&B)::gamma)  C 
        
    | seq_ruleampLr : forall (gamma : seq) ( A B C: P) ,
        toSeqRules (B::gamma) C ->
        toSeqRules ((A&B)::gamma) C
        
    | seq_ruleplusRl : forall (gamma  : seq) ( A B: P) ,
        toSeqRules gamma A ->
        toSeqRules gamma (A (+) B)
    
    | seq_ruleplusRr : forall (gamma  : seq) ( A B: P) ,
        toSeqRules gamma B ->
        toSeqRules gamma (A (+) B)
    
    | seq_ruleplusL : forall (gamma : seq)  ( A B C: P) ,
        toSeqRules (A::gamma) C ->
        toSeqRules (B::gamma) C ->
        toSeqRules ( (A(+)B)::gamma) C
    
    | seq_rulebangR : forall (gamma : seq)( A : P) ,
        (checkAllBangSeq gamma) = true ->
        toSeqRules gamma A ->
        toSeqRules gamma (!A) 
        
    | seq_ruleDereliction : forall (gamma : seq) (A B:P),
        toSeqRules ( A::gamma) B ->
        toSeqRules ((!A)::gamma) B 
    
    | seq_ruleContraction: forall (gamma : seq) (A B:P),
            toSeqRules ( (!A)::(!A)::gamma) B ->
            toSeqRules ( (!A)::gamma) B 

    | seq_ruleWeakening: forall (gamma : seq)  (A B:P),
        toSeqRules gamma B ->
        toSeqRules ( (!A)::gamma) B 
    .

Inductive pattern:Type :=
    (* Borrowed from Madhukar *)
    | pt_b_ : pattern (*_ pattern*)
    | pt_st : pattern (* * pattern*)
    | pt_xXy : pattern (*tensor pattern*)
    | pt_fst_ : pattern (*<x,_> pattern*) 
    | pt_snd_ : pattern (*<_,y> pattern*)
    | pt_ofc : pattern (*!x pattern*)
    | pt_xAty : pattern (*x@y pattern*).

Fixpoint eqPtn (p1 p2:pattern):bool:=
    match p1,p2 with 
    | pt_b_,pt_b_ => true
    | pt_st ,pt_st => true
    | pt_xXy ,pt_xXy => true
    | pt_fst_ ,pt_fst_ => true
    | pt_snd_ ,pt_snd_ => true
    | pt_ofc ,pt_ofc => true
    | pt_xAty ,pt_xAty => true
    | _,_ => false
    end.
Inductive l_term:Type :=
    | lstar : l_term
    | lvar : nat -> l_term
    | abs : l_term -> l_term
    | app : l_term -> l_term -> l_term
    | letin : l_term ->  pattern -> l_term -> l_term
    
    (**  ** @ etc *)
    | tsrPair : l_term -> l_term -> l_term  (** (x,y) === x ** y*)
    | atPair : l_term -> l_term -> l_term (** <x,y> === x @ y*)

    (** inl inr*)
    | inl : l_term -> l_term  
    | inr : l_term -> l_term  

    (* Case z of inl(x) -> e1 inr(y) -> e2 *)
    | caseof : nat -> nat -> l_term -> nat -> l_term -> l_term  
    (** !t *)
    | lbng : l_term -> l_term  
    .

Fixpoint eqlc (e1 e2:l_term) : bool:=
    match e1, e2 with
    | lstar,lstar => true
    | lvar n1, lvar n2 => (n1=?n2)
    | abs e11,abs e21 => (eqlc e11 e21) 
    | app e11 e12, app e21 e22=>  (andb (eqlc e11 e21) (eqlc e12 e22) )
    | letin z1 ptn1 t1,letin z2 ptn2 t2 => if (eqPtn ptn1 ptn2) 
        then  (andb (eqlc z1  z2) (eqlc t1 t2))
        else false
    
    (**  ** @ etc *)
    | tsrPair e11 e12 , tsrPair e21 e22 => (andb (eqlc e11 e21) (eqlc e12 e22) )  
    | atPair e11 e12 , atPair e21 e22 => (andb (eqlc e11 e21) (eqlc e12 e22) )  

    (** inl inr*)
    | inl e11, inl e21 => (eqlc e11 e21) 
    | inr e11, inr e21 => (eqlc e11 e21) 

    (* Case z of inl(x) -> e1 inr(y) -> e2 *)
    | caseof n1 x1 e11 y1 e12,caseof n2 x2 e21 y2 e22 => if (andb (n1=?n2) (x1 =? x2) )
        then if (y1 =? y2) 
            then (andb (eqlc e11 e21) (eqlc e12 e22) )  
            else false
        else false
    (** !t *)
    | lbng e11, lbng e21 => (eqlc e11 e21) 
    | _,_ => false
    end.
(* Compute (tsrPair lstar lstar ).
Compute (3,4). *)
Notation " a ** b " := ( tsrPair lstar lstar ) (at level 98, left associativity).
Notation " a @ b " := ( atPair lstar lstar ) (at level 98, left associativity).
    

(**START COPY from assignment 1*)

Fixpoint db_shift_i_co (i :nat) (co:nat) (e : l_term) : l_term :=
  match e with
    | lstar => lstar
    | lvar n => if n <? co then (lvar n) else lvar( n + i)
    | abs e' => abs (db_shift_i_co i (co+1) e')
    | app e1 e2 => app (db_shift_i_co i co e1) (db_shift_i_co i co e2)
    | letin n ptn e => letin n ptn (db_shift_i_co i co e)
    
    (**  ** @ etc *)
    | tsrPair e1 e2 => tsrPair (db_shift_i_co i co e1) (db_shift_i_co i co e2)
    | atPair e1 e2  => atPair (db_shift_i_co i co e1) (db_shift_i_co i co e2)

    (** inl inr*)
    | inl e => inl (db_shift_i_co i co e)
    | inr e => inr (db_shift_i_co i co e)

    (* Case z of inl(x) -> e1 inr(y) -> e2 *)
    | caseof n x e1 y e2 => caseof n x (db_shift_i_co i co e1) y (db_shift_i_co i co e2 )
    (** !t *)
    | lbng e1 => lbng  (db_shift_i_co i co e1)
  end.

Fixpoint db_shift_left_i_co (i :nat) (co:nat) (e : l_term) : l_term :=
  match e with 
    | lstar => lstar
    | lvar n => if n <? co then (lvar n) else lvar( n - i )
    | abs e' => abs (db_shift_left_i_co i (co + 1) e')
    | app e1 e2 => app (db_shift_left_i_co i co e1) (db_shift_left_i_co i co e2)

    | letin n ptn e => letin n ptn (db_shift_left_i_co i co e)
    (**  ** @ etc *)
    | tsrPair e1 e2 => tsrPair (db_shift_left_i_co i co e1) (db_shift_left_i_co i co e2)
    | atPair e1 e2  => atPair (db_shift_left_i_co i co e1) (db_shift_left_i_co i co e2)

    (** inl inr*)
    | inl e => inl (db_shift_left_i_co i co e)
    | inr e => inr (db_shift_left_i_co i co e)

    (* Case z of inl(x) -> e1 inr(y) -> e2 *)
    | caseof n x e1 y e2 => caseof n x (db_shift_left_i_co i co e1) y (db_shift_left_i_co i co e2 )
    (** !t *)
    | lbng e1 => lbng  (db_shift_left_i_co i co e1)
  end.

Fixpoint substitute_lterm (e2 : l_term) (fr_x : nat)  (e1 :l_term) :l_term :=
  if ( eqlc e1 (lvar fr_x)) then e2 else 
    match e1 with 
      | lvar x => e1
      | lstar => lstar
      | abs e11 => abs (substitute_lterm (db_shift_i_co 1 0 e2) (fr_x+1)  e11)
      | app e11 e12 => app (substitute_lterm e2 fr_x e11) (substitute_lterm e2 fr_x e12 )
      | letin n ptn e11 => letin n ptn (substitute_lterm e2 fr_x e11)
      (**  ** @ etc *)
      | tsrPair e11 e12 => tsrPair (substitute_lterm e2 fr_x e11) (substitute_lterm e2 fr_x e12)
      | atPair  e11 e12  => atPair (substitute_lterm e2 fr_x e11) (substitute_lterm e2 fr_x e12)
  
      (** inl inr*)
      | inl e11 => inl (substitute_lterm e2 fr_x e11)
      | inr e11 => inr (substitute_lterm e2 fr_x e11)
  
      (* Case z of inl(x) -> e1 inr(y) -> e2 *)
      | caseof n x e11 y e12 => caseof n x (substitute_lterm e2 fr_x e11) y (substitute_lterm e2 fr_x e12)
      (** !t *)
      | lbng e11 => lbng  (substitute_lterm e2 fr_x e11)
      end.

Definition substitution_under_lambda M N := 
        (  db_shift_left_i_co 1 0 ( substitute_lterm ( db_shift_i_co 1 0 N) 0  M ) ).

Definition make_abs (t:l_term):l_term :=
        abs (db_shift_i_co 1 0 t).
(** END COPY from assignment 1 *)




Definition sequent := list (nat * P).

Fixpoint fetchFromGamma (x:nat) (G:sequent): (option P) :=
    match G with 
    | [] => None
    | h::t => if (fst h)=?x 
                then (Some (snd h))
                else   fetchFromGamma x t
    end.

Fixpoint removeFromGamma (x:nat) (G:sequent): sequent :=
    match G with
    | [] => []
    | h::t => if (fst h) =? x
        then t
        else h::(removeFromGamma x t)
    end.


Fixpoint CompareGamma (G1:sequent) (G2:sequent): bool:=
    (** compares sequents ignoring reordering*)
    match G1 with
        | [] => match G2 with
                |[] => true
                | _ => false
        end
        | h1::t1 => match (fetchFromGamma (fst h1) G2) with
            | None => false
            | Some p => if (eqP p (snd h1)) 
                then (CompareGamma t1 (removeFromGamma (fst h1) G2) )
                else false
        end
    end.


Inductive toLinRules : sequent -> l_term -> P -> Prop :=
    (* |(type_of gamma e1 (  type_to_type_sc (t1 -a> t2) )) *)
    | id_rule : forall (x:nat) (A: P) ,
        toLinRules ([ (x,A) ]) (lvar x) A  

    | exch_rule : forall (gamma delta: sequent) (t:l_term) ( C: P) ,
        (CompareGamma gamma delta) =true -> 
        toLinRules gamma  t C ->
        toLinRules delta  t C

    | cut_rule : forall (gamma delta: sequent) (x:nat) (t u:l_term) ( A B C: P) ,
        toLinRules gamma t A ->
        toLinRules ((x,A)::delta) u B ->
        toLinRules (gamma ++ delta) (substitute_lterm t x u) B

    | rule1R :  
        toLinRules [] lstar one

    | rule1L : forall (gamma : sequent) (z:nat) (t :l_term) ( A: P) ,
        toLinRules gamma  t A ->
        toLinRules ( (z,one)::gamma )  (letin (lvar z) pt_st t) A 
    
    | ruletensorR : forall (gamma delta : sequent)  (t u :l_term) ( A B: P) ,
        toLinRules gamma  t A ->
        toLinRules delta  u B ->
        toLinRules (gamma++delta)  (t ** u) (A (x) B) 
    
    | ruletensorL : forall (gamma : sequent) (x y z:nat) (t :l_term) ( A B C: P) ,
        toLinRules ( (x,A)::(y,B)::gamma)  t C ->
        toLinRules ( (z, (A (x) B))::gamma )  (letin (lvar z) pt_xXy t) C

    | ruleimpliesR : forall (gamma : sequent) (x y z:nat) (t :l_term) ( A B C: P) ,
        toLinRules ( (x,A)::gamma)  t B ->
        toLinRules gamma (make_abs t) (A --o B)
    
    | ruleimpliesL : forall (gamma delta : sequent) (x f:nat) (t u:l_term) ( A B C: P) ,
        toLinRules gamma  t A ->
        toLinRules ( (x,B)::delta)  u C ->
        toLinRules ( (f,(A--oB))::gamma ++ delta ) ( substitute_lterm (app (lvar f) t) x u ) C
    
    | ruleampR : forall (gamma : sequent)  (t u:l_term) ( A B : P) ,
        toLinRules gamma  t A ->
        toLinRules gamma  u B ->
        toLinRules gamma  (t@u) (A & B)


    | ruleampLl : forall (gamma : sequent) (x z:nat) (t :l_term) ( A B C: P) ,
        toLinRules ((x,A)::gamma)  t C ->
        toLinRules ((z, (A&B) )::gamma)  (letin (lvar z) pt_fst_ t) C

    | ruleampLr : forall (gamma : sequent) (y z:nat) (t :l_term) ( A B C: P) ,
        toLinRules ((y,B)::gamma)  t C ->
        toLinRules ((z, (A&B) )::gamma)  (letin (lvar z) pt_snd_ t) C

    | ruleplusRl : forall (gamma  : sequent)  (t :l_term) ( A B: P) ,
        toLinRules gamma  t A ->
        toLinRules gamma  (inl t) (A (+) B)
    
    | ruleplusRr : forall (gamma  : sequent)  (t :l_term) ( A B: P) ,
        toLinRules gamma  t B ->
        toLinRules gamma  (inr t) (A (+) B)
    
    | ruleplusL : forall (gamma : sequent) (x y z:nat) (e1 e2 :l_term) ( A B C: P) ,
        toLinRules ((x,A)::gamma)  e1 C ->
        toLinRules ((y,B)::gamma)  e2 C ->
        toLinRules ((z, (A (+)B) )::gamma)  (caseof z x e1 y e2) C
    
    | rulebangR : forall (gamma : sequent) (t :l_term) ( A : P) ,
        (* (allbang gamma) = true -> *)
        toLinRules gamma t A ->
        toLinRules gamma (lbng t) (!A) 
        
    | ruleDereliction : forall (gamma : sequent) (t :l_term) (  z x: nat) (A B:P),
        toLinRules ((x, A)::gamma) t B ->
        toLinRules ((z,(!A))::gamma) (letin (lvar z) pt_ofc t) B 

    
    | ruleContraction: forall (gamma : sequent) (t :l_term) ( z x y: nat) (A B:P),
        toLinRules ( (x,(!A))::(y,(!A))::gamma) t B ->
        toLinRules ( (z, (!A))::gamma) (letin (lvar z) pt_xAty t ) B

    | ruleWeakeing: forall (gamma : sequent) (t :l_term) (  z x: nat) (A B:P),
        toLinRules gamma t B ->
        toLinRules ( (x, (!A))::gamma) (letin (lvar z) pt_b_ t ) B
    .

(** Operation Semantics *)

Inductive  opSemantics : l_term -> l_term  -> Prop :=
    | starSemantics :
        opSemantics lstar lstar

    | starDeconstructionSemantics: forall (t:nat) (u c:l_term),
        opSemantics (lvar t) lstar ->
        opSemantics u c -> 
        opSemantics (letin (lvar t) pt_st u) c

    | tensorPairingSemantics: forall (t u c d:l_term),
        opSemantics t c ->
        opSemantics u d ->
        opSemantics (t ** u) ( c ** d)
    | lazyPairSemantics : forall (t u :l_term),
        opSemantics (t @ u) (t @ u)
    
    | bangSemantics: forall (t:l_term),
    opSemantics (lbng t) (lbng t)
    
    | bangWeakeningSemantics: forall (t u v c :l_term),
        opSemantics t (lbng v) ->
        opSemantics u c ->
        opSemantics (letin t pt_b_ u) c

    | functionSemantics: forall (t : l_term),
    opSemantics ( abs t)  (abs t)
    
    | functionCallSemantics: forall (t v u c d:l_term),
        opSemantics t (abs v) ->
        opSemantics u c -> 
        opSemantics (substitution_under_lambda v c) d ->
        opSemantics (app t u) d
    | tensorDeconstructionSemantic: forall (x y t:nat) ( u c d e:l_term),
        opSemantics (lvar t) (c ** d) ->
        opSemantics   (substitute_lterm d y (substitute_lterm c x u))  e ->
        opSemantics (letin (lvar t) pt_xXy u) e
    
    
    
    | lazyPairDeconstructionLSemantics : forall (x:nat) (t u v w c d :l_term),
        opSemantics t (v@w) ->
        opSemantics v c -> 
        opSemantics (substitute_lterm c x u) d ->
        opSemantics (letin t pt_fst_ u) d
    | lazyPairDeconstructionRSemantics : forall (y:nat) (t u v w c d :l_term),
        opSemantics t (v@w) ->
        opSemantics w c -> 
        opSemantics (substitute_lterm c y u) d ->
        opSemantics (letin t pt_snd_ u) d
    
    | inlSemantics: forall  (t c :l_term),
        opSemantics t c ->
        opSemantics (inl t) (inl c) 

    | inrSemantics: forall  (t c :l_term),
        opSemantics t c ->
        opSemantics (inr t) (inr c) 
    | caseLSemantics: forall (t x y:nat) (u v c d:l_term), 
        opSemantics (lvar t) (inl c) ->
        opSemantics (substitute_lterm c x u) d ->
        opSemantics (caseof t x u y v ) d  
    
    | caseRSemantics: forall (t x y:nat) (u v c d:l_term), 
        opSemantics (lvar t) (inr c) ->
        opSemantics (substitute_lterm c y v) d ->
        opSemantics (caseof t x u y v ) d  
    
    
    | bangDerelictionSemantics: forall (x:nat) (t u v c d : l_term) ,
        opSemantics t (lbng v) ->
        opSemantics v c ->
        opSemantics (substitute_lterm c x u) d ->
        opSemantics (letin t pt_ofc u) d
    
    | bangContractionSemantics: forall (x y:nat) (t u v c:l_term),
        opSemantics t (lbng v) ->
        opSemantics (substitute_lterm (lbng v) y (substitute_lterm (lbng v) x u)) c -> 
        opSemantics (letin t pt_xAty u) c
        .

Check eqb_refl.
Theorem eqb_refl2 : forall n : nat,
  true = (n =? n).
Proof.
  intros n. induction n. simpl. reflexivity.
  simpl. rewrite <- IHn. reflexivity. Qed.

Theorem  eqlc_refl: forall (t:l_term),
eqlc t t= true.
Proof.
    simpl.  induction t.
        -- simpl. reflexivity.
        -- simpl. rewrite <- eqb_refl2. reflexivity.
        -- simpl. Admitted.



Lemma DeterminacyLemma: forall (t c d:l_term) , 
    opSemantics t c -> 
    opSemantics t d -> 
    (eqlc c d) = true.
Proof.
 intros t c d.
 intros H1. generalize d.
 induction H1.
    -intros d1 H2. 
        inversion H2. 
        simpl. 
        reflexivity.
    - intros d1 H2. 
        inversion H2. 
        apply IHopSemantics2. 
        trivial.
    - intros d1 H2. 
        inversion H2. 
        reflexivity.
    - intros d1 H2. 
        inversion H2. 
        reflexivity.
    -intros d1 H2. 
        inversion H2.
        simpl. 
        apply eqlc_refl.
    - intros d1 H2.
        inversion H2. 
        apply IHopSemantics2. 
        trivial.
    - intros d1 H2.
    inversion H2. simpl. apply eqlc_refl.
    - intros d1 H2.
    inversion H2. apply IHopSemantics3.
     Admitted. 
 (*
 intros d1 H2. inversion H2. 
 destruct H1 eqn:E.
 destruct H2 eqn:E2.
 - simpl. reflexivity.
   *)
(*  
Qed.   *)