(* BEGIN FIX *)
(**
  A beandando ket reszbol all:
  - Az elso resz (1-7 feladatok) 4 pontot er, az itt elert pontszam szamit
    a "beadando" kategoria pontszamanak.
  - A masodik resz (8-11 feladatok) 2 pontot er, az itt elert pontszam a
    plusz-minuszok kategoriajahoz adodik hozza. Ezzel tulajdonkeppen ket
    plusz-minuszt lehet javitani/potolni. (Viszont tovabbra is max 3
    alkalommal lehet hianyozni a gyakorlatokrol!)

  A beadandót meg kell védeni személyesen (pl. valamelyik gyakorlat után).
*)

From Coq Require Import Strings.String
                        Arith.PeanoNat.

Definition X:string := "X"%string.
Definition Y:string := "Y"%string.
Definition Z:string := "Z"%string.

Inductive AExp : Set :=
| ALit (n : nat)
| AVar (s : string)
| APlus (a1 a2 : AExp)
(* END FIX *)
(** 1. feladat: (0.25 pont)
    Egeszitsd ki a kifejezesnyelvet a let kifejezessel (`let x := a1 in a2`)!
    Legyen a konstruktor neve `ALet`!
*)
| ALet (x: string) (a1 a2: AExp)
.

(* BEGIN FIX *)
Definition ex1 := ALet Y (ALit 0) (APlus (AVar Y) (AVar X)).
Definition ex2 := ALet X (APlus (ALit 1) (AVar X)) (AVar X).
Definition ex3 := APlus (ALet X (ALit 0) (APlus (AVar X) (ALit 5)))
                        (AVar X).
Definition ex4 := ALet X (AVar Y)
                       (ALet Y (ALit 10)
                             (ALet X (AVar Y) (AVar X))).

Definition state := string -> nat.

Definition empty : state := fun x => 0.

Definition update (x : string)(n : nat)(s : state) : state :=
  fun (y : string) =>
    match string_dec x y with
    | left _  => n
    | right _ => s y
    end.

Definition aState : state := 
fun x =>
  match x with
  | "X"%string => 1
  | "Y"%string => 2
  | "Z"%string => 42
  | _ => 0
  end
.

Fixpoint aeval (a : AExp) (s : state) : nat :=
match a with
| ALit n => n
| AVar x => s x
| APlus a1 a2 => aeval a1 s + aeval a2 s
(* END FIX *)
(** 2. feladat: (0.25 pont)
    Ertelmezd a denotacios szemantikat a `let` kifejezesre, ugy hogy az alabbi
    tesztek lefussanak! A `let` kifejezes `let x := a1 in a2` nevkotest fejez
    ki, azaz eloszor kiertekeli `a1`-et a kezdeti allapotban, majd `a2`-t a
    kezdeti allapot frissitett valtozataban, ahol az `x` valtozo erteke az
    `a1` kifejezes eredmenye.
*)
| ALet x a1 a2 => aeval a2 (update x (aeval a1 s) s)
end.

(* BEGIN FIX *)

Goal aeval ex1 empty = 0.
Proof. cbn. reflexivity. Qed.
Goal aeval ex1 aState = 1.
Proof. cbn. reflexivity. Qed.
Goal aeval ex1 (update Y 10 empty) = 0.
Proof. cbn. reflexivity. Qed.
Goal forall s, aeval ex2 s = 1 + s X.
Proof. intro. cbn. reflexivity. Qed.
Goal forall s, aeval ex3 s = 5 + s X.
Proof. intro. cbn. reflexivity. Qed.
Goal forall s, aeval ex4 s = 10.
Proof. intro. cbn. reflexivity. Qed.

Fixpoint optim (a : AExp) : AExp :=
match a with
| ALit n => ALit n
| AVar x => AVar x
| APlus a1 a2 => APlus (optim a1) (optim a2)
| ALet x a1 (AVar y) =>
  if string_dec x y
  then a1
  else ALet x (optim a1) (AVar y)
| ALet x a1 a2 => ALet x (optim a1) (optim a2)
end.

Lemma update_eq :
  forall x n s, update x n s x = n.
Proof.
  intros.
  unfold update. destruct string_dec.
  * reflexivity.
  * exfalso. apply n0. reflexivity.
Qed.

Lemma update_neq :
  forall x n s y, x <> y -> update x n s y = s y.
Proof.
  intros. unfold update. destruct string_dec.
  * rewrite e in H. exfalso. apply H. reflexivity.
  * reflexivity.
Qed.

Theorem optim_sound :
  forall a s, aeval a s = aeval (optim a) s.
(* END FIX *)
(** 3. feladat: (0.5 pont)
    Bizonyitsd be a fenti optimalizacio helyesseget!
*)
Proof.
(* Tipp: ALet eseten segithet a `remember` vagy a `simpl in *` taktika!
   Tipp: Lehet esetszetvalasztast vegezni `string_dec x y` szerint is!
   Tipp: Szukseged lehet a fenti ket lemmara!
*)
  intro a.
  induction a.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl in *. intro s. rewrite IHa1, IHa2. reflexivity.
  * simpl in *; intro s. destruct a2.
    - reflexivity.
    - destruct (string_dec x s0).
      + simpl in *. rewrite e. apply update_eq.
      + simpl in *. rewrite IHa1. reflexivity.
    - simpl in *. rewrite IHa1. rewrite <- IHa2. reflexivity.
    - simpl. rewrite IHa1. rewrite <- IHa2. reflexivity.
Qed.

(* BEGIN FIX *)
Module SmallStep.

Reserved Notation "| a , st | => v" (at level 60).
Inductive eval_smallstep : AExp -> state -> AExp -> Prop :=

| seval_var x s :
  (* ------------------------ *)
    | AVar x, s | => ALit (s x)

| seval_plus_lhs a1 a1' a2 s:
     | a1, s | => a1' ->
  (* ---------------------------------- *)
     | APlus a1 a2, s | => APlus a1' a2

| seval_plus_rhs n a2' a2 s:
     | a2, s | => a2' ->
  (* ---------------------------------------------- *)
     | APlus (ALit n) a2, s | => APlus (ALit n) a2'

| seval_plus n1 n2 s :
  (* ------------------------------------------------- *)
    | APlus (ALit n1) (ALit n2), s | => ALit (n1 + n2)

(** 4. feladat: (1 pont)
    Add meg a `let` kifejezes small-step szemantikajat!
    Tipp: Szukseg lehet ket kiertekelest propagalo szabalyra
    (mint a fenti `seval_plus_lhs`, `seval_plus_rhs`)! Ezzel tudod
    kifejezni, hogy a masodik reszkifejezes egy frissitett kornyezetben
    ertekelodjon ki!

    Megjegyzes: a `let` kifejezesnek ilyen modon megadott szemantikaja
    nem standard. A standard megoldashoz lasd a Calculus of Closures
    szemantikahoz kapcsolodo feladatot.
*)
(* END FIX *)
| seval_let_bind x a1 a1' a2 s :
    | a1, s | => a1' ->
  (* ------------------------------------------------- *)
    | ALet x a1 a2, s | => ALet x a1' a2

| seval_let_body x a2 a2' n s :
   | a2, update x n s | => a2' ->
  (* ------------------------------------------------- *)
  | ALet x (ALit n) a2, s | => ALet x (ALit n) a2'

| seval_let_finish x s n m :

  (* ------------------------------------------------- *)
  | ALet x (ALit n) (ALit m), s | => (ALit m)
  

(* BEGIN FIX *)
where "| a , st | => v" := (eval_smallstep a st v).

Reserved Notation "| a , st | =>* v" (at level 60).
Inductive eval_smallstep_rtc : AExp -> state -> AExp -> Prop := 

| seval_refl a s :
  | a , s | =>* a
| seval_trans a a' a'' s :
  | a, s | => a' -> | a', s | =>* a'' ->
(* ------------------------------------*)
            | a, s | =>* a''

where "| a , st | =>* v" := (eval_smallstep_rtc a st v).


(** 5. feladat: (1 pont)
    Bizonyitsd a kovetkezo teszteseteket!
*)
Goal | ex1, aState | =>* ALit 1.
(* END FIX *)
Proof.
  unfold ex1.
  eapply seval_trans.
  * apply seval_let_body. apply seval_plus_lhs. apply seval_var.
  * eapply seval_trans.
    + apply seval_let_body. apply seval_plus_rhs. apply seval_var.
    + eapply seval_trans.
      - apply seval_let_body. apply seval_plus.
      - eapply seval_trans.
        ** apply seval_let_finish.
        ** simpl. apply seval_refl. 
Qed.

(* BEGIN FIX *)
Goal | (APlus (ALet X (ALit 1) (AVar X)) (AVar X)), empty | =>* ALit 1.
(* END FIX *)
Proof.
  eapply seval_trans.
  * apply seval_plus_lhs. apply seval_let_body. apply seval_var.
  * eapply seval_trans.
    + apply seval_plus_lhs. apply seval_let_finish.
    + eapply seval_trans.
      - apply seval_plus_rhs. apply seval_var.
      - eapply seval_trans.
        ** apply seval_plus.
        ** apply seval_refl.
Qed.

(* BEGIN FIX *)
Theorem smallstep_trans:
  forall a1 a2 a3 s,
    | a1, s | =>* a2 ->
    | a2, s | =>* a3 ->
    | a1, s | =>* a3.
Proof.
  intros. revert a3 H0.
  induction H; intros.
  * assumption.
  * apply IHeval_smallstep_rtc in H1.
    eapply seval_trans.
    + exact H.
    + exact H1.
Qed.

Lemma seval_plus_lhs_any a1 a1' a2 s:
  | a1, s | =>* a1' ->
  | APlus a1 a2, s | =>* APlus a1' a2.
Proof.
  intro. induction H.
  * apply seval_refl.
  * eapply seval_trans.
    + apply seval_plus_lhs. exact H.
    + exact IHeval_smallstep_rtc.
Qed.

Lemma seval_plus_rhs_any a2 a2' n s:
  | a2, s | =>* a2' ->
  | APlus (ALit n) a2, s | =>* APlus (ALit n) a2'.
Proof.
  intro.
  induction H.
  * apply seval_refl.
  * eapply seval_trans.
    + apply seval_plus_rhs. exact H.
    + exact IHeval_smallstep_rtc.
Qed.

(**
  6. feladat (0.5 pont): Bizonyitsd az alabbi lemmakat!
  Tipp: Meritsd otletet a fenti lemmak bizonyitasabol.
  Tipp: A masodik tetelhez szukseged lehet `dependent induction`-re!
*)
Lemma seval_let_lhs_any a1 a1' a2 x s:
  | a1, s | =>* a1' ->
  | ALet x a1 a2, s | =>* ALet x a1' a2.
(* END FIX *)
Proof.
  intro.
  induction H.
  * apply seval_refl.
  * eapply seval_trans.
    + apply seval_let_bind. exact H.
    + exact IHeval_smallstep_rtc.
Qed.

(* BEGIN FIX *)
Require Import Coq.Program.Equality.
Lemma seval_let_rhs_any n a2 a2' x s:
  | a2, update x n s | =>* a2' ->
  | ALet x (ALit n) a2, s | =>* ALet x (ALit n) a2'.
(* END FIX *)
Proof.
  intro.
  dependent induction H.
  * apply seval_refl.
  * eapply seval_trans.
     - apply seval_let_body. exact H.
     - eapply smallstep_trans.
        + apply IHeval_smallstep_rtc. reflexivity.
        + apply seval_refl.
Qed.

(* BEGIN FIX *)
(**
  7. feladat (0.5 pont): Bizonyitsd be, hogy a small-step szemantika
  kifejezi a denotacios szemantikat!

  Tipp: A tetel bizonyitasahoz szukseged lesz az elozo 5 tetel
  kombinaciojara! Gondold vegig eloszor "papiron" a bizonyitast!
*)
Theorem denot_to_smallstep:
  forall a s, | a, s | =>* ALit (aeval a s).
(* END FIX *)
Proof.
  intro.
  induction a.
  * simpl. apply seval_refl.
  * intro. simpl. apply (seval_trans _ (ALit (s0 s))).
    + apply seval_var.
    + apply seval_refl. 
  * intro. eapply smallstep_trans.
    + apply seval_plus_lhs_any. apply IHa1.
    + eapply smallstep_trans.
      - apply seval_plus_rhs_any. apply IHa2.
      - eapply seval_trans.
        ** apply seval_plus.
        ** apply seval_refl.
  * intro. eapply smallstep_trans.
    + apply seval_let_lhs_any. apply IHa1.
    + eapply smallstep_trans.
      - apply seval_let_rhs_any. apply IHa2.
      - eapply seval_trans.
        ** apply seval_let_finish.
        ** apply seval_refl.
Qed.

(* BEGIN FIX *)
End SmallStep.
