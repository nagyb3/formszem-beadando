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

Admitted.

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

Admitted.

(* BEGIN FIX *)
Goal | (APlus (ALet X (ALit 1) (AVar X)) (AVar X)), empty | =>* ALit 1.
(* END FIX *)
Proof.

Admitted.

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

Admitted.


(* BEGIN FIX *)
Require Import Coq.Program.Equality.
Lemma seval_let_rhs_any n a2 a2' x s:
  | a2, update x n s | =>* a2' ->
  | ALet x (ALit n) a2, s | =>* ALet x (ALit n) a2'.
(* END FIX *)
Proof.

Admitted.

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

Admitted.

(* BEGIN FIX *)
End SmallStep.

Module CalculusOfClosures.

(** Calculus of Closures - extra feladat javitashoz *)
(**
  PROBLEMAFELVETES:
  Sajnos a `let` kifejezesek small-step szemantikajat nem
  lehetseges ugy megadni, hogy az `a2` kiertekelese ne az egesz
  `let` kifejezes szintaktikus kontextusaban tortenjen a jelenlegi
  megkozelites mellett.

  Gondolj bele, az eloadason es gyakorlatokon tanultak szerint
  szemantikaba kell egy (vagy tobb) szabaly, amelyik a resz-
  kifejezeseket egyszerusiti, amig egy literalt el nem erunk.
  Ez a `let` kifejezes eseten a kovetkezokeppen nezne ki
  (call-by-value/moho kiertekelest feltetelezve):

   | a1, s | => a1'
  ________________________________________________ seval_let_lhs
   | let x := a1 in a2, s | => let x := a1' in a2

  Az `a2` kifejezest nem kell kiertekelni, csak miutan az
  `a1`-gyel elertunk egy literalt. Miutan ez megtortent,
  az `a2` kifejezest az `x`-szel kiegeszitett allapotban
  kellene kiertekelni, pl. igy:

  _______________________________________________ seval_let
   | let x := n in a2, s | => | a2, s[x |-> n] |

  Ez viszont azt jelenti, hogy az `a2` kiertekelesehez
  szukseges a modositott allapot, tehat az allapotnak 
  meg kell jelennie a => mindket oldalan (minden szabalyban).
  Tovabba ez a szabaly elfelejti a `let` scope-jat, es igy rossz
  allapotban folytatodna a kiertekeles egyeb reszkifejezesek eseten
  (amelyek a `let` kifejezes oseinek a `let`-tol kulonbozo
  reszkifejezesei).

  Ez a kovetkezot jelentene az pl. osszeadasra nezve:

   | a1, s | => | a1', s' |
  __________________________________ seval_plus_lhs
   | a1 + a2, s | => | a1' + a2, s' |

  A => jobb oldalan muszaj egy potencialisan modositott
  allapotot hasznalnunk (s'), ugyanis ha az `a1` egy `let`
  kifejezes volt, akkor a kiertekelese modositja az allapotot,
  amit pedig az `a1'` tovabbi kiertekelesi lepeseiben kell
  hasznalnunk.
  PROBLEMA: Viszont az `a2` kiertekelesebe nem szolhat bele egy
  `a1`-beli `let` kifejezes, mert mas a scope-juk! A problema
  illusztralva:

  ____________________________________________________ seval_let
  | let x := 1 in x, empty | => | x, empty[x |-> 1] |
  _____________________________________________________________ seval_plus_lhs
  | (let x := 1 in x) + x, empty | => | x + x, empty[x |-> 1] |

  Viszont ezutan a lepes utan `x + x` a frissitett allapotban
  a kovetkezokeppen ertekelodik ki:

  | x + x, empty[x |-> 1] | => (seval_plus_lhs + seval_var miatt)
  | 1 + x, empty[x |-> 1] | => (seval_plus_rhs + seval_var miatt)
  | 1 + 1, empty[x |-> 1] | => (seval_plus miatt)
  | 2, empty[x |-> 1] |

  Viszont a 2 itt nyilvanvaloan rossz eredmeny!!!


  (STANDARD MEGOLDAS 1: allapotok helyett hasznaljunk behelyettesitest!
   Ezt majd fogjatok tanulni Nyelvek Tipusrendszeren.)

  STANDARD MEGOLDAS 2: Calculus of Closures
  Ne hasznaljunk egy globalis allapotot kiertekeleshez! Helyette, minden
  reszkifejezes kiertekelesehez "propagaljuk be" az allapotot! Ehhez
  minden kifejezest felannotalunk egy allapottal (ezt hivjuk closure-nek),
  tovabba minden reszkifejezessel rendelkezo kifejezeshez keszitsunk egy
  closure-t (ami nekunk most az osszeadas es a `let`):
*)
Inductive closure :=
| c_aexp (a : AExp) (s : state)
| c_plus (c1 c2 : closure)
| c_let (x : string) (c1 : closure) (a2 : AExp) (s : state).

(** A `c_let` eseten alkalmazunk egy apro trukkot: `a2` nem igazi closure.
   Viszont a `s : state` parameter az `a2`-hoz hasznalt allapotot fogja 
   tartalmazni, amelyet az `x` kotesevel kell majd kiegesziteni. *)

(**
  A szemantikat ki kell terjesztenunk, mostantol closure-ok kozotti
  relaciokent adjuk meg a kovetkezo szabalyokkal. Harom kulonbseg van az
  orakon vett szabalyokhoz kepest:
  - A kiertekelest reszfakba vivo szabalyokban (`seval_plus_lhs`,
    `seval_plus_rhs`) nincs szukseg a state-re, ugyanis az allapot a
    closure-ok reszet kepezi.
  - Ahhoz, hogy `AExp`-ekbol closure-t kepezzunk, a globalis allapotot
    propagalni kell a reszkifejezesekbe (lasd `seval_plus_propagate`).
  - Az axiomak (`seval_var`, `seval_plus`) egy closure-ben levo `AExp`-el
    operalnak az orakon megszokott modon. `seval_var` a closure-ben levo
    allapotot hasznalja a valtozo jelentesenek megadasahoz.

  A szabalyok "papiros" leirasahoz a kovetkezo szintaxist hasznaljuk:

   a ::= n | x | a1 + a2 | let x := a1 in a2
   c ::=  a{s} | c1 + c2 | let x := c1 in a2
           ^        ^             ^
           |        |             |
Kodban: c_aexp    c_plus        c_let
 *)
Reserved Notation "c1 => c2" (at level 60).
Inductive eval_smallstep : closure -> closure -> Prop :=

(**
  __________________________ seval_var
        x{s} => s[x]{s}
*)
| seval_var x s :
    c_aexp (AVar x) s => c_aexp (ALit (s x)) s 

(**
  UJ SZABALY:
 __________________________________ seval_plus_propagate
    (a1 + a2){s} => a1{s} + a2{s}
*)
| seval_plus_propagate a1 a2 s :
    c_aexp (APlus a1 a2) s => c_plus (c_aexp a1 s) (c_aexp a2 s)

(**
        c1 => c1'
  ______________________ seval_plus_lhs
    c1 + c2 => c1' + c2
*)
| seval_plus_lhs c1 c1' c2 :
  c1 => c1'
->
  c_plus c1 c2 => c_plus c1' c2

(**
         c2 => c2'
  __________________________ seval_plus_rhs
    n{s} + c2 => n{s} + c2'
*)
| seval_plus_rhs n c2 c2' s :
  c2 => c2'
->
  c_plus (c_aexp (ALit n) s) c2 => c_plus (c_aexp (ALit n) s) c2'

(**
  ________________________________ seval_plus
   n{s1} + m{s2} => (n + m){s1}
                            ^
                            |
  MEGJEGYZES: literalok eseten nem szamit, hogy mi a closure-ben tarolt
  allapot, ezert itt `s1`-et valasztottunk (lehetne `s2` is).
*)
| seval_plus n m s1 s2 :
  c_plus (c_aexp (ALit n) s1) (c_aexp (ALit m) s2) => c_aexp (ALit (n + m)) s1

(**
  8. feladat (0.5 bonusz pont): Add meg a `let` kifejezes small-step szemantikajat
  Calculus of Closures-ben!
  Tipp: Less az osszeadas szemantikajabol, es a `c_let` szintaxisabol!
  Tipp: 2 szabalyt mar korabban nagyjabol leirtunk (nem closure szintaxissal)
  fentebb, a problemafelvetes reszben!
  Tipp: 3 szabalyra lesz szukseged
    - Egy closure-be propagalo szabalyra (lasd `seval_plus_propagage`).
    - Egy reszkifejezest kiertekelo szabalyra (lasd `seval_let_lhs` fentebb,
      illetve `seval_plus_lhs`, `seval_plus_rhs`). Nincs szukseg a `let`
      kifejezes eseten "rhs" szabalyra.
    - Egy szamitasi szabaly, ami elvegzi az allapot frissitest az `a2`
      kiertekelesehez (lasd `seval_let`). Az `a2` kiertekelesehez
      mindenkeppen a `c_let` 4. parameterekent nyilvantartott allapotot
      frissitsd!
*)
(* END FIX *)

(* BEGIN FIX *)
where "c1 => c2" := (eval_smallstep c1 c2).

(**
  A reflexiv tranzitiv lezartat a szokasos modon adjuk meg:
*)
Reserved Notation "c =>* c'" (at level 60).
Inductive eval_smallstep_rtc : closure -> closure -> Prop := 

| seval_refl c :
  c =>* c
| seval_trans c c' c'':
  c => c' -> c' =>* c'' ->
(* ------------------------------------*)
     c =>* c''

where "c =>* c'" := (eval_smallstep_rtc c c').

(** 9. feladat: (0.5 bonusz pont)
    Bizonyitsd a kovetkezo teszteseteket!
    Tipp: A bizonyitas soran szukseged lesz a propagacios (_propagate)
    szabalyok hasznalatara tobbszor!
*)
Goal c_aexp ex1 aState =>* c_aexp (ALit 1) (update Y 0 aState).
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
(**
   A kovetkezo teszt kifejezetten a fent emlitett problemas esetet teszteli.
*)
Goal c_aexp (APlus (ALet X (ALit 1) (AVar X)) (AVar X)) empty =>*
     c_aexp (ALit 1) (update X 1 empty).
(* END FIX *)
Proof.

Admitted.

(** Megadunk par segedtetelt a lenti bonyolultabb bizonyitashoz: *)
(* BEGIN FIX *)
Theorem smallstep_trans :
  forall c c' c'',
    c =>*  c' ->
    c' =>* c'' ->
    c =>*  c''.
Proof.
  intros. revert c'' H0. induction H; intros.
  * assumption.
  * apply IHeval_smallstep_rtc in H1.
    eapply seval_trans. exact H. exact H1.
Qed.

Lemma seval_plus_lhs_any c1 c1' c2 :
  c1 =>* c1' ->
  c_plus c1 c2 =>* c_plus c1' c2.
Proof.
  intro. induction H.
  * apply seval_refl.
  * eapply seval_trans. apply seval_plus_lhs.
    - exact H.
    - exact IHeval_smallstep_rtc.
Qed.

Lemma seval_plus_rhs_any n s c2 c2' :
  c2 =>* c2' ->
  c_plus (c_aexp (ALit n) s) c2 =>* c_plus (c_aexp (ALit n) s) c2'.
Proof.
  intro. induction H.
  * apply seval_refl.
  * eapply seval_trans. apply seval_plus_rhs.
    - exact H.
    - exact IHeval_smallstep_rtc.
Qed.

(**
  10. feladat (0.25 bonusz pont): Bizonyitsd a kovetkezo allitast!
  Tipp: Az elsonel meritsd otletet a fenti lemmak bizonyitasabol.
*)
Lemma seval_let_lhs_any x c c' a s :
  c =>* c' ->
  c_let x c a s =>* c_let x c' a s.
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
(**
  11. feladat (0.75 bonusz pont):
  Bizonyitsd be, hogy a small-step szemantika
  kifejezi a denotacios szemantikat! Azaz a Calculus of Closures eredmenye
  a denotacios szemantika altal meghatarozott ertek!

  Tipp: A tetel bizonyitasahoz szukseged lesz az elozo 4 tetel
  kombinaciojara! Gondold vegig eloszor "papiron" a bizonyitast!
*)
Theorem denot_to_smallstep :
  forall a s, exists s', c_aexp a s =>* c_aexp (ALit (aeval a s)) s'.
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
End CalculusOfClosures.