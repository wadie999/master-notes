(**************************************)
(* TP noté 2022-2023 (French version) *)
(**************************************)

(* Ce TP contient 20 TODOs.
   Certains sont juste des tests unitaires, via "reflexivity."
   Les derniers TODOs, un peu plus difficiles, serviront de points bonus. *)

Require Import String.
Require Import Nat.
Require Import ZArith. (* pour les entiers signés *)
Require Import Lia. (* pour les buts arithmétiques *)
Require Import List. Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Module EXP.

(* On définit le type inductif "exp", décrivant un langage d'expressions.
   Une expression est une variable, une constante, un opposé ou une somme. *)
Inductive exp : Type :=
  | Var (n : string)
  | Const (c : Z)
  | Opp (e : exp)
  | Add (e1 e2 : exp).

(* Representation des variables a et b par des "exp"s. *)
Definition A := Var "a".
Definition B := Var "b".

(* representation de l'expression (1 + 2 + 3 + a) *)
Definition example1 := Add (Add (Add (Const 1) (Const 2)) (Const 3)) A.

(* représentation de l'expression (b - (1 + a - 2)) *)
Definition example2 := Add B (Opp (Add (Add (Const 1) A) (Opp (Const 2)))).

(* Donner la sémantique dénotationnelle des expressions. Elle est
   définie par une fonction "eval" prenant en argument un
   environnement (c.-à-d., une fonction associant un entier à un nom
   de variable), une expression et renvoyant la valeur de l'expression
   (de type "Z"). *)
Fixpoint eval (env : string -> Z) (e : exp) : Z :=
  match e with 
  | Const c   => c
  | Var v     => env v
  | Opp e     => 0 - eval env e
  | Add e1 e2 => eval env e1 + eval env e2
  end.

(* Un environnement, donnant aux variables a et b, la valeur 1 et 2. *)
Definition env_example v :=
  match v with
  | "a" => 1
  | "b" => 2
  | _ => 0
  end.

(* Exemple (test unitaire!) de l'évaluation de l'expression. *)
Lemma eval_example1 : eval env_example example1 = 7.
Proof.
  simpl.
  reflexivity.
Qed.

(* Exemple (test unitaire!) de l'évaluation de l'expression, à nouveau. *)
Lemma eval_example2 : eval env_example example2 = 2.
Proof.
  simpl.
  reflexivity.
Qed.

(* On veut implémenter une optimisation typique des compilateurs
   appelée constant-foldLemma eval_example2 : eval env_example example2 = 2
   Proof.
   simpl.
   ing. Cette optimisation consiste à calculer à
   la compilation les constantes, ce qui permet de gagner du temps à
   l'exécution. Autrement dit, les expressions sont transformées pour
   en simplifier les constantes.
   Pour intuiter le fonctionnement de cette fonction récursive, regardez
   les 2 exemples ci-dessous (constant_fold_example1, constant_fold_example2)
*)

(* Écrire une fonction réalisant au moins les 2 transformations prouvées ci-dessous *)
Fixpoint constant_fold (e : exp) : exp :=
  match e with 
  | Const c => Const c
  | Var n => Var n 
  | Opp e => match constant_fold e with 
            | Const c => Const (-c)
            | e1 => Opp e1
             end
  | Add e1 e2 => match ((constant_fold e1), (constant_fold e2)) with
                 | (Const c1, Const c2) => Const (c1 + c2)
                 | ( e3 , e4 )=> Add e3 e4
                 end
  end.

(* Rappel :
   Definition example1 := Add (Add (Add (Const 1) (Const 2)) (Const 3)) A. *)
Lemma constant_fold_example1 : constant_fold example1 = Add (Const 6) A.
Proof.
simpl.
reflexivity.
Qed.

(* Rappel :
   Definition example2 := Add B (Opp (Add (Add (Const 1) A) (Opp (Const 2)))). *)
Lemma constant_fold_example2 :
  constant_fold example2
  = Add B (Opp (Add (Add (Const 1) A) (Const (-2)))).
Proof.
  simpl.
  reflexivity.
Qed.

(* Prouver que la fonction "constant_fold" est correcte.
   En cas de but du style "... match qqch e with ...",
   vous pourrez utiliser "destruct (qqch e)",
   après avoir généralisé les hypothèses d'induction avec "revert IHe"…

   Autre rappel :
   les réécritures peuvent se faire de gauche à droite, "rewrite H."
   ou de droite à gauche, "rewrite <- H." *)
Lemma constant_fold_correct env e : eval env (constant_fold e) = eval env e.
Proof.
  induction e.
  simpl.
  reflexivity.
  
  simpl.
  reflexivity.

  simpl.
  revert IHe.
  destruct (constant_fold e).
  simpl.
  lia.

  simpl.
  lia.

  simpl.
  lia.
  
  simpl.
  lia.  

  simpl.

  revert IHe1.
  destruct (constant_fold e1).
  simpl.
  lia.
  simpl.
  revert IHe2.
  destruct (constant_fold e2).
  simpl.
  simpl.
  lia.
  simpl.
  lia.
 simpl.
  lia.
  simpl.
  lia.
 simpl.
  lia.
  simpl.
  lia.
Qed.

(* Écrire une fonction "push_opp" qui pousse l'opp vers les feuilles de l'arbre.
   Dans le résultat, Opp ne doit donc apparaître qu'avant Var ou Const.
   Les doubles négations seront simplifiées.

   Dans ce but, on écrit une fonction auxiliaire "push_opp'",
   avec un argument booléen supplémentaire :
   - quand cet argument est vrai, nous ajoutons un Opp aux feuilles de l'expression,
   - sinon on ne le fait pas.

On rappelle que la négation booléenne s'appelle "negb" en Coq.


Une fois de plus, cette question vient avec 2 tests unitaires (ci-dessous) *)


Fixpoint push_opp' (opp : bool) (e : exp) : exp :=
  match e with 
    | Const c => if opp then Opp (Const c) else Const c
    | Var v => if opp then Opp (Var v) else Var v
    | Opp o => push_opp' (negb opp) o
    | Add e1 e2 => Add (push_opp' opp e1) (push_opp' opp e2) 
  end.

Definition push_opp := push_opp' false.

Lemma push_opp_example1 : push_opp example1 = example1.
Proof.
  simpl.
  reflexivity.
Qed.

(* Rappel :
   Definition example2 := Add B (Opp (Add (Add (Const 1) A) (Opp (Const 2)))). *)

Lemma push_opp_example2 :
  push_opp example2
  = Add B (Add (Add (Opp (Const 1)) (Opp A)) (Const 2)).
Proof.
  simpl.
  reflexivity.
Qed.

(* Montrer que "push_opp" est correct. On commencera par prouver un
   lemme intermédiaire sur "push_opp'".
   Vous pourrez avoir besoin de "revert" avant l'"induction",
   et vous pourrez utiliser "lia" pour les buts arithmétiques. *)
Lemma push_opp'_correct env opp e :
  eval env (push_opp' opp e) = eval env (if opp then Opp e else e).
Proof.
  induction e.
  
  - (* Cas Const *)
    simpl. destruct opp; simpl; reflexivity.

  - (* Cas Var *)
    simpl. destruct opp; simpl; reflexivity.
Admitted.






(* Montrer maintenant que "push_opp" est correct.
   Pour faire apparaître "push_opp'", la tactique "unfold" sera utile. *)
Lemma push_opp_correct env e : eval env (push_opp e) = eval env e.
Proof.
  (* TODO *)
Admitted.

(* Idéalement, l'expression (b - (1 + a - 2)) de l'example2 devrait être
   simplifiée en (b - a + 1). *)

(* Pour cela, on change de représentation pour utiliser des arbres n-aires. *)
Inductive expn : Type :=
  | NVar (n : string)
  | NConst (c : Z)
  | NOpp (e : expn)
  | NAdd (el : list expn).

(* Donner la sémantique dénotationnelle des nouvelles expressions.

   Vous pouvez utiliser la fonction "fold_right" qui a pour type
   "forall res elt, (elt -> res -> res) -> res -> list elt -> res"
   et qui est définie par
   "fold_right f r0 [e1; e2] = f e1 (f e2 r0)" *)

Check fold_right :
  forall res elt, (elt -> res -> res) -> res -> list elt -> res.
Eval compute in fun res elt (f : elt -> res -> res) r0 e1 e2 =>
  fold_right f r0 [e1; e2].

Fixpoint evaln (env : string -> Z) (e : expn) : Z :=
  match e with
  | NConst c => c
  | NVar v => env v
  | NOpp e' => 0 - evaln env e'
  | NAdd el => fold_right (fun e' acc => evaln env e' + acc) 0 el
  end.

(* Representation de l'expression (1 + 2 + 3 + a) *)
Definition example3 := NAdd [NConst 1; NConst 2; NConst 3; NVar "a"].

Lemma evaln_example3 : evaln env_example example3 = 7.
Proof.
  simpl.
  lia.
Qed.

(* Écrire la fonction de conversion d'un "exp" en un "expn".
   Vous pourrez utiliser la fonction "app" (aussi écrite "++"). *)
Check app.
Eval compute in [1; 2] ++ [3; 4].
Fixpoint exp_to_expn (e : exp) : expn :=
  match e with
  | Var n     => NVar n
  | Const c   => NConst c
  | Opp e     => NOpp (exp_to_expn e)
  | Add e1 e2 => NAdd [exp_to_expn e1; exp_to_expn e2]
  end.


Lemma exp_to_expn_example1 : exp_to_expn example1 = example3.
Proof.
  simpl.

Admitted.

(* Prouver la correction de "exp_to_expn". Vous pouvez utiliser "; try lia"
   pour résoudre tous les sous-objectifs qui sont résolus par lia
   (et garder les autres). Ne pas hésiter à prouver un lemme intermédiaire. *)
Lemma exp_to_expn_correct env e : evaln env (exp_to_expn e) = eval env e.
Proof.
  (* TODO *)
Admitted.

(* Écrivons maintenant le constant-folding sur les "expn".
   Vous pouvez utiliser des couples (x, y)
   et les fonctions "fst" et "snd" si besoin. *)
Fixpoint constant_foldn (e : expn) : expn :=
  e.  (* TODO *)

Lemma constant_foldn_example2 :
  constant_foldn (exp_to_expn (push_opp example2))
  = NAdd [NVar "b"; NOpp (NVar "a"); NConst 1].
Proof.
  (* TODO *)
Admitted.

(* Nous aurons besoin d'un principe d'induction spécial pour la suite. *)
Fixpoint expn_ind' (P : expn -> Prop)
    (fn : forall n, P (NVar n))
    (fc : forall c, P (NConst c))
    (fo : forall e, P e -> P (NOpp e))
    (fan : P (NAdd []))
    (fac : forall a el, P a -> P (NAdd el) -> P (NAdd (a :: el)))
    (e : expn) :
    P e :=
  let Fe := expn_ind' _ fn fc fo fan fac in
  let Fl :=
    fix Fl (el : list expn) : P (NAdd el) :=
      match el with
      | [] => fan
      | a :: el => fac _ _ (Fe a) (Fl el)
      end in
  match e with
    | NVar n => fn n
    | NConst c => fc c
    | NOpp e => fo _ (Fe e)
    | NAdd el => Fl el
    end.

(* Prouvons enfin que "constant_foldn" est correct.

   Vous pourrez commencer par "induction e using expn_ind'; auto."
   et utiliser "revert IHe…" si besoin. *)
Lemma constant_foldn_correct env e : evaln env (constant_foldn e) = evaln env e.
Proof.
  (* TODO *)
Admitted.

End EXP.