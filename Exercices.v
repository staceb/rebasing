(* Importation de module *)
Require Import Coq.Arith.Plus.
Require Import List.
(* Contexte de listes *)
Open Scope list_scope.
(* Important des notations [] et h::t *)
Import ListNotations.
Require Import Omega.

Definition admit {T: Type} : T.  Admitted.

(** PAIRS **)

Definition swap_pair {X Y:Type} (p : X * Y) : (Y * X) :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem swap_theorem : forall X Y (p : X * Y), (snd p, fst p) = swap_pair p.
Proof.
  destruct p.
  - simpl. reflexivity. (*Equivalent à "trivial."*)
Qed.

(** LISTES **)

Theorem nil_app : forall (X:Type) (l:list X), [] ++ l = l.
Proof.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Attention : parfois destruct suffit à la place de l'induction *)
Theorem tl_length_pred : forall (X:Type) (l:list X),
  pred (length l) = length (tl l).
Proof.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem app_assoc : forall (X:Type) (l1 l2 l3 : list X),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros X l1 l2 l3.
  generalize dependent l1. (*Rajoute un forall dans le goal sur l1 (forall l1, .... à la place de (l1 ++ l2) ...*)
  induction l1.
  - trivial.
  - simpl. rewrite <- IHl1. reflexivity.
Qed.

Theorem app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  induction l1.
  - simpl. reflexivity.
  - simpl. intro l2. rewrite IHl1. reflexivity.
Qed.


Theorem rev_length : forall (X:Type) (l:list X),
  length (rev l) = length l.
Proof.
  induction l.
  - simpl. reflexivity.
  (* Longueur de (rev l ++ [a]) = longueur de rev l + longueur de [a]
    On simplifie et on utilise la IH. 
    Commutativité de l'addition entre length l + 1 et S length l*)
  - simpl. rewrite app_length. simpl. rewrite IHl. rewrite plus_comm. trivial.
Qed.


Theorem rev_involutive : forall (X:Type) (l:list X),
  rev (rev l) = l.
Proof.
  induction l.
  - trivial.
  - simpl. rewrite -> rev_unit. rewrite -> IHl. reflexivity.
Qed.

Theorem app_nil_r : forall (X:Type) (l:list X),
  l ++ [] = l.
Proof.
  induction l.
  - trivial.
  - simpl. rewrite IHl. reflexivity.
Qed.

(* FORMULES  *)

Definition variable : Type := nat.

Inductive formula : Type :=
  | Var : variable -> formula
  | Neg : formula -> formula
  | Or : formula -> formula -> formula
  | And : formula -> formula -> formula.


(* Définir une fonction qui calcule le nombre de parenthèses d'une formule *)
Fixpoint nb_par (p:formula) : nat := match p with
  | Var v => 0
  | Neg n => nb_par n
  | Or o1 o2 => 2 + nb_par o1 + nb_par o2
  | And a1 a2 => 2 + nb_par a1 + nb_par a2
end.

(* Pareil pour le nombre de ET et de OU logiques *)
Fixpoint nb_and (p:formula) : nat := match p with
  | Var v => 0
  | Neg n => nb_and n
  | Or o1 o2 => nb_and o1 + nb_and o2
  | And a1 a2 => 1 + nb_and a1 + nb_and a2
end.

Fixpoint nb_or (p:formula) : nat := match p with
  | Var v => 0
  | Neg n => nb_or n
  | Or o1 o2 => 1 + nb_or o1 + nb_or o2
  | And a1 a2 => nb_or a1 + nb_or a2
end.

(* la tactique 'omega' de Coq qui peut
résoudre automatiquement certaines preuves purement arithmétiques *)
Theorem prop1_ol5 : forall p, nb_par p = 2 * (nb_and p + nb_or p).
Proof.
  induction p.
  - trivial.
  - simpl.
    assert (nb_and p + nb_or p + 0 = nb_and p + nb_or p) as Hzero.
    {
      Check plus_comm. (* Affiche type d'une preuve *)
      rewrite <- plus_comm. simpl. reflexivity.
    }
    rewrite -> Hzero.
    rewrite -> IHp. simpl. rewrite -> Hzero. reflexivity.
  (*Omega automatise certains calculs*)
  - simpl. omega.
  - simpl. omega.
Qed.

(*taille_formula = nombre de caractères*)
Fixpoint taille_formula (p:formula) : nat := match p with
  | Var v => 1
  | Neg n => 1 + taille_formula n
  | Or o1 o2 => 2 + taille_formula o1 + taille_formula o2 + 1
  | And a1 a2 => 2 + taille_formula a1 + taille_formula a2 + 1 
end.

Fixpoint nb_par_left (p:formula) : nat := match p with
  | Var v => 0
  | Neg n => nb_par_left n
  | Or o1 o2 => 1 + nb_par_left o1 + nb_par_left o2 
  | And a1 a2 => 1 + nb_par_left a1 + nb_par_left a2
end.

Definition nb_par_right (p:formula) : nat := nb_par_left p.

Fixpoint nb_neg (p:formula) : nat := match p with
  | Var v => 0
  | Neg n => 1 + nb_neg n
  | Or o1 o2 => nb_neg o1 + nb_neg o2
  | And a1 a2 => nb_neg a1 + nb_neg a2
end.

Theorem prop2_olg5 : forall p, 
  taille_formula p = (nb_neg p) + (2 * nb_par_left p) + (2 * nb_par_right p) + 1.
Proof.
  induction p.
  - trivial.
  - simpl. rewrite -> IHp. simpl. unfold nb_par_right. reflexivity.
  - simpl. rewrite -> IHp1. rewrite -> IHp2. simpl. unfold nb_par_right. omega.
  - simpl. rewrite -> IHp1. rewrite -> IHp2. simpl. unfold nb_par_right. omega.
Qed.

(* Définir l'évaluation où les valuations sont des fonctions Var -> {0, 1} *)
Fixpoint eval (v : variable -> bool) (p : formula) : bool := match p with
  | Var var => v var
  | Neg n => negb (eval v n)
  | Or o1 o2 => eval v o1 || eval v o2
  | And a1 a2 => eval v a1 && eval v a2
end.

Notation "[[ p ]] v" := (eval v p) (at level 15).

Theorem trivial_theorem : forall x v, [[Var x]]v = v(x).
Proof.
  trivial.
Qed.

(* Dans la correspondance de Curry-Howard, forall et l'implication sont vu
   comme des fonctions Preuve->Preuve.
   - S'ils sont dans le goal, on peut introduire les paramètres/hypothèses avec 'intros'
   - S'ils sont dans le contexte, on peut les appliquer comme des fonctions avec 'apply' *)
Theorem exo2_td2_ol5 : forall p v1 v2,
  (forall x, v1(x) = v2(x)) -> ([[p]]v1 = [[p]]v2).
Proof.
  intros p v1 v2.
  induction p.   (*! = applique le theorem autant de fois qu'il le peut*)
  - intro supp. rewrite !trivial_theorem. rewrite supp. reflexivity.
  - intro supp. simpl. apply IHp in supp. rewrite supp. reflexivity.
  - intro supp. 
    (*dédoubler la supposition pour pouvoir appliquer apply avec IHp1 et IHp2*)
    assert (forall x : variable, v1 x = v2 x) as supp'. apply supp.
    simpl. apply IHp1 in supp. apply IHp2 in supp'.
    rewrite supp. rewrite supp'. reflexivity.
  -  intro supp. 
    (*dédoubler la supposition pour pouvoir appliquer apply avec IHp1 et IHp2*)
    assert (forall x : variable, v1 x = v2 x) as supp'. apply supp.
    simpl. apply IHp1 in supp. apply IHp2 in supp'.
    rewrite supp. rewrite supp'. reflexivity.
Qed.

Fixpoint my_map (X Y:Type) (l:list X) (f: X->Y) : list Y :=
match l with
| [] => []
| h::t => (f h)::(my_map X Y t f)
end.

Fixpoint my_filter (X:Type) (l:list X) (f:X->bool) : list X :=
match l with
| [] => []
| h::t => if (f h) then (h::(my_filter X t f)) else (my_filter X t f)
end.

Definition my_foldmap {X Y:Type} (l:list X) (f:X->Y) : list Y :=
  let fix aux acc l :=
    match l with 
    | [] => acc
    | h::t => (f h)::(aux acc t)
    end
  in
aux [] l.

Fixpoint map_opt {X Y:Type} (l:list (option X)) (f:X->Y) : list (option Y) :=
match l with
| [] => []
| (None)::t => (map_opt t f)
| (Some h)::t => (Some (f h))::(map_opt t f)
end.

(* Comprendre l'énoncé et prouver *)
Theorem opt1 : forall (X:Type) (l:list (option X)),
  map_opt (fun x => x) l =
  filter (fun x =>
    match x with
    | None => false
    | _ => true
    end) l.
Proof.
Admitted.
 







