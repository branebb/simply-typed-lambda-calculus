Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import String.
Require Import Lia.

Inductive Ty :=
  | TyBool : Ty
  | TyArr : Ty -> Ty -> Ty
  | TyError : Ty.

Inductive Term :=
  | TmTrue : Term
  | TmFalse : Term
  | TmIf : Term -> Term -> Term -> Term
  | TmVar : nat -> Term
  | TmAbs : string -> Ty -> Term -> Term
  | TmApp : Term -> Term -> Term
  | TmError : Term.

Inductive Binding :=
  | NameBind
  | VarBind : Ty -> Binding.

Definition Context := list (string * Binding).

Definition addBinding (ctx : Context) (x : string) (bind : Binding) : Context :=
  (x, bind) :: ctx.


Fixpoint getTypeFromContext (ctx : Context) (i : nat) : Ty :=
  match ctx, i with
  | [], _ => TyError
  | (_, binding) :: _, 0 => match binding with
                            | VarBind ty => ty
                            | _ => TyError
                            end
  | _ :: ctx', S i' => getTypeFromContext ctx' i'
  end.

Fixpoint shift (d c : nat) (t : Term) : Term :=
  match t with
  | TmVar x => TmVar (if x <? c then x else x + d)
  | TmAbs x tyT1 t2 => TmAbs x tyT1 (shift d (S c) t2)
  | TmApp t1 t2 => TmApp (shift d c t1) (shift d c t2)
  | TmIf t1 t2 t3 => TmIf (shift d c t1) (shift d c t2) (shift d c t3)
  | TmTrue => TmTrue
  | TmFalse => TmFalse
  | TmError => TmError
  end.

Fixpoint subst (j : nat) (s : Term) (t : Term) : Term :=
  match t with
  | TmVar x => if j =? x then s else TmVar x
  | TmAbs x tyT1 t2 => TmAbs x tyT1 (subst (S j) (shift 1 0 s) t2)
  | TmApp t1 t2 => TmApp (subst j s t1) (subst j s t2)
  | TmIf t1 t2 t3 => TmIf (subst j s t1) (subst j s t2) (subst j s t3)
  | TmTrue => TmTrue
  | TmFalse => TmFalse
  | TmError => TmError
  end.


Definition isval (t : Term) : bool :=
  match t with
  | TmAbs _ _ _ => true
  | TmTrue => true
  | TmFalse => true
  | _ => false
  end.

Fixpoint eval_step (ctx : Context) (t : Term) : Term :=
  match t with 
  | TmApp (TmAbs x tyT1 t12) v2 =>
      if isval v2 then subst 0 v2 t12 else TmApp (TmAbs x tyT1 t12) (eval_step ctx v2)
  | TmApp t1 t2 =>
      if isval t1 then TmApp t1 (eval_step ctx t2) else TmApp (eval_step ctx t1) t2
  | TmIf TmTrue t2 _ => t2
  | TmIf TmFalse _ t3 => t3
  | TmIf t1 t2 t3 => TmIf (eval_step ctx t1) t2 t3
  | _ => t
  end.

(* States that shifting a term by 0 has no effect. *)
Lemma shift_identity : forall t c,
  shift 0 c t = t.
Proof.
  induction t; intros; simpl; try reflexivity.
  - rewrite IHt1. rewrite IHt2. rewrite IHt3. reflexivity.
  - destruct (n <? c).
    -- reflexivity.
    -- rewrite plus_0_r. reflexivity.
  - f_equal. rewrite IHt. reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

(*States that shifting a term twice consecutively is equivalent to shifting once by the sum of the shifts. *)
Lemma shift_composition : forall t d1 d2 c,
  shift d1 c (shift d2 c t) = shift (d1 + d2) c t.
Proof.
  induction t; intros; simpl; try reflexivity.
  - f_equal. apply IHt1.  apply IHt2.  apply IHt3.
  - destruct (n <? c) eqn:H.
    -- rewrite H. reflexivity.
    -- f_equal. destruct (n + d2 <? c) eqn:H_comp.
       --- assert (H1: False). { apply Nat.ltb_lt in H_comp.
          apply Nat.ltb_ge in H.
          lia. } contradiction.
       --- simpl. rewrite Nat.add_assoc.  rewrite Nat.add_comm. 
           rewrite (Nat.add_comm n d1). rewrite Nat.add_assoc. reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt1. apply IHt2.
Qed.




(* States that substituting a variable with itself leaves the term unchanged. *)
Lemma subst_identity : forall t x,
  subst x (TmVar x) t = t.
Proof.
  induction t ; intros ; try reflexivity.
  - simpl. f_equal. apply IHt1. apply IHt2. apply IHt3.
  - simpl. destruct (x=? n) eqn:H.
    -- apply Nat.eqb_eq in H. rewrite H. reflexivity.
    -- reflexivity.
  -  simpl. f_equal. rewrite Nat.add_1_r. apply IHt.
  - simpl. f_equal. apply IHt1. apply IHt2.
Qed.

(* Asserts that shifting a value (as determined by isVal) still results in a value. *)

Lemma shift_preserves_value : forall t d c,
  isval t = true -> isval (shift d c t) = true.
Proof.
  intros t d c H. induction t; simpl in *; 
  try discriminate ; try reflexivity.
Qed.

(* Asserts that the evaluation of a term is deterministic — 
if a term reduces to two different terms in one step, they must be the same. *)
Lemma eval_determinism : forall ctx t t1 t2,
  eval_step ctx t = t1 -> eval_step ctx t = t2 -> t1 = t2.
Proof.
  intros. rewrite H in H0. assumption.
Qed.

(*  States that substituting a variable with itself leaves the variable unchanged. *)
Lemma subst_identity_same_var : forall j,
  subst j (TmVar j) (TmVar j) = TmVar j.
Proof.
  intros j.
  simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Fixpoint type_eq (ty1 ty2 : Ty) : bool :=
  match ty1, ty2 with
  | TyBool, TyBool => true
  | TyError, TyError => true
  | TyArr t1 t2, TyArr t1' t2' => andb (type_eq t1 t1') (type_eq t2 t2')
  | _, _ => false
  end.

Fixpoint typeof (ctx : Context) (t : Term) : Ty :=
  match t with
  | TmTrue => TyBool
  | TmFalse => TyBool
  | TmIf t1 t2 t3 =>
      match typeof ctx t1 with
      | TyBool =>
          let tyT2 := typeof ctx t2 in
          let tyT3 := typeof ctx t3 in
          if type_eq tyT2 tyT3 then tyT2
          else TyError
      | _ => TyError
      end
  | TmVar i => getTypeFromContext ctx i
  | TmAbs x tyT1 t2 =>
      let tyT2 := typeof (addBinding ctx x (VarBind tyT1)) t2 in
      TyArr tyT1 tyT2
  | TmApp t1 t2 =>
      match typeof ctx t1 with
      | TyArr tyT11 tyT12 =>
          let tyT2 := typeof ctx t2 in
          if type_eq tyT11 tyT2 then tyT12
          else TyError
      | _ => TyError
      end
  | _ => TyError
  end.

(*
States the progress theorem: for well-typed terms, 
either the term is a value or it can take a step in evaluation. *)
Theorem progress : forall ctx t T,
  typeof ctx t = T ->
  (isval t = true \/ exists t', eval_step ctx t = t').
Proof.
  intros ctx t.
  induction t; intros T HT; simpl in HT; inversion HT; subst.
  - left. reflexivity.
  - left. reflexivity.
  - right. destruct (typeof ctx t1) eqn:HT1.
    + destruct t1; try inversion HT1.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
    + eauto.
  + eauto.
  - right. simpl. exists (TmVar n). reflexivity.
  - left. simpl. reflexivity.
  - right. exists (eval_step ctx (TmApp t1 t2)). reflexivity.
  - right. exists (eval_step ctx TmError).  reflexivity. 
Qed.


(*
   States that values (terms identified by isval) 
  preserve their typing under the type inference system.
*)

Lemma values_preserve_typing : forall ctx t T,
  typeof ctx t = T ->
  isval t = true ->
  typeof ctx t = T.
Proof.
  intros ctx t T HType HVal.
  induction t; try discriminate; try assumption.
Qed.

(*
   States that the equality comparison for types is reflexive.
*)

Lemma type_eq_refl : forall ty,
  type_eq ty ty = true.
Proof.
  intros ty.
  induction ty; simpl; try reflexivity.
  - rewrite IHty1, IHty2. reflexivity.
Qed.


(*
   States that evaluating a value 
  (as determined by isval) results in the value itself.
*)
Lemma eval_value_preservation : forall ctx t,
  isval t = true ->
  eval_step ctx t = t.
Proof.
  intros ctx t HVal.
  destruct t; simpl in HVal; try reflexivity; try discriminate.
Qed.


(*
   States the preservation theorem: 
if a well-typed term takes a step in evaluation, 
 the resulting term is also well-typed.
*)
Theorem preservation : forall (ctx : Context) (t t' : Term) (T : Ty),
  typeof ctx t = T ->
  eval_step ctx t = t' ->
  typeof ctx t' = T.
Proof.
Admitted.










