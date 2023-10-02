From WR Require Export syntax.
From Hammer Require Import Tactics.

Inductive Domain : Type :=
| D_Abs : tm -> (nat -> Domain) -> Domain
| D_Ne : DomainNe -> Domain
with DomainNe : Type :=
| N_Var : nat -> DomainNe
| D_App : DomainNe -> Domain -> DomainNe.

Definition Env := nat -> Domain.

Inductive DApp : Domain -> Domain -> Domain -> Prop :=
| DA_AppAbs t ρ e d :
  DEval (e .: ρ) t d ->
  (* ------------------ *)
  DApp (D_Abs t ρ) e d

| DA_App e d :
  (* ------------------------------ *)
  DApp (D_Ne e) d (D_Ne (D_App e d))

with DEval : Env -> tm -> Domain -> Prop :=
| DE_Var ρ i :
  (* ------------------------ *)
  DEval ρ (var_tm i) (ρ i)

| DE_Abs ρ a :
  (* --------------------------- *)
  DEval ρ (Lam a) (D_Abs a ρ)

| DE_App ρ a f b d d0 :
  DEval ρ a f ->
  DEval ρ b d ->
  DApp f d d0 ->
  (* -------------------- *)
  DEval ρ (App a b) d0.


Inductive RB n : Domain -> tm -> Prop :=
| B_AppAbs ρ b t t0  :
  DEval (D_Ne (N_Var n) .: ρ) t b ->
  RB (S n) b t0 ->
  RB n (D_Abs t ρ) (Lam t0)
| B_Ne e t :
  RBNe n e t ->
  RB n (D_Ne e) t
with RBNe n : DomainNe -> tm -> Prop :=
| B_Var i :
  RBNe n (N_Var i) (var_tm (n - (S i)))
| B_App e f t0 t1 :
  RBNe n e t0 ->
  RB n f t1 ->
  RBNe n (D_App e f) (App t0 t1).

Definition init_env n : Env := fun i => D_Ne (N_Var (n - (S i))).

Definition norm n a b := exists d, DEval (init_env n) a d /\ RB n d b.

Example test0 : norm 0 (App (Lam (var_tm 0)) (Lam (var_tm 0))) (Lam (var_tm 0)).
Proof. sauto lq:on rew:off. Qed.

Example test1 : norm 1 (App (Lam (var_tm 0)) (var_tm 0)) (var_tm 0).
Proof. sauto lq:on rew:off. Qed.

Example test2 : norm 1 (App (Lam (App (var_tm 0) (var_tm 1))) (var_tm 0)) (App (var_tm 0) (var_tm 0)).
Proof. sauto lq:on rew:off. Qed.
