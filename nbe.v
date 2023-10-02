From WR Require Export syntax.

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

| DE_Abs ρ A a :
  (* --------------------------- *)
  DEval ρ (Lam A a) (D_Abs a ρ)

| DE_App ρ a f b d d0 :
  DEval ρ a f ->
  DEval ρ b d ->
  DApp f d d0 ->
  (* -------------------- *)
  DEval ρ (App a b) d0.
