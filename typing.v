From WR Require Export syntax.

Definition context := nat -> ty.

(* Statics *)
Inductive Wt (n : nat) (Γ : context) : tm -> ty -> Prop :=
| T_Var i :
    i < n ->
    (* ------------------------------- *)
    Wt n Γ (var_tm i) (Γ i)

| T_Lam : forall A a B,
    Wt (S n) (A .: Γ) a B ->
    (* -------------------------- *)
    Wt n Γ (Lam a) (Fun A B)

| T_App : forall a A B b,
    Wt n Γ a (Fun A B) ->
    Wt n Γ b A ->
    (* ----------------------------- *)
    Wt n Γ (App a b) B.

#[export]Hint Constructors Wt : core.
