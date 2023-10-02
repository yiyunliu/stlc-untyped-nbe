tm : Type
ty : Type

Lam : (tm -> tm) -> tm
App : tm -> tm -> tm

Fun : ty -> ty -> ty
I : ty