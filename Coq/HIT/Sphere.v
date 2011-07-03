Add LoadPath "..".
Require Import Homotopy.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** The 2-Sphere, S^2 **)

Axiom sphere : Type.

Axiom bp : sphere.
Axiom tc : idpath bp ~~> idpath bp.

Axiom sphere_rect :
  forall (P : sphere -> Type) (d_bp : P bp)
    (d_tc : (transport 
      (P := fun p : bp ~~> bp => (transport p d_bp ~~> d_bp)) 
      tc (idpath d_bp)) ~~> (idpath d_bp)),
    forall (x : sphere), P x.

Axiom compute_bp :
  forall (P : sphere -> Type) (d_bp : P bp)
    (d_tc : (transport 
      (P := fun p : bp ~~> bp => (transport p d_bp ~~> d_bp)) 
      tc (idpath d_bp)) ~~> (idpath d_bp)),
    sphere_rect P d_bp d_tc bp ~~> d_bp.

Axiom compute_tc :
  forall (P : sphere -> Type) (d_bp : P bp)
    (d_tc : (transport 
      (P := fun p : bp ~~> bp => (transport p d_bp ~~> d_bp)) 
      tc (idpath d_bp)) ~~> (idpath d_bp)),
    
    (* Lots more to go here *)
    

    map_dep (sphere_rect P d_bp d_tc) 

(* There should be a "derived section" on the space of paths
   bp ~~> bp, and we need to apply map_dep to this guy and
   tc.  Some combination of the resulting lift has to agree
   with the one provided by sphere_rect *)

Definition sphere_rect' : 
  forall (B : Type) (bp' : B) (tc' : idpath bp' ~~> idpath bp'),
    sphere -> B.

