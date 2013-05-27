Module InconsistentExtraction.

(* "Squash" type *)

Inductive squashType (A : Type) : Prop :=
  | squash : A -> squashType A.

Check (squash Type Type).

(* Singleton elimination test *)

Inductive singletonThing : Prop :=
  | SingleCons : singletonThing.

Check singletonThing_rect.

(* Assuming univalence and an extra axiom relating "transport" to
univalence, we can write a term "x : bool" that is propositionally
equal to "false", yet if we evaluate its extracted version, then the
result is "false". *)

(* We begin by defining what it means to be an isomorphism. Note that
we use "sig" instead of "exists" as we want to be able to extract the
functions from the witness of isomorphism. *)
Definition iso A B := sig (A:=(A -> B) * (B -> A)) (fun x => match x with
  | (i, j) => (forall a : A, j (i a) =  a) /\   
              (forall b : B, i (j b) =  b)
  end).

Definition iso_to : forall A B, iso A B -> A -> B.
unfold iso. intros A B e. destruct e as [x _]. destruct x as [to _]. assumption.
Defined.

Definition iso_from : forall A B, iso A B -> B -> A.
unfold iso. intros A B e. destruct e as [x _]. destruct x as [_ from]. assumption.
Defined.

(* If we have an isomorphism, we have a propositional equality. *)
Axiom univalence : forall (A B : Set), iso A B -> A = B.

(* Assuming univalence, we now have two distinct proofs of the
propositional equality "bool = bool": "refl" and the one induced by
the automorphism "not" *)
Definition boolEq0 : bool = bool.
exact (eq_refl bool).
Defined.

Definition negbIso : iso bool bool.
unfold iso. exists (negb, negb); split; intros x; case x; reflexivity.
Defined.

Definition boolEq1 : bool = bool.
exact (univalence bool bool negbIso).
Defined.

(* We can transport a value in a total space of a fibration P along a
path in the base A.*)
Definition transport : forall A, forall (P : A -> Type), 
  forall (x y : A),
  forall (path : x = y),
  P x -> P y.
intros A P x y path px. inversion path. rewrite <- path. assumption.
Defined.

(* This development is based on the blog post:
http://homotopytypetheory.org/2012/01/22/univalence-versus-extraction/ *)

(* Extra "computation rule" for "transport": transporting along an
isomorphism is the same as applying the isomorphism. *)
Axiom transportUnivalence : forall (A B : Set) (P : Type -> Type) (e :
iso A B) (a : A), transport Set (fun (A : Set) => A) A B (univalence A
B e) a = iso_to A B e a.

Definition x : bool.
exact (transport Set (fun A => A) bool bool boolEq1 true).
Defined.

(* "x" is propositionally equal to "false", using the "computation
rule" for "transport" *)
Theorem xisfalse : x = false.  
Proof.  
unfold x. unfold boolEq1. assert (iso_to bool bool negbIso true =
false). compute. reflexivity. rewrite <- H. exact (transportUnivalence
bool bool (fun A => A) negbIso true).
Defined.

End InconsistentExtraction.

(* However, if we look at the extracted code, we notice that "x" gets
extracted to:

x :: Bool
x =
  transport __ __ True

which evaluates to "True", which is not propositionally equal to
"False". Coq's extraction mechanism assumes Prop satisfies proof
irrelevance, but this is not the case anymore if we assume univalence.
*)

Extraction Language Haskell.
Extraction InconsistentExtraction.
