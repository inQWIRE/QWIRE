Require Import Program. 
Require Import Contexts.
Require Import TypedCircuits.
Require Import FlatCircuits.
Require Import Examples.
Require Import List.
Require Import Arith.
Require Import Quantum.
Require Import Omega.
Import ListNotations.

Class Denote source target :=
{
    correctness : target -> Prop;
    denote : source -> target;
    denote_correct : forall (x : source), correctness (denote x)
}.
Notation "〚 s 〛" := (denote s) (at level 10).

(** Wire Denotation **)

Open Scope circ_scope.

Fixpoint num_wires (W : WType) : nat := 
  match W with
  | One => 0
  | Qubit => 1
  | Bit => 1
  | W1 ⊗ W2 => num_wires W1 + num_wires W2
  end.

Fixpoint num_elts (Γ : Ctx) : nat :=
  match Γ with
  | [] => 0
  | None :: Γ' => num_elts Γ'
  | Some _ :: Γ' => S (num_elts Γ')
  end.
Definition num_elts_o (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => 0
  | Valid Γ' => num_elts Γ'
  end.


Close Scope circ_scope.

Instance denote_WType : Denote WType nat :=
{|
    correctness := fun _ => True;
    denote := num_wires;
    denote_correct := fun _ => I
|}.
Instance denote_Ctx : Denote Ctx nat :=
{|
    correctness := fun _ => True;
    denote := num_elts;
    denote_correct := fun _ => I
|}.
Instance denote_OCtx : Denote OCtx nat :=
{|
    correctness := fun _ => True;
    denote := num_elts_o;
    denote_correct := fun _ => I
|}.

(** Unitary Denotation **)

Fixpoint denote_unitary {W} (U : Unitary W) : Square (2^〚W〛) :=
  match U with  
  | H => hadamard 
  | σx => pauli_x
  | σy => pauli_y
  | σz => pauli_z
  | CNOT => control pauli_x
  | TypedCircuits.control _ g => control (denote_unitary g)
  | TypedCircuits.bit_control _ g => control (denote_unitary g)  
  | TypedCircuits.transpose _ g => (denote_unitary g)†
  end. 

Lemma unitary_wf : forall {W} (U : Unitary W), WF_Matrix (denote_unitary U).
Proof.
  induction U.
  + apply WF_hadamard.
  + apply WF_pauli_x.
  + apply WF_pauli_y.
  + apply WF_pauli_z.
  + apply WF_control. apply WF_pauli_x.
  + simpl. apply WF_control. assumption.    
  + simpl. apply WF_control. assumption.    
  + simpl. apply WF_conj_transpose. assumption.    
Qed.

Lemma unitary_gate_unitary : forall {W} (U : Unitary W), unitary_matrix (denote_unitary U).
Proof.
  induction U.
  + apply H_unitary.
  + apply σx_unitary.
  + apply σy_unitary.
  + apply σz_unitary.
  + apply cnot_unitary.
  + simpl. apply control_unitary; assumption. (* NB: Admitted lemma *)
  + simpl. apply control_unitary; assumption. (* NB: Admitted lemma *)
  + simpl.
    unfold unitary_matrix in *.
    rewrite conj_transpose_involutive.
    apply Minv_left in IHU as [_ S]. (* NB: Admitted lemma *)
    assumption.
Qed.

Instance denote_Unitary {W} : Denote (Unitary W) (Square (2^〚W〛)) :=
{|
    correctness := fun m => WF_Matrix m /\ unitary_matrix m;
    denote := denote_unitary;
    denote_correct := fun U => conj (unitary_wf U) (unitary_gate_unitary U)
|}.

(** Gate Denotation *)

Definition denote_gate {W1 W2} (g : Gate W1 W2) : 
  Superoperator (2^〚W1〛) (2^〚W2〛) :=
  match g with
  | U _ u  => super (〚u〛)
  | init0 => new0_op 
  | init1 => new1_op
  | new0 => new0_op
  | new1 => new1_op 
  | meas => meas_op
  | discard => discard_op
  end.

Definition super_op_correctness {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Lemma denote_gate_correct : forall {W1} {W2} (g : Gate W1 W2), 
                            super_op_correctness (denote_gate g). 
Proof.
  unfold super_op_correctness.
Admitted.

Instance denote_Gate {W1 W2} : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := super_op_correctness;
    denote := denote_gate;
    denote_correct := denote_gate_correct
|}.

(*
Eval compute in (denote_unitary CNOT 0%nat 0%nat).
Eval compute in (denote_unitary CNOT 0%nat 1%nat).
Eval compute in (denote_unitary CNOT 1%nat 0%nat).
Eval compute in (denote_unitary CNOT 1%nat 1%nat).
Eval compute in (denote_unitary CNOT 2%nat 2%nat).
Eval compute in (denote_unitary CNOT 2%nat 3%nat).
Eval compute in (denote_unitary CNOT 3%nat 2%nat).
Eval compute in (denote_unitary CNOT 3%nat 3%nat).
*)


(*
Eval simpl in (from_HOAS_Box hadamard_measure).
Eval compute in (from_HOAS_Box hadamard_measure).
Eval vm_compute in (from_HOAS_Box hadamard_measure).
*)

Notation bnat n := (sig (fun i => i < n)).

Program Fixpoint zip_to (m n: nat) (l : list (bnat n)) :
  list (bnat n * bnat n) :=
  match l with
  | nil => nil 
  | x :: xs => match m <? n with 
              | true => (m, x) :: zip_to (S m) n xs
              | false => nil
              end
  end.
Next Obligation. apply Nat.ltb_lt. auto. Defined. 

Program Fixpoint swap_list_aux 
  (n : nat) (l : list (bnat n * bnat n)) : Square  (2^n) :=
  match l with
  | nil => Id (2^n)
  | cons (a,b) xs => swap_two n a b × swap_list_aux n xs
  end. 


Definition swap_list (n : nat) (l : list (bnat n)) :=
  swap_list_aux n (zip_to 0 n l). 

Program Definition my_one : {i : nat | i < 2} := S O.
Lemma swap_list_swap : swap_list 2 [my_one] = swap.
Proof.
  simpl.
  unfold swap_list, swap_list_aux.
  simpl.
  rewrite Mmult_1_r. 
  apply swap_two_base.
  (* .. and we're done here *)
Admitted.

(*

(*
Require Import Coq.Vectors.Vector.

Definition LList := t.
*)


Program Fixpoint swap_list {m n} (v : LList (sig (fun i => i < n)) m) : Square (2^n) :=
  match v with 
  | nil => Id (2^(n-m))
  | cons i _ v' => (swap_to_0 n i) × ((Id 2) ⊗ (@swap_list (m-1) (n-1) v'))
  end.
Next Obligation. rewrite Nat.sub_0_r. reflexivity. Defined.
Next Obligation. rewrite Nat.sub_0_r. reflexivity. Defined.
Next Obligation. rewrite plus_0_r.  reflexivity. Defined.
Next Obligation. rewrite Nat.sub_0_r. reflexivity. Defined.
*)

Local Obligation Tactic := program_simpl; unify_pows_two; try omega.

Program Definition pad {m} n (pf: m <= n) (A : Square (2^m)) : Square (2^n) :=
  (A ⊗ Id (2^ (n - m))).

Definition apply_U {m n} (U : Square (2^m)) (ρ : Density (2^n)) 
  (l : list (bnat n)) {pf : m <= n} : Density (2^n) := 
  let S := swap_list n l in 
  let SU := S × (pad n pf U) × S† in  
  super SU ρ.

(*
Program Definition pad_k0 n : Matrix (2^(S n)) (2^n) := (|0⟩ ⊗ Id (2^n)).
Program Definition pad_k1 n : Matrix (2^(S n)) (2^n) := (|1⟩ ⊗ Id (2^n)).
Program Definition pad_b0 n : Matrix (2^n) (2^(S n)) := (⟨0| ⊗ Id (2^n)).
Program Definition pad_b1 n : Matrix (2^n) (2^(S n)) := (⟨1| ⊗ Id (2^n)).
*)
Lemma bnat_gt_0 : forall n, bnat n -> 0 < n.
Proof.
  intros n [b pf].
  revert b pf.
  induction n; intros b pf.
  - inversion pf.
  - omega. 
Qed.

(* Jennifer: What is the point of k here? *)
Program Definition apply_new0 {n} (ρ : Density (2^n)) (k : bnat n) : 
  Density (2^(n+1)) := super (|0⟩ ⊗ Id (2^n)) ρ.

Program Definition apply_new1 {n} (ρ : Density (2^n)) (k : bnat n) : 
  Density (2^(n+1)) := super (|1⟩ ⊗ Id (2^n)) ρ.

Program Definition apply_discard {n} (ρ : Density (2^n)) (k : bnat n) : 
  Density (2^(n-1)) := 
  let S := @swap_two n 0 k _ _ in 
  super ((⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ super ((⟨1| ⊗ Id (2^(n-1))) × S) ρ.

(* Jennifer: it would help to have k be a list *)
Program Definition apply_meas {n} (ρ : Density (2^n)) (k : bnat n) : 
  Density (2^n) := 
  let S := @swap_two n 0 k _ _ in 
  super (S† × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ 
  super (S† × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S) ρ.

(*
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapList.

  Lemma compare_nat : forall (x y : nat), Compare lt eq x y.
  Proof.
    induction x; destruct y. 
    - apply EQ; auto. 
    - apply LT; omega. 
    - apply GT; omega.
    - destruct (IHx y).
      * apply LT; omega.
      * apply EQ; omega.
      * apply GT; omega.
  Qed.

Print eq.
Module Ordered_Nat <: OrderedType.
  Definition t := nat.
  Definition eq := (@eq nat).
  Definition lt := lt.
  Definition eq_refl := (@eq_refl nat).
  Definition eq_sym := (@eq_sym nat).
  Definition eq_trans := (@eq_trans nat).
  Definition lt_trans := lt_trans. SearchAbout (_ < _ -> not (_ = _)).
  Definition lt_not_eq := Nat.lt_neq. SearchAbout (Compare _ _ _ _).

    

  Definition compare := compare_nat.
  Definition eq_dec := eq_nat_dec.
End Ordered_Nat.
Module FMap := Raw Ordered_Nat.
*)

(* We want a finite map from natural numbers (indices into a context) 
   to natural numbers (indices into a matrix)
   Therefore the domain of the map should be bounded by a natural number.
 *)


Definition pad_bnat {m n} {pf : m <= n} (b : bnat m) : bnat n.
Admitted.

(*(* is this always going to be the identity? *)
Program Fixpoint compress (Γ : Ctx)  : list (bnat 〚Γ〛) :=
  match Γ with
  | []           => []
  | None   :: Γ' => compress Γ'
  | Some _ :: Γ' => num_elts Γ' :: map pad_bnat (compress Γ')
  end.*)


Lemma singleton_num_elts : forall x W Γ, SingletonCtx x W Γ -> num_elts Γ = 1%nat.
Proof.
  induction 1; simpl in *; omega. 
Qed.

(* The intention is that the length of the list is equal to num_elts Γ *)
Definition env n Γ := { ls : list (bnat n) & length ls = 〚Γ〛}.
Hint Unfold env.

(*Notation env Γ := (list (bnat (num_elts_o Γ))).*)

Inductive Disjoint : Ctx -> Ctx -> Set :=
| DisjointNilL  : forall Γ, Disjoint [] Γ
| DisjointNilR  : forall Γ, Disjoint Γ []
| DisjointConsNone : forall Γ1 Γ2, Disjoint Γ1 Γ2 -> Disjoint (None :: Γ1) (None :: Γ2)
| DisjointConsSomeL : forall W Γ1 Γ2, Disjoint Γ1 Γ2 -> Disjoint (Some W :: Γ1) (None :: Γ2)
| DisjointConsSomeR : forall W Γ1 Γ2, Disjoint Γ1 Γ2 -> Disjoint (None :: Γ1) (Some W :: Γ2)
.
Inductive DisjointO : OCtx -> OCtx -> Set :=
| DisjointValid : forall Γ1 Γ2, Disjoint Γ1 Γ2 -> DisjointO Γ1 Γ2
.
Lemma disjoint_dec Γ1 Γ2 : DisjointO Γ1 Γ2 + {Γ1 ⋓ Γ2 = Invalid}.
Admitted.

Lemma num_elts_o_cons_None : forall Γ1 Γ2, 〚Valid (None :: Γ1) ⋓ Valid (None :: Γ2)〛 = 〚Valid Γ1 ⋓ Valid Γ2〛.
Admitted.



Lemma coerce_env' : forall Γ1 Γ2, 〚Γ1〛 = 〚Γ2〛 -> list (bnat (num_elts_o Γ1))
                  -> list (bnat (num_elts_o Γ2)).
Proof.
  intros Γ1 Γ2 H ls. simpl in *. rewrite H in ls. exact ls.
Defined.

Lemma coerce_env : forall m n Γ1 Γ2, m <= n -> 〚Γ1〛 = 〚Γ2〛 -> env m Γ1 -> env n Γ2.
Proof. 
  intros m n Γ1 Γ2 pf H [ls pf_ls]. simpl in *.
  exists (map (@pad_bnat _ _ pf) ls). 
  rewrite map_length.
  rewrite pf_ls. auto.
Defined.

(* Don't do anything to the values of ls1 and ls2 *)
Definition interleave {n} {Γ1 Γ2 : OCtx} (disj : DisjointO Γ1 Γ2)
                      (ls1 : env n Γ1) (ls2 : env n Γ2) :
                      〚Γ1〛 + 〚Γ2〛 <= n -> env n (Γ1 ⋓ Γ2).
Proof.
    destruct ls1 as [ls1 pf_ls1].
    destruct ls2 as [ls2 pf_ls2].
    revert ls1 ls2 pf_ls1 pf_ls2.
    destruct disj as [Γ1 Γ2 disj].
    induction disj; intros ls1 ls2 pf_ls1 pf_ls2 pf_n.
    * rewrite merge_nil_l. exists ls2; auto.
    * rewrite merge_nil_r. exists ls1; auto.
    * apply (coerce_env n n (Γ1 ⋓ Γ2)); [apply le_n | rewrite num_elts_o_cons_None; auto | ].
      apply (IHdisj ls1 ls2); auto.
    * simpl in *. remember (merge' Γ1 Γ2) as Γ.
      destruct Γ as [ | Γ]; [exists []; auto | ]. 
      destruct ls1 as [ | i ls1]; [inversion pf_ls1 | ].
      destruct (IHdisj ls1 ls2) as [ls pf_ls]; auto.
      + eapply le_trans; [| exact pf_n]; omega.
      + exists (i :: ls). simpl. f_equal; auto.
    * simpl in *. remember (merge' Γ1 Γ2) as Γ.
      destruct Γ as [ | Γ]; [exists []; auto | ]. 
      destruct ls2 as [ | i ls2]; [inversion pf_ls2 | ].
      destruct (IHdisj ls1 ls2) as [ls pf_ls]; auto.
      + eapply le_trans; [| exact pf_n]; omega.
      + exists (i :: ls). simpl. f_equal; auto.
Defined.

Definition shift_up_by {n} m (b : bnat n) : bnat (m + n).
Admitted.

Definition shift_map_up_by {n} m {Γ} : env n Γ -> env (m+n) Γ.
Admitted.


Lemma num_elts_merge : forall (Γ1 Γ2 : OCtx) (Γ : Ctx), Γ1 ⋓ Γ2 = Γ ->
                       num_elts_o Γ = (num_elts_o Γ1 + num_elts_o Γ2)%nat.
Admitted.

Lemma disjoint_merge_valid : forall Γ1 Γ2, DisjointO Γ1 Γ2 -> is_valid (Γ1 ⋓ Γ2).
Admitted.

Locate "{ _ } + { _ }". Print sumor.
Program Definition merge_env (Γ1 Γ2 : OCtx) (ls1 : env (num_elts_o Γ1) Γ1) (ls2 : env (num_elts_o Γ2) Γ2) 
                     : env (num_elts_o (Γ1 ⋓ Γ2)) (Γ1 ⋓ Γ2) :=
  match disjoint_dec Γ1 Γ2 with
  | inleft disj => let ls2' := shift_map_up_by (num_elts_o Γ1) ls2 in
                 interleave disj (coerce_env _ _ _ _ _ _ ls1) (coerce_env _ _ _ _ _ _ ls2') _
  | inright _ => existT _ [] _
  end.
Next Obligation.
  destruct (disjoint_merge_valid _ _ disj) as [Γ H].
  rewrite H.
  rewrite (num_elts_merge Γ1 Γ2 Γ); auto.
  destruct Γ1; [ inversion H | unfold num_elts_o; omega ].
Qed.
Next Obligation.
  destruct (disjoint_merge_valid _ _ disj) as [Γ H].
  erewrite <- num_elts_merge; eauto. rewrite <- H. omega.
Qed.
Next Obligation.
  destruct (disjoint_merge_valid _ _ disj) as [Γ H].
  erewrite <- num_elts_merge; eauto. rewrite <- H. omega.
Qed.
Next Obligation.
  rewrite wildcard'. simpl. reflexivity.
Qed.
  

Definition singleton_env {Γ x W} (pf : SingletonCtx x W Γ) : env (num_elts Γ) Γ.
Proof.
  apply singleton_num_elts in pf.
  assert (my_zero : bnat (num_elts Γ)). exists (0%nat). omega.
  exists [my_zero]. simpl. omega.
Defined.

Definition empty_env : env (num_elts_o ∅) ∅.
Proof.
  exists []. simpl. omega.
Defined.


Fixpoint make_env {Γ : OCtx} {W} (p : Pat Γ W) : env (num_elts_o Γ) Γ.
  refine (
  match p with
  | unit => empty_env
  | pair Γ1 Γ2 Γ0 W1 W2 valid merge p1 p2 => 
      let ls1 := make_env Γ1 W1 p1 in
      let ls2 := make_env Γ2 W2 p2 in 
      let ls' := merge_env _ _ ls1 ls2 in
      _
  | qubit x Γ sing => singleton_env sing
  | bit   x Γ sing => singleton_env sing
  end).
  rewrite merge. exact ls'.
Defined.

(* A pattern Γ |- p : W will result in a nxn matrix, where
   n is the number of non-zero elements in Γ
 *)
Definition denote_pat {Γ W} (p : Pat Γ W) : Square (2^(num_elts_o Γ)) :=
  let (ls,_) := make_env p in 
  swap_list (num_elts_o Γ) ls.

Lemma denote_pat_WF : forall Γ W (p : Pat Γ W),
      WF_Matrix (denote_pat p).
Admitted.

Lemma denote_pat_unitary : forall Γ W (p : Pat Γ W),
      unitary_matrix (denote_pat p).
Proof.
Admitted.


Lemma denote_pat_correct : forall Γ W (p : Pat Γ W),
      WF_Matrix (denote_pat p) /\ unitary_matrix (denote_pat p).
Proof.
  intros. split; [apply denote_pat_WF | apply denote_pat_unitary].
Qed.

Instance denote_Pat {Γ W} : Denote (Pat Γ W) (Square (2 ^ (num_elts_o Γ))) :=
{|
    correctness := fun m => WF_Matrix m /\ unitary_matrix m;
    denote := denote_pat;
    denote_correct := denote_pat_correct Γ W
|}.

Fixpoint denote_circuit {Γ W} (c : Flat_Circuit Γ W) 
                        : Superoperator (2^〚Γ〛) (2 ^ 〚W〛).
Admitted.


(*Fixpoint denote_circuit {Γ : Ctx} {W : WType} (c : Flat_Circuit Γ W)*)

(* *)