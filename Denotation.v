Require Import Program. 
Require Import Contexts.
Require Import TypedCircuits.
Require Import FlatCircuits.
(*Require Import Examples.*)
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

Notation bnat n := (sig (fun i => i < n)).

(* The first argument is the upper bound on the elements of the list *)
(* The second argument is the length of the list *)
Definition env n m := sig (fun (ls : list (bnat n)) => length ls <= m).
Hint Unfold env.


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

Definition super_plus {m n}
                      (s1 : Superoperator m n)
                      (s2 : Superoperator m n)
                    : Superoperator m n :=
  fun ρ => s1 ρ .+ s2 ρ.

Definition denote_gate {W1 W2} n (g : Gate W1 W2) : 
  Superoperator (2^〚W1〛 * n) (2^〚W2〛 * n) :=
  match g with
  | U _ u  => super (〚u〛 ⊗ Id n)
  | init0 => super (|0⟩ ⊗ Id n) 
  | init1 => super (|1⟩ ⊗ Id n) 
  | new0 => super (|0⟩ ⊗ Id n) 
  | new1 => super (|1⟩ ⊗ Id n) 
  | meas => super_plus (super (|0⟩⟨0| ⊗ Id n)) (super (|1⟩⟨1| ⊗ Id n))
  | discard => super_plus (super (⟨0| ⊗ Id n)) (super (⟨1| ⊗ Id n))
  end.
 
Definition super_op_correctness {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Lemma denote_gate_correct : forall {W1} {W2} n (g : Gate W1 W2), 
                            super_op_correctness (denote_gate n g). 
Proof.
  unfold super_op_correctness.
Admitted.

Instance denote_Gate {W1 W2} : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := super_op_correctness;
(*    denote := denote_gate; *)
(*    denote_correct := denote_gate_correct *)
|}.
Admitted.

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


Definition swap_list {n m : nat} (η : env n m) :=
  let (ls,_) := η in 
  swap_list_aux n (zip_to 0 n ls). 
Definition mk_bnat i n {pf : i < n} : bnat n :=
  exist _ i pf.
Program Definition mk_env {n} m (ls : list (bnat n)) {pf : length ls <= m} 
                   : env n m :=
  exist _ ls pf.


Program Definition my_one : bnat 2 := S O.
Program Lemma swap_list_swap : swap_list (mk_env 2 [mk_bnat 1 2]) = swap.
(*Proof.
  simpl.
  rewrite Mmult_1_r.  
  rewrite swap_two_base.
  (* .. and we're done here *) *)
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
  (l : env n m) {pf : m <= n} : Density (2^n) := 
  let S := swap_list l in 
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



Definition coerce_bnat {m n} (pf_m_n : m <= n) (b : bnat m) : bnat n.
  destruct b as [x pf_x_m].
  exists x. 
  SearchAbout (_ < _ -> _ <= _ -> _ < _).
  exact (lt_le_trans x m n pf_x_m pf_m_n).
Defined.
Print coerce_bnat.


Definition coerce_env {n1 n2 m1 m2} (pf_n : n1 <= n2) (pf_m : m1 <= m2)
           (η : env n1 m1) : env n2 m2.
Proof. 
  destruct η as [ls1 len].
  exists (map (coerce_bnat pf_n) ls1).
  rewrite map_length. 
  apply (le_trans _ _ _ len pf_m).
Defined.



Lemma num_elts_merge : forall (Γ1 Γ2 : OCtx) (Γ : OCtx), Γ1 ⋓ Γ2 = Γ -> is_valid Γ->
                       num_elts_o Γ = (num_elts_o Γ1 + num_elts_o Γ2)%nat.
Admitted.

(* Don't do anything to the values of ls1 and ls2 *)
Definition interleave {n} {Γ1 Γ2 : OCtx} (disj : DisjointO Γ1 Γ2)
                      (ls1 : env n (〚Γ1〛)) (ls2 : env n (〚Γ2〛)) :
                      〚Γ1〛 + 〚Γ2〛 <= n -> env n (〚Γ1 ⋓ Γ2〛).
Proof.
    destruct ls1 as [ls1 pf_ls1].
    destruct ls2 as [ls2 pf_ls2].
    revert ls1 ls2 pf_ls1 pf_ls2.
    destruct disj as [Γ1 Γ2 disj].
    induction disj; intros ls1 ls2 pf_ls1 pf_ls2 pf_n.
    { rewrite merge_nil_l. exists ls2; auto. }
    { rewrite merge_nil_r. exists ls1; auto. }
    { refine (coerce_env _ _ (IHdisj ls1 ls2 _ _ _)); auto.
      rewrite num_elts_o_cons_None; auto.
    }
    { simpl in *. remember (merge' Γ1 Γ2) as Γ.
      destruct Γ as [ | Γ]; [exists []; auto | ].
      erewrite (num_elts_merge (Valid (Some W :: Γ1)) (Valid (None :: Γ2)));
        [ | simpl; rewrite <- HeqΓ; auto | apply valid_valid]. 
      destruct ls1 as [ | i ls1].
      { exists ls2. simpl. omega. }
      { destruct (IHdisj ls1 ls2) as [ls pf_ls]; auto.
        +{ simpl in pf_ls1. omega. }
        +{ eapply le_trans; [| exact pf_n]; omega. }
        +{ exists (i :: ls). simpl. 
           rewrite (num_elts_merge Γ1 Γ2) in pf_ls; [ | auto | apply valid_valid].
           simpl in pf_ls.
           omega.
          }
      }
    }
    { simpl in *. remember (merge' Γ1 Γ2) as Γ.
      destruct Γ as [ | Γ]; [exists []; auto | ]. 
      rewrite (num_elts_merge (Valid (None :: Γ1)) (Valid (Some W :: Γ2))); 
        [ | simpl; rewrite <- HeqΓ; auto | apply valid_valid]. 
      destruct ls2 as [ | i ls2]. 
      { exists ls1. simpl. omega. }
      destruct (IHdisj ls1 ls2) as [ls pf_ls]; auto.
      +{ simpl in pf_ls2. omega. }
      +{ eapply le_trans; [| exact pf_n]; omega. }
      +{ exists (i :: ls). simpl. 
           rewrite (num_elts_merge Γ1 Γ2) in pf_ls; [ | auto | apply valid_valid].
           simpl in pf_ls.
           omega.
       }
    }
Defined. 

Definition shift_up_by {n} m (b : bnat n) : bnat (m + n).
Admitted.

Definition shift_map_up_by {n} m {Γ} : env n Γ -> env (m+n) Γ.
Admitted.


Lemma disjoint_merge_valid : forall Γ1 Γ2, DisjointO Γ1 Γ2 -> is_valid (Γ1 ⋓ Γ2).
Admitted.

Locate "{ _ } + { _ }". Print sumor. About coerce_env. About Tensor.
Program Definition merge_env (Γ1 Γ2 : OCtx) (W1 W2 : WType)
                             (ls1 : env (〚W1〛) (〚Γ1〛)) (ls2 : env (〚W2〛) (〚Γ2〛)) 
                             (eq1 : 〚W1〛=〚Γ1〛) (eq2 : 〚W2〛 = 〚Γ2〛)
                            : env (〚Tensor W1 W2〛) (〚Γ1 ⋓ Γ2〛) :=
  match disjoint_dec Γ1 Γ2 with
  | inleft disj => let ls2' := shift_map_up_by (num_elts_o Γ1) ls2 in
                 interleave disj (coerce_env _ _ ls1) (coerce_env _ _ ls2') _
  | inright _   => []
  end.
(*
Next Obligation.
  destruct ls1. destruct ls2. simpl.
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
*)


Definition singleton_env {Γ x W} (pf : SingletonCtx x W Γ) 
                         : 〚W〛=1%nat -> env (〚W〛) (〚Γ〛).
Proof.
  apply singleton_num_elts in pf.
  assert (my_zero : bnat 1). exists (0%nat). omega.
  intros; subst. rewrite H. simpl. rewrite pf.
  exists [my_zero]. simpl. omega.
Defined.

Definition empty_env : env (〚One〛) (〚∅〛).
Proof.
  exists []. simpl. omega.
Defined.


Lemma pat_square : forall Γ W (p : Pat Γ W), 〚Γ〛 = 〚W〛.
Proof.
  induction 1; simpl; auto.
  - eapply singleton_num_elts; eauto.
  - eapply singleton_num_elts; eauto.
  - inversion i. rename x into Γ. inversion H; subst.
    erewrite num_elts_merge; [ | eauto | apply valid_valid].
    simpl in *.
    omega.
Qed.

Fixpoint make_env {Γ : OCtx} {W} (p : Pat Γ W) : env (〚W〛) (〚Γ〛).
  refine (
  match p with
  | unit => empty_env
  | pair Γ1 Γ2 Γ0 W1 W2 valid merge p1 p2 => 
      let ls1 := make_env Γ1 W1 p1 in
      let ls2 := make_env Γ2 W2 p2 in 
      let ls' := merge_env _ _ _ _ ls1 ls2 _ _ in
      _
  | qubit x Γ sing => singleton_env sing _
  | bit   x Γ sing => singleton_env sing _
  end); simpl; auto.
  rewrite merge. exact ls'.
  Unshelve.
  erewrite pat_square; auto.
  erewrite pat_square; auto.
Defined.


(* A pattern Γ |- p : W will result in a nxn matrix, where
   n is the number of non-zero elements in Γ
 *)
Definition denote_pat {Γ W} (p : Pat Γ W) : Matrix (2^〚W〛) (2^〚Γ〛).
  erewrite pat_square; [ | eauto].
  exact (swap_list (make_env p)).
Defined.

(*
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
*)

Definition denote_order_gates {Γ1 W1 Γ2 W2}
                              (p1 : Pat Γ1 W1) (g : Gate W1 W2) (p2 : Pat Γ2 W2)
                              : Superoperator (2 ^ 〚W2〛) (2 ^ 〚W1〛).
Admitted.

Definition super_tensor : forall n1 n2 m1 m2,
                          Superoperator n1 n2 -> Superoperator m1 m2
                        -> Superoperator (n1 * m1) (n2 * m2).
Proof.
  intros n1 n2 m1 m2 s1 s2 ρ.


Lemma pow_distr : forall (m n p : nat), p ^ (m + n) = ((p ^ m) * (p ^ n))%nat.
Admitted.

Definition cross_list {A B} (ls1 : list A) (ls2 : list B) : list (A * B) :=
  let f := fun ls0 a => fold_left (fun ls0' b => (a,b)::ls0') ls2 ls0 in
  fold_left f ls1 [].

Lemma cross_nil_r : forall {A B} (ls : list A), cross_list ls ([] : list B) = [].
Proof.
  induction ls; simpl; auto.
Qed.

Lemma cross_list_distr_l : forall {A B} a (ls1 : list A) (ls2 : list B),
      length (cross_list (a :: ls1) ls2) 
    = (length ls2 + length (cross_list ls1 ls2))%nat.
Admitted.

Lemma cross_list_distr_r : forall {A B} b (ls1 : list A) (ls2 : list B),
      length (cross_list ls1 (b :: ls2))
    = (length ls1 + length (cross_list ls1 ls2))%nat.
Admitted.

Lemma length_cross_list : forall {A B} (ls1 : list A) (ls2 : list B),
      length (cross_list ls1 ls2) = (length ls1 * length ls2)%nat.
Proof.
  induction ls1 as [ | a ls1]; destruct ls2 as [ | b ls2]; simpl; try omega.
  - rewrite cross_nil_r. simpl. omega.
  - rewrite cross_list_distr_l. simpl. rewrite cross_list_distr_r.
    rewrite IHls1. 
    f_equal.
    f_equal.
    apply eq_trans with ((length ls1 * 1 + length ls1 * length ls2))%nat; try omega.
    rewrite <- Nat.mul_add_distr_l. simpl. reflexivity.
Qed.

Fixpoint get_interpretations (W : WType) : list (interpret W) :=
  match W with
  | One => [tt]
  | Tensor W1 W2 => cross_list (get_interpretations W1) (get_interpretations W2)
  | Qubit => [true;false]
  | Bit   => [true;false]
  end.


Definition discard_left : forall m n, Superoperator (2 ^ m * 2 ^ n) (2 ^ n).
  induction m; intros n ρ.
  - simpl in ρ. rewrite plus_0_r in ρ. exact ρ.
  - rewrite <- pow_distr in ρ.
    apply apply_discard in ρ; [ | exists 0%nat; omega].
    apply IHm.
    simpl in ρ. 
    rewrite <- minus_n_O in ρ.
    rewrite pow_distr in ρ.
    exact ρ.
Defined.

Fixpoint sum_superoperators_with {m n} 
                 (s : Superoperator m n) (ls : list (Superoperator m n)) 
                 : Superoperator m n :=
  match ls with
  | []        => s
  | s' :: ls' => super_plus s (sum_superoperators_with s' ls')
  end.



Lemma interp_nonzero : forall W, 0%nat < length (get_interpretations W).
Proof.
  induction W; simpl; try omega.
  rewrite length_cross_list.
  apply Nat.mul_pos_pos; auto. 
Qed.

Definition sum_over_interpretations {W m n} 
        (f : interpret W -> Superoperator m n)
        : Superoperator m n.
  set (vs := get_interpretations W).
  assert (H_neq : 0%nat <> length vs ). { apply lt_0_neq. apply interp_nonzero. }
  destruct vs as [ | v vs]; [absurd (0 <> 0); auto | ].
  exact (sum_superoperators_with (f v) (map f vs)).
Defined.


Definition denote_lift {w m n} 
                      (f : interpret w -> Superoperator (2^m) (2^n))
                     : Superoperator (2 ^ 〚w〛 * 2^m) (2^n) :=
  let supers : interpret w -> Superoperator (2 ^ 〚w〛 * (2^m)) (2^n)
              := fun v ρ => f v (discard_left (〚w〛) m ρ) in
  sum_over_interpretations supers.

Fixpoint denote_circuit {Γ W} (c : Flat_Circuit Γ W) 
                        : Superoperator (2 ^ 〚Γ〛) (2^〚W〛).
  destruct c; subst.
  - refine (super (denote_pat p)).
  - intros ρ.
    apply (denote_circuit _ _ c).
    rewrite (num_elts_merge ctx2 ctx); auto.
    rewrite (num_elts_merge ctx1 ctx) in ρ; auto.
    rewrite pow_distr in *.
    apply (denote_gate (2 ^ (num_elts_o ctx))) in g.
    rewrite <- (pat_square _ _ p) in g.
    rewrite <- (pat_square _ _ p0) in g.
    exact (g ρ).
  - intros ρ.
    rewrite (num_elts_merge ctx1 ctx2) in ρ; auto.
    rewrite pow_distr in ρ.
    set (f'  := fun w => denote_circuit _ _ (f w)).
    apply (denote_lift f'). 
    rewrite <- (pat_square _ _ p). exact ρ.
Defined.


(*Fixpoint denote_circuit {Γ : Ctx} {W : WType} (c : Flat_Circuit Γ W)*)

(* *)