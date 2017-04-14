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
Program Definition empty_env m n : env m n := [].
Next Obligation. omega. Defined.


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
Definition denote_gate1 {W1 W2} (g : Gate W1 W2) : Superoperator (2^〚W1〛) (2^〚W2〛).
Proof.
  rewrite <- (Nat.mul_1_r (2^〚W1〛)).
  rewrite <- (Nat.mul_1_r (2^〚W2〛)).
  exact (denote_gate 1 g).
Defined.


 
Definition super_op_correctness {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

(*
Lemma denote_gate_correct : forall {W1} {W2} n (g : Gate W1 W2), n <> 0 ->
                            super_op_correctness (denote_gate n g). 
Proof.
  intros W1 W2 n g.
  destruct g; unfold super_op_correctness; intros ρ mixed.
  - simpl. apply mixed_unitary; auto.
    apply (WF_kron (denote_unitary u) (Id n)).
apply unitary_wf.
  -
  -
  -
  -
  -
  -
Admitted.
*)
Check denote_gate.
Instance denote_Gate {W1 W2} : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := super_op_correctness;
    denote := denote_gate1
(*    denote_correct := denote_gate_correct *)
|}.
Proof.
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
Definition mk_env n m {p} (ls : list (bnat n)) {pf : length ls <= m}
                   {eq : n = p} : env p m.
  subst. exact (exist _ ls pf).
Defined.


Program Definition my_one : bnat 2 := S O.
(*Program Lemma swap_list_swap : swap_list (mk_env 2 _ [mk_bnat 1 2]) = swap.
(*Proof.
  simpl.
  rewrite Mmult_1_r.  
  rewrite swap_two_base.
  (* .. and we're done here *) *)
Admitted.*)

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

Lemma valid_disjoint : forall Γ1 Γ2, is_valid (Γ1 ⋓ Γ2) -> DisjointO Γ1 Γ2.
Proof.
  intros Γ1 Γ2 valid.
  assert (not_invalid :  ~ (is_valid Invalid)). { inversion 1. inversion H0. }
  destruct Γ1 as [ | Γ1]; [ absurd (is_valid Invalid); auto | ].
  destruct Γ2 as [ | Γ2]; [ absurd (is_valid Invalid); auto | ].
  constructor.
  revert Γ2 valid.
  induction Γ1 as [ | o1 Γ1]; intros Γ2 v; [constructor | ].
  destruct Γ2 as [ | o2 Γ2]; [constructor | ].
  destruct o1 as [ | W1]; destruct o2 as [ | W2];
    [absurd (is_valid Invalid); auto | | | ];
  constructor; apply IHΓ1; eapply valid_cons; eauto.
Qed.

(*
Lemma disjoint_dec Γ1 Γ2 : DisjointO Γ1 Γ2 + {Γ1 ⋓ Γ2 = Invalid}.
Admitted.
*)

Lemma merge_dec Γ1 Γ2 : is_valid (Γ1 ⋓ Γ2) + {Γ1 ⋓ Γ2 = Invalid}.
Proof.
  induction Γ1 as [ | Γ1]; [ right; auto | ].
  destruct  Γ2 as [ | Γ2]; [ right; auto | ].
  revert Γ2; induction Γ1 as [ | o1 Γ1]; intros Γ2.
  { simpl. left. apply valid_valid. }
  destruct Γ2 as [ | o2 Γ2]. 
  { simpl. left. apply valid_valid. }
  destruct (IHΓ1 Γ2) as [IH | IH].
  - destruct o1 as [ | W1]; destruct o2 as [ | W2]; simpl in *. 
    { right; auto. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }    
  - right. simpl in *. rewrite IH. destruct (merge_wire o1 o2); auto.
Qed.

Lemma num_elts_o_cons_None : forall Γ1 Γ2, 〚Valid (None :: Γ1) ⋓ Valid (None :: Γ2)〛 = 〚Valid Γ1 ⋓ Valid Γ2〛.
Proof.
  induction Γ1 as [ | o1 Γ1]; intros Γ2; auto. 
  destruct Γ2 as [ | o2 Γ2]; auto.
  destruct o1; destruct o2; auto;
  simpl in *;
    destruct (merge' Γ1 Γ2) eqn:H; auto.
Qed.


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
Proof.
Admitted.

(* Don't do anything to the values of ls1 and ls2 *)
Definition interleave {n} {Γ1 Γ2 : OCtx} (disj : is_valid (Γ1 ⋓ Γ2))
                      (ls1 : env n (〚Γ1〛)) (ls2 : env n (〚Γ2〛)) :
                      〚Γ1〛 + 〚Γ2〛 <= n -> env n (〚Γ1 ⋓ Γ2〛).
Proof.
    destruct ls1 as [ls1 pf_ls1].
    destruct ls2 as [ls2 pf_ls2].
    revert ls1 ls2 pf_ls1 pf_ls2.
    apply valid_disjoint in disj.
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
Program Definition merge_env (Γ1 Γ2 : OCtx) {n1 n2}
                             (ls1 : env n1 (〚Γ1〛)) (ls2 : env n2 (〚Γ2〛)) 
                             (pf1 : n1 = 〚Γ1〛) (pf2 : n2 = 〚Γ2〛)
                            : env (〚Γ1 ⋓ Γ2〛) (〚Γ1 ⋓ Γ2〛) :=
  match merge_dec Γ1 Γ2 with
  | inleft disj => let ls2' := shift_map_up_by (num_elts_o Γ1) ls2 in
                 interleave disj (coerce_env _ _ ls1) (coerce_env _ _ ls2') _
  | inright _   => []
  end.
Next Obligation. rewrite (num_elts_merge Γ1 Γ2 (Γ1 ⋓ Γ2)); [omega | auto | auto].
Defined.
Next Obligation. rewrite (num_elts_merge Γ1 Γ2 (Γ1 ⋓ Γ2)); [omega | auto | auto].
Defined.
Next Obligation. rewrite (num_elts_merge Γ1 Γ2 (Γ1 ⋓ Γ2)); [omega | auto | auto].
Defined.


Definition singleton_env {Γ x W} (pf : SingletonCtx x W Γ) 
                         : 〚W〛=1%nat -> env (〚W〛) (〚Γ〛).
Proof.
  apply singleton_num_elts in pf.
  assert (my_zero : bnat 1). exists (0%nat). omega.
  intros; subst. rewrite H. simpl. rewrite pf.
  exists [my_zero]. simpl. omega.
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
About merge_env.


Program Fixpoint make_env {Γ : OCtx} {W} (p : Pat Γ W) : env (〚W〛) (〚Γ〛) :=
  match p with
  | pair Γ1 Γ2 Γ0 W1 W2 valid merge p1 p2 => 
      let ls1 := make_env p1 in
      let ls2 := make_env p2 in 
      let (ls',pf) := merge_env _ _ ls1 ls2 _ _ in
      mk_env _ _ ls'
  | qubit x Γ sing => singleton_env sing _
  | bit   x Γ sing => singleton_env sing _
  | unit => empty_env _ _
  end. 
Next Obligation. erewrite pat_square; eauto. Defined.
Next Obligation. erewrite pat_square; eauto. Defined.
Next Obligation. erewrite num_elts_merge; eauto.
    erewrite pat_square; eauto. erewrite pat_square; eauto.
Defined.

(* A pattern Γ |- p : W will result in a nxn matrix, where
   n is the number of non-zero elements in Γ
 *)
Definition denote_pat {Γ W} (p : Pat Γ W) : Matrix (2^〚W〛) (2^〚Γ〛).
  erewrite pat_square; [ | eauto].
  exact (swap_list (make_env p)).
Defined.

Program Definition unitary_correctness {m n} (A : Matrix m n) := 
          forall (pf : m = n),
           WF_Matrix A /\ unitary_matrix A.

Instance Denote_Pat {Γ W} : Denote (Pat Γ W) (Matrix (2^〚W〛) (2^〚Γ〛)) :=
{|
    correctness := unitary_correctness;
    denote := denote_pat
|}.
Proof.
Admitted.





Program Definition get_Ctx (Γ : OCtx) : is_valid Γ -> Ctx :=
  match Γ with
  | Invalid => _
  | Valid Γ' => fun _ => Γ'
  end.
Next Obligation.
  absurd (is_valid Invalid); auto. intros _. destruct H. inversion H.
Defined.

Fixpoint Ctx_to_WType (Γ : Ctx) : WType :=
  match Γ with 
  | [] => One
  | None :: Γ' => Ctx_to_WType Γ'
  | Some W :: Γ' => Tensor W (Ctx_to_WType Γ')
  end.
Definition OCtx_to_WType (Γ : OCtx) (pf : is_valid Γ) : WType :=
  Ctx_to_WType (get_Ctx Γ pf).

Program Definition inc {n} (i : bnat n) : bnat (S n) := S i.

Program Fixpoint id_env' n : list (bnat n) :=
  match n with
  | 0 => []
  | S n' => 0%nat :: map inc (id_env' n')
  end.
Program Definition id_env n : env n n := id_env' n.
Next Obligation.
  induction n; simpl; auto.
  rewrite map_length. omega.
Defined.

(* This might need to be transposed?? *)
Program Definition apply_pat_in {Γ W} (p : Pat Γ W) Γ'
                        (pf : is_valid (Γ ⋓ Γ')) 
                        : Matrix (2 ^ (〚W〛 + 〚Γ'〛)) (2 ^ (〚Γ〛 + 〚Γ'〛)) :=
  let e := merge_env _ _ (make_env p) (id_env (〚Γ'〛)) _ _
  in swap_list e.
Next Obligation.
  set (sq := pat_square _ _ p). simpl in sq. auto. 
Defined.
Next Obligation.
  erewrite num_elts_merge; eauto.
  set (sq := pat_square _ _ p). simpl in sq. auto.
Defined.
Next Obligation.
  erewrite num_elts_merge; eauto.
Defined.


Definition compose_super {m n p} (g : Superoperator n p) (f : Superoperator m n)
                      : Superoperator m p :=
  fun ρ => g (f ρ).

Definition apply_gate {Γ1 Γ2 Γ : OCtx} {W1 W2} (g : Gate W1 W2) 
                   (p1 : Pat Γ1 W1) (p2 : Pat Γ2 W2) 
                   (pf1 : is_valid (Γ1 ⋓ Γ)) (pf2 : is_valid (Γ2 ⋓ Γ))
                   : Superoperator (2^〚Γ1 ⋓ Γ〛) (2^〚Γ2 ⋓ Γ〛).
  set (p1' := super (apply_pat_in p1 Γ pf1)).
  set (p2' := super ((apply_pat_in p2 Γ pf2)†)).
  set (g' := denote_gate (2^〚Γ〛) g).
  assert (H : forall Γ0 Γ0', is_valid (Γ0 ⋓ Γ0') ->
                             2^〚Γ0 ⋓ Γ0'〛 = (2^〚Γ0〛 * 2^〚Γ0'〛)%nat). 
    intros.
    erewrite num_elts_merge; eauto.
    rewrite Nat.pow_add_r; auto.
  repeat rewrite H; auto.
  repeat rewrite Nat.pow_add_r in *. 
  exact (compose_super (compose_super (compose_super (super (Id _)) p2') g') p1').
Defined.



SearchAbout (_ ^ (_ + _)).
(*
Lemma pow_distr : forall (m n p : nat), p ^ (m + n) = ((p ^ m) * (p ^ n))%nat.
Admitted.
*)

Close Scope circ_scope.
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
  - rewrite <- Nat.pow_add_r in ρ.
    apply apply_discard in ρ; [ | exists 0%nat; omega].
    apply IHm.
    simpl in ρ. 
    rewrite <- minus_n_O in ρ.
    rewrite Nat.pow_add_r in ρ.
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
  - exact (super (denote_pat p)).
  - intros ρ.
    exact (denote_circuit _ _ c (apply_gate g p p0 i i0 ρ)).
  - intros ρ.
    rewrite (num_elts_merge ctx1 ctx2) in *; auto.
    set (p' := super (apply_pat_in p ctx2 i)).
    repeat rewrite Nat.pow_add_r in *.
    exact (denote_lift (fun w => denote_circuit _ _ (f w)) (p' ρ)).
Defined.


Instance denote_Flat_Circuit Γ W 
        : Denote (Flat_Circuit Γ W) (Superoperator (2^〚Γ〛) (2^〚W〛)) :=
{|
    correctness := super_op_correctness;
    denote := denote_circuit
|}.
Proof.
  intros C.
  induction C. 
  - simpl. subst. unfold eq_rec_r. simpl.
    admit.
  - subst. simpl. unfold eq_rec_r. simpl.
    intros ρ pf.
    apply IHC.
    admit.
  - subst. simpl. unfold eq_rec_r. simpl. Check Nat.pow_add_r.
    destruct (Nat.pow_add_r (num_elts_o ctx1) (num_elts_o ctx2) 2); simpl.
    unfold super_op_correctness.
    intros ρ mixed.
    admit.
Admitted.
  

Instance denote_Circuit Γ W : Denote (Circuit Γ W) (Superoperator (2^〚Γ〛) (2^〚W〛)) :=
{|
    correctness := super_op_correctness;
    denote := fun c => 〚from_HOAS c〛
|}.
Admitted.

Definition denote_box {W1 W2} (b : Flat_Box W1 W2) 
                      : Superoperator (2^〚W1〛) (2^〚W2〛).
  intros ρ.
  destruct b as [W1 W2 Γ p c].
  set (p' := super ((denote_pat p)†)).
  exact (denote_circuit c (p' ρ)).
Defined.

Instance denote_Flat_Box W1 W2 
        : Denote (Flat_Box W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := super_op_correctness;
    denote := denote_box
|}.
Admitted.


Instance denote_Box W1 W2 
        : Denote (Box W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := super_op_correctness;
    denote := fun b => 〚from_HOAS_Box b〛
|}.
Admitted.


(* Examples *)

Require Import Examples.
Definition Sup := 〚bell00〛. Check Sup.
Definition Mat := (Sup (Id (2 ^ 〚One〛))). Check Mat.
(* M is a 2^4 x 2^4 square *) 
Fixpoint nats_to n : list nat :=
  match n with
  | 0 => [] 
  | S n' => 0%nat :: map S (nats_to n')
  end.
Definition idx := let ls := nats_to 16 in
                  cross_list ls ls.

Close Scope circ_scope.
Definition Mat' := map (fun (x : nat * nat) => match x with (i,j) => Mat{i,j} end) idx.
Open Scope circ_scope.

Eval compute in (Mat{0,0})%nat. (* not computing still :( *)
