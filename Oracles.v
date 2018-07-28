Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Symmetric.
Require Import SemanticLib.

Require Import List.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

(* --------------------------------*)
(* Reversible bexps with variables *)
(* --------------------------------*)

Delimit Scope bexp_scope with bx.
Open Scope bexp_scope.
Open Scope circ_scope.

Inductive bexp := 
| b_t   : bexp
| b_f   : bexp
| b_var : Var -> bexp
| b_not : bexp -> bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp.

Reserved Notation "⌈ b | f ⌉" (at level 0). 

Fixpoint interpret_bexp (b : bexp) (f : Var -> bool) : bool :=
  match b with
  | b_t         => true 
  | b_f         => false 
  | b_var v     => f v 
  | b_not b     => ¬ ⌈ b | f ⌉
  | b_and b1 b2 => ⌈ b1 | f⌉ && ⌈ b2 | f⌉
  | b_xor b1 b2 => ⌈ b1 | f⌉ ⊕ ⌈ b2 | f⌉
  end where "⌈ b | f ⌉" := (interpret_bexp b f).  

Reserved Notation "Γ1 ∪ Γ2" (at level 30).

(* assumes no conflicts - all wires are 'Qubit' *)
Fixpoint classical_merge (Γ1 Γ2 : Ctx) := 
  match Γ1, Γ2 with 
  | []           , _        => Γ2
  | _            , []       => Γ1
  | None :: Γ1'  , o :: Γ2' => o      :: (Γ1' ∪ Γ2') 
  | Some w :: Γ1', _ :: Γ2' => Some w :: (Γ1' ∪ Γ2') 
  end where "Γ1 ∪ Γ2" := (classical_merge Γ1 Γ2).

(* Gets a context for the variables in an bexp *)
Fixpoint get_context (b : bexp) : Ctx :=
  match b with 
  | b_t          => [] 
  | b_f          => []
  | b_var v      => singleton v Qubit 
  | b_not b      => get_context b 
  | b_and b1 b2  => get_context b1 ∪ get_context b2 
  | b_xor b1 b2  => get_context b1 ∪ get_context b2 
  end.

Reserved Notation "Γ1 ⊂ Γ2" (at level 70).

Inductive subset_eq : Ctx -> Ctx -> Set :=
| sub_empty : forall Γ, [] ⊂ Γ
| sub_some  : forall o W Γ1 Γ2, Γ1 ⊂ Γ2 -> o :: Γ1 ⊂ Some W :: Γ2
| sub_none  : forall Γ1 Γ2, Γ1 ⊂ Γ2 -> None :: Γ1 ⊂ None :: Γ2
where "Γ1 ⊂ Γ2" := (subset_eq Γ1 Γ2).

Lemma classical_merge_nil_l : forall Γ, [] ∪ Γ = Γ.
Proof. destruct Γ; trivial. Qed.

Lemma classical_merge_nil_r : forall Γ, Γ ∪ [] = Γ.
Proof. destruct Γ; trivial. simpl. destruct o; easy. Qed.

Lemma subset_classical_merge : forall Γ Γ1 Γ2, Γ1 ∪ Γ2 ⊂ Γ -> (Γ1 ⊂ Γ) * (Γ2 ⊂ Γ).
Proof.
  induction Γ.
  - intros Γ1 Γ2 H.
    destruct Γ1, Γ2. 
    split; constructor.
    inversion H.
    destruct o; inversion H.
    destruct o; inversion H.
  - intros.
    destruct Γ1, Γ2.
    split; constructor.
    simpl in H.
    split; [constructor|easy].
    split; [rewrite classical_merge_nil_r in H; easy | constructor].
    destruct a. 
    destruct (IHΓ Γ1 Γ2); auto.
    simpl in H. destruct o.
    inversion H; subst. easy.
    inversion H; subst. easy.
    split; apply sub_some; easy.
    destruct o, o0; inversion H; subst.
    specialize (IHΓ _ _ H2) as [S1 S2].
    split; apply sub_none; easy.
Qed.

(* Gets the index of v in Γ excluding Nones *)
Fixpoint position_of (v : Var) (Γ : Ctx) : nat := 
  match v with
  | 0     => 0
  | S v'  => match Γ with
            | [] => 0
            | None :: Γ'   => position_of v'  Γ'
            | Some w :: Γ' => S (position_of v' Γ')
            end
  end.

Lemma position_of_lt : forall v Γ W, nth v Γ None = Some W -> (position_of v Γ < ⟦Γ⟧)%nat.
Proof.
  intros v Γ. revert v.
  induction Γ.
  - simpl. destruct v; easy.
  - intros. destruct v.
    + simpl in H. subst. 
      simpl. omega.
    + simpl in *.
      specialize (IHΓ _ _ H). 
      destruct a. omega.
      easy.
Qed.

Lemma singleton_nth_classical : forall Γ v, singleton v Qubit ⊂ Γ ->
                                       exists W, nth v Γ None = Some W.
Proof.
  induction Γ; intros.
  destruct v; inversion H.
  simpl in *.
  destruct v.
  inversion H. 
  eauto. 
  simpl in *.
  apply IHΓ.
  inversion H; subst; easy.
Qed.

(* Retrieves the nth wire in a list *)
(* Will return default if m = 0 or n >= m *)
Fixpoint get_wire {W m} (n : nat) (ps : Pat (m ⨂ W)) (default : Pat W) : Pat W.
destruct m as [|m'].
+ exact default.
+ simpl in ps.
  dependent destruction ps.
  destruct n as [|n']. 
  - exact ps1.
  - exact (get_wire W m' n' ps2 default).
Defined.

Lemma get_wire_WT : forall Γ m n default (p : Pat (m ⨂ Qubit)), 
  (n < m)%nat ->
  Γ ⊢ p :Pat ->
  {Γ1 : OCtx & {Γ2 : OCtx & Γ == Γ1 ∙ Γ2 &
                     Γ1  ⊢ get_wire n p default :Pat}}.
Proof.
  intros Γ m. 
  generalize dependent Γ.
  induction m.
  intros; omega.
  intros Γ n default p H H0.
  dependent destruction p.
  dependent destruction H0.
  destruct n.
  - simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    exists Γ1, Γ2. constructor; trivial. assumption.
  - edestruct (IHm Γ2 n default) as [Γ1' T].    
    omega.
    apply H0_0.
    destruct T as [Γ2' T].
    simpl in t.
    simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    exists Γ1', (Γ1 ⋓ Γ2'). 2: apply t.
    type_check.
Qed.    

(* Replaces the nth wire in a pattern with the given wire *)
Fixpoint replace_wire {W m} (p : Pat W) (n : nat) (ps : Pat (m ⨂ W)) : (Pat (m ⨂ W)).
destruct m as [|m'].
+ exact ps.
+ dependent destruction ps.
    destruct n as [|n'].
  - exact (pair p ps2).
  - exact (pair ps1 (replace_wire W m' p n' ps2)).
Defined.

(* Different approach *)
Fixpoint default_wire (W : WType) : Pat W := 
  match W with
  | One          => unit  
  | Qubit        => qubit 0%nat
  | Bit          => bit 0%nat 
  | Tensor W1 W2 => pair (default_wire W1) (default_wire W2)
  end.

Fixpoint unzip_wires {W m} (n : nat) (ps : Pat (m ⨂ W)) : 
  Pat (n ⨂ W) * Pat W * Pat ((m - n - 1) ⨂ W).  
  destruct m as [|m'].
  - (* failure case *)
    exact (default_wire _ , default_wire _, default_wire _)%core.
  - dependent destruction ps.
    destruct n as [|n']. 
    + simpl.
      rewrite Nat.sub_0_r. 
      exact (unit, ps1, ps2)%core.
    + simpl.
      apply unzip_wires with (n:=n') in ps2.
      destruct ps2 as [[ps1' p] ps2'].
      exact (pair ps1 ps1', p, ps2')%core.                                             
Defined.

Fixpoint zip_wires {W m1 m2} (ps1 : Pat (m1 ⨂ W)) (p: Pat W) (ps2 : Pat (m2 ⨂ W)) :
  Pat ((m1 + m2 + 1) ⨂ W).
destruct m1.
- simpl. rewrite Nat.add_1_r. apply (pair p ps2).
- simpl. 
  dependent destruction ps1.
  specialize (zip_wires _ _ _ ps1_2 p ps2).
  exact (pair ps1_1 zip_wires).
Defined.

Notation "'Square_Box' W" := (Box W W) (at level 100).

(* Shares the kth of n qubits to the (last) target qubit *)
(* Returns the identity circuit if k > n *)
Fixpoint share_to (n k : nat) : Square_Box ((n ⨂ Qubit) ⊗ Qubit) := 
  match n with 
  | 0 => id_circ (* error: n < k *)
  | S n' => match k with
           | 0    => box_ qqst ⇒
                    let_ ((q,qs),t) ← output qqst;
                    let_ (q,t)     ← CNOT $ (q,t);
                    ((q,qs),t)
           | S k' => box_ qqst ⇒
                    let_ ((q,qs),t) ← output qqst;
                    let_ (qs,t) ← share_to n' k' $ (qs,t);
                    ((q,qs),t)
           end
  end.

(* Morally this circuit:
Fixpoint share_to (n k : nat) : Square_Box (S n ⨂ Qubit) ⊗ Qubit := 
  match n with 
  | 0 => id_circ (* error: n < k *)
  | S n' => match k with
           | 0    => box_ qqst ⇒
                     let_ ((q,qs),t) ← output qqst;
                     gate_ (q,t)     ← CNOT @(q,t);
                     output ((q,qs),t)
           | S k' => (@id_circ Qubit) ∥ (share_to' n' k')
           end
  end.
*)

Lemma share_to_WT : forall n k, Typed_Box (share_to n k).
Proof. induction n; type_check. destruct k; type_check. apply IHn; type_check. Qed.

(* First qubit is target *)
Fixpoint share_to' (n k : nat) : Square_Box ((S n ⨂ Qubit)) := 
  match n with 
  | 0 => id_circ (* error: n < k *)
  | S n' => match k with
           | 0    => box_ qqst ⇒
                    let_ (t,(q,qs)) ← qqst;
                    let_ (q,t)     ← CNOT $ (q,t);
                    (t,(q,qs))
           | S k' => box_ qqst ⇒
                    let_ (t,(q,qs)) ← qqst;
                    let_ (t,qs) ← share_to' n' k' $ (t,qs);
                    (t,(q,qs))
           end
  end.

Lemma share_to_WT' : forall n k, Typed_Box (share_to' n k).
Proof. induction n; type_check. destruct k; type_check. apply IHn; type_check. Qed.



Lemma size_repeat_ctx : forall n W, size_ctx (repeat (Some W) n) = n.
Proof.
  induction n; trivial.
  intros; simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma ctx_dom_repeat : forall n, ctx_dom (repeat (Some Qubit) n) = seq 0 n.
Proof.      
  induction n; trivial.
  simpl.
  rewrite IHn.
  rewrite seq_shift.
  reflexivity.
Qed.

Fixpoint pat_max {W} (p : Pat W) : nat := 
  match p with
  | () => 0
  | qubit v => v 
  | bit v   => v 
  | pair p1 p2 => Nat.max (pat_max p1) (pat_max p2)
  end.

(* For DBCircuits *)

Lemma maps_to_repeat : forall v n W, v < n ->
                                maps_to v (repeat (Some W) n) = Some v.
Proof.
  induction v; intros n W L; auto.
  - destruct n; try omega. easy.
  - destruct n; try omega.
    simpl. rewrite IHv by omega. easy.
Qed.
  
(* Does it make sense to have a shifted version of this too? *)
Lemma subst_pat_σ_n: forall W W' n (p : Pat W), (pat_max p < n)%nat -> 
                                           subst_pat (repeat (Some W') n) p = p.
Proof.
  intros.
  gen W'.
  induction p; intros W'.
  - simpl; reflexivity.
  - simpl in *.
    unfold subst_var.
    rewrite maps_to_repeat; easy.
  - simpl in *.
    unfold subst_var.
    rewrite maps_to_repeat; easy.
  - simpl in *.
    apply Nat.max_lub_lt_iff in H as [L1 L2].
    rewrite IHp1, IHp2; easy. 
Qed.

(* We'll see if we need this
Lemma ntensor_pat_to_list_shifted : forall (m n o : nat),
  (m + n < o)%nat ->
  pat_to_list (subst_pat (repeat (Some Qubit) n) (add_fresh_pat (n ⨂ Qubit) 
                                 (repeat (Some Qubit) m ))) = seq m n. 
Proof.
  intros m n. revert m.
  induction n; trivial.
  intros.
  rewrite subst_pat_σ_n.
  simpl.
  rewrite repeat_length.
  rewrite subst_var_σ_n by omega.
  replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
  rewrite repeat_combine.
  rewrite IHn by omega.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.
*)

Lemma pat_max_fresh : forall m n, 
    (pat_max (add_fresh_pat (n ⨂ Qubit) (repeat (Some Qubit) m)) < S (m + n))%nat.
Proof.
  intros. 
  generalize dependent m.
  induction n.
  - intros; simpl; omega.
  - intros.
    simpl.    
    unfold add_fresh_pat; simpl.
    rewrite add_fresh_split; simpl.
    apply Nat.max_lub_lt. 
    rewrite repeat_length. omega.
    rewrite (repeat_combine (option WType) m 1%nat). 
    specialize (IHn (m + 1)).
    omega.
Qed.      

(* Also true, does this come up?
Lemma pat_max_fresh : forall m n, 
    (pat_max (fresh_pat (NTensor n Qubit) (σ_{ m}) ) < S (m + n))%nat.
Proof.
  intros. 
  generalize dependent m.
  induction n.
  - intros; simpl; omega.
  - intros.
    simpl.
    rewrite seq_length.
    apply Nat.max_lub_lt. omega.
    simpl. 
    rewrite <- seq_S.
    specialize (IHn (S m)). 
    omega.
Qed.      
*)

Open Scope matrix_scope.

Lemma singleton_repeat : forall n W, singleton n W = repeat None n ++ repeat (Some W) 1%nat.
Proof.
  induction n; intros W; trivial. 
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma ctx_dom_none_repeat : forall m n, 
  ctx_dom (repeat None m ++ repeat (Some Qubit) n) = seq m n.
Proof. 
  induction m; intros n.
  - simpl. apply ctx_dom_repeat.
  - simpl. rewrite IHm. apply fmap_S_seq. 
Qed.

Lemma size_repeat_none : forall (n : nat), size_ctx (repeat None n) = 0%nat.
Proof. induction n; trivial. Qed.

Lemma types_pat_fresh_ntensor : forall (Γ : Ctx) (n : nat), n <> 0%nat ->
Valid (repeat None (length Γ) ++ repeat (Some Qubit) n) ⊢ 
      add_fresh_pat (n ⨂ Qubit)%qc Γ :Pat.
Proof.
  intros Γ n nz. revert Γ.
  induction n; intros Γ.
  - simpl. contradiction. 
  - destruct n. 
    + simpl. clear.
      econstructor.
      4: type_check.
      3: type_check.
      validate.
      rewrite merge_nil_r.
      reflexivity.
      simpl_rewrite' (singleton_repeat (length Γ)). 
      apply singleton_singleton.
    + remember (S n) as n'.
      simpl.
      unfold add_fresh_pat; simpl.
      rewrite add_fresh_split; simpl.
      econstructor.
      validate.
      2: constructor; apply singleton_singleton.
      2: apply IHn; omega.
      rewrite singleton_repeat.
      rewrite app_length. simpl.
      rewrite <- repeat_combine.
      rewrite <- app_assoc.
      erewrite merge_offset.
      reflexivity.
      unlock_merge.
      reflexivity.
Qed.

(* This proof needs updating for in_place unitary application (if we want this proof):
Proposition share_to_spec : forall (t b : bool) (k n : nat) (l1 l2 : list (Square 2)),
  (k < n)%nat ->
  length l1 = k ->
  length l2 = (n - k - 1)%nat ->
  (forall i, WF_Matrix 2 2 (nth i l1 (Zero 2%nat 2%nat))) ->
  (forall i, WF_Matrix 2 2 (nth i l2 (Zero 2%nat 2%nat))) ->
  ⟦share_to n k⟧  ((⨂ l1)  ⊗ bool_to_matrix b ⊗ (⨂ l2) ⊗ bool_to_matrix t) =  
 (⨂ l1) ⊗ (bool_to_matrix b) ⊗ (⨂ l2) ⊗ bool_to_matrix (xorb t b).
Proof.
  intros t b k n.
  generalize dependent k.
  induction n as [|n' IH]; [intros; omega|]. 
  intros k l1 l2 Lt L1 L2 WF1 WF2.
  destruct k.
  - clear IH.
    simpl in *.
    rewrite Nat.sub_0_r in L2. clear Lt.
    destruct l1. 2: simpl in L1; omega. clear L1.
    simpl. Msimpl. 
    unfold denote_box.
    simpl.
    rewrite Nat.add_1_r.
    unfold compose_super.
    simpl.
    unfold add_fresh_state; simpl.
    unfold get_fresh_var; simpl.

(* Show that padding and subst_var are the identity *)
    rewrite fresh_state_ntensor. 
    remember (repeat (Some Qubit) (S (S n'))) as Qubits.
    replace (([Some Qubit] ++ repeat (Some Qubit) n') ++ [Some Qubit])%core with 
        Qubits.
    Focus 2.
      subst. clear.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1%nat) by reflexivity.
      repeat rewrite repeat_combine.
      rewrite Nat.add_1_r. reflexivity.
        
    simpl.
    rewrite repeat_length.
    unfold denote_pat.
    replace (pat_to_list _) with (σ_{S (S n')}).
    Focus 2.
      rewrite HeqQubits. clear.
      induction n'.
      reflexivity.
      rewrite seq_S.
      rewrite IHn'.
      simpl.
      unfold add_fresh_state; simpl.
      unfold get_fresh_var; simpl.
      rewrite ctx_dom_repeat.      
      repeat rewrite seq_shift.      
      replace (0%nat :: 1%nat :: 2%nat :: seq 3 n') with (σ_{3+n'}) by reflexivity.
      replace (0%nat :: 1%nat :: seq 2 n') with (σ_{2+n'}) by reflexivity.
      repeat rewrite subst_var_σ_n by omega.
      replace ([Some Qubit; Some Qubit]) with (repeat (Some Qubit) 2) by reflexivity.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite ntensor_pat_to_list_shifted by omega.
      rewrite ntensor_pat_to_list_shifted by omega.
      rewrite <- seq_S. simpl. reflexivity.

    simpl.
    rewrite size_ntensor. simpl.

*)

(* Can probably use an existing list function *)
Fixpoint qubit_at (v : Var) (Γ : Ctx) := 
  match Γ with
  | [] => false 
  | W :: Γ' => match v with
              | 0 => match W with 
                    | Some Qubit => true
                    | _          => false
                    end
              | S v' => qubit_at v' Γ' 
              end
  end.

Lemma qubit_at_reflect : forall v Γ, qubit_at v Γ = true <-> nth v Γ None = Some Qubit. 
Proof.
  induction v.
  - intros. simpl. 
    destruct Γ. easy.
    destruct o. destruct w; easy. 
    easy.
  - intros. simpl.
    destruct Γ. easy.
    simpl. apply IHv.
Qed.

(* Without init_at, assert_at
Fixpoint compile (b : bexp) (Γ : Ctx) : Square_Box (S (⟦Γ⟧) ⨂ Qubit) :=
  match b with
  | b_t          => TRUE ∥ id_circ 
  | b_f          => FALSE ∥ id_circ
  | b_var v      => 
    (* share_to' (⟦Γ⟧) (position_of v Γ) *)
    (* CNOT_at_option (S (⟦Γ⟧)) (position_of v Γ) (⟦Γ⟧) *)
    CNOT_at (S (⟦Γ⟧)) (S (position_of v Γ)) 0
  | b_not b      =>  (id_circ ∥ (strip_one_l_in (init1 ∥ id_circ))) ;;
                     (id_circ ∥ (compile b Γ)) ;;
                     (CNOT_at (2 + ⟦Γ⟧) 1 0)    ;;
                     (id_circ ∥ (compile b Γ)) ;;
                     (id_circ ∥ (strip_one_l_out (assert1 ∥ id_circ)))
  | b_and b1 b2  => (id_circ ∥ (strip_one_l_in (init0 ∥ id_circ))) ;;
                     (id_circ ∥ compile b1 Γ) ;;
                     (id_circ ∥ (id_circ ∥ (strip_one_l_in (init0 ∥ id_circ)))) ;;
                     (id_circ ∥ (id_circ ∥ compile b2 Γ)) ;;
                     (Toffoli_at (3 + ⟦Γ⟧) 1 2 0)           ;;
                     (id_circ ∥ (id_circ ∥ compile b2 Γ)) ;;
                     (id_circ ∥ (id_circ ∥ (strip_one_l_out (assert0 ∥ id_circ)))) ;;
                     (id_circ ∥ compile b1 Γ) ;;
                     (id_circ ∥ (strip_one_l_out (assert0 ∥ id_circ)))                
  | b_xor b1 b2  => (id_circ ∥ (strip_one_l_in (init0 ∥ id_circ))) ;;
                     (id_circ ∥ compile b1 Γ) ;;
                     (CNOT_at (2 + ⟦Γ⟧) 1 0)   ;;                    
                     (id_circ ∥ compile b1 Γ) ;; 
                     (id_circ ∥ compile b2 Γ) ;; (* reusing ancilla *)
                     (CNOT_at (2 + ⟦Γ⟧) 1 0)   ;;                    
                     (id_circ ∥ compile b2 Γ) ;;
                     (id_circ ∥ (strip_one_l_out (assert0 ∥ id_circ)))              
  end. *)

Open Scope circ_scope.
Fixpoint compile (b : bexp) (Γ : Ctx) : Square_Box (S (⟦Γ⟧) ⨂ Qubit) :=
  match b with
  | b_t          => TRUE ∥ id_circ 
  | b_f          => FALSE ∥ id_circ
  | b_var v      => CNOT_at (1 + ⟦Γ⟧) (1 + position_of v Γ) 0
  | b_not b      => init_at true (1 + ⟦Γ⟧) 1 ;;
                   id_circ ∥ (compile b Γ)  ;;
                   CNOT_at (2 + ⟦Γ⟧) 1 0    ;;
                   id_circ ∥ (compile b Γ)  ;;
                   assert_at true (1+⟦Γ⟧) 1 
  | b_and b1 b2  => init_at false (1 + ⟦Γ⟧) 1        ;;
                   id_circ ∥ compile b1 Γ           ;;
                   init_at false (2 + ⟦Γ⟧) 2        ;;
                   id_circ ∥ id_circ ∥ compile b2 Γ ;;
                   Toffoli_at (3 + ⟦Γ⟧) 1 2 0       ;;
                   id_circ ∥ id_circ ∥ compile b2 Γ ;;
                   assert_at false (2 + ⟦Γ⟧) 2      ;;
                   id_circ ∥ compile b1 Γ           ;;
                   assert_at false (1 + ⟦Γ⟧) 1 
  | b_xor b1 b2  => init_at false (1 + ⟦Γ⟧) 1 ;;
                   id_circ ∥ compile b1 Γ    ;;
                   CNOT_at (2 + ⟦Γ⟧) 1 0     ;;                    
                   id_circ ∥ compile b1 Γ    ;; 
                   id_circ ∥ compile b2 Γ    ;; (* reusing ancilla *)
                   CNOT_at (2 + ⟦Γ⟧) 1 0     ;;                    
                   id_circ ∥ compile b2 Γ    ;;
                   assert_at false (1 + ⟦Γ⟧) 1
  end.

Lemma ntensor_fold : forall n W, W ⊗ (n ⨂ W) = (S n ⨂ W).
Proof. reflexivity. Qed.

(* Because 'auto' sucks *)
Ltac compile_typing lem := 
  repeat match goal with
  | _ => apply inSeq_WT
  | _ => apply inPar_WT
  | _ => apply id_circ_WT
  | _ => apply boxed_gate_WT
  | [|- Typed_Box (CNOT_at ?n ?x ?y)] => 
      specialize (CNOT_at_WT n x y); simpl; easy
  | [|- Typed_Box (Toffoli_at ?n ?x ?y ?z )] => 
      specialize (Toffoli_at_WT n x y z); simpl; easy
  | _ => apply share_to_WT'
  | _ => apply TRUE_WT
  | _ => apply FALSE_WT
  | _ => apply strip_one_l_in_WT
  | _ => apply strip_one_l_out_WT
  | _ => apply strip_one_r_in_WT
  | _ => apply strip_one_r_out_WT
  | [H : forall (Γ : Ctx), Typed_Box _ |- _]  => apply H
  | _ => apply lem 
  end.

Lemma compile_WT : forall (b : bexp) (Γ : Ctx), Typed_Box (compile b Γ).
Proof. induction b; intros; simpl; compile_typing True. Qed.

Hint Resolve compile_WT : typed_db.

Open Scope matrix_scope.

Fixpoint ctx_to_mat_list (Γ : Ctx) (f : Var -> bool) {struct Γ} : list (Matrix 2 2) :=
  match Γ with 
  | [] => []
  | None :: Γ' => ctx_to_mat_list Γ' (fun v => f (S v))
  | Some W :: Γ' => bool_to_matrix (f O) :: ctx_to_mat_list Γ' (fun v => f (S v))
  end.

Definition ctx_to_matrix (Γ : Ctx) (f : Var -> bool) : Square (2^⟦Γ⟧) :=
  big_kron (ctx_to_mat_list Γ f).

Lemma ctx_to_mat_list_length : forall Γ f, length (ctx_to_mat_list Γ f) = ⟦Γ⟧.
Proof.
  induction Γ; intros f; trivial.
  simpl. destruct a; simpl; rewrite IHΓ; easy.
Qed.

Lemma WF_ctx_to_matrix : forall Γ f, WF_Matrix (2^⟦Γ⟧) (2^⟦Γ⟧) (ctx_to_matrix Γ f).
Proof.
  induction Γ; intros f.
  - auto with wf_db.
  - destruct a; simpl. 
    unfold ctx_to_matrix. 
    apply WF_kron. unify_pows_two. 
    rewrite ctx_to_mat_list_length. simpl; omega.
    rewrite ctx_to_mat_list_length. simpl; omega.
    apply WF_bool_to_matrix.
    rewrite ctx_to_mat_list_length. apply IHΓ.
    unfold ctx_to_matrix.
    simpl. 
    apply IHΓ.
Qed.

Lemma WF_ctx_to_mat_list : forall Γ f, WF_Matrix (2^⟦Γ⟧) (2^⟦Γ⟧) (big_kron (ctx_to_mat_list Γ f)).
Proof. apply WF_ctx_to_matrix. Qed.

Hint Resolve WF_ctx_to_matrix WF_ctx_to_mat_list : wf_db.

Lemma pure_bool_to_matrix : forall b, Pure_State (bool_to_matrix b).
Proof. destruct b. apply pure1. apply pure0. Qed.

Search big_kron.

(* Belongs in Quantum.v *)
Lemma pure_big_kron : forall (n : nat) (l : list (Square n)) (A : Square n),
  (forall i : nat, Pure_State (nth i l A)) -> 
  Pure_State (⨂ l).
Proof.
  induction l;  intros A H.
  - simpl. apply pure_id1.
  - simpl. apply pure_state_kron. apply (H 0).
    apply (IHl A).    
    intros i.
    apply (H (S i)).
Qed.

Lemma mixed_big_kron : forall (n : nat) (l : list (Square n)) (A : Square n),
(forall i : nat, Mixed_State (nth i l A)) -> Mixed_State (⨂ l).
Proof.
  induction l;  intros A H.
  - simpl. constructor. apply pure_id1.
  - simpl. apply mixed_state_kron. apply (H 0).
    eapply IHl.
    intros i.
    apply (H (S i)).
Qed.

Lemma big_kron_append : forall m n (l1 l2 : list (Matrix m n)) (A B : Matrix m n), 
  (forall j, WF_Matrix m n (nth j l1 A)) ->
  (forall j, WF_Matrix m n (nth j l2 B)) ->
  ⨂ (l1 ++ l2) = (⨂ l1) ⊗ (⨂ l2). 
Proof.
  induction l1.
  - intros. simpl. rewrite kron_1_l. reflexivity. eapply WF_big_kron.  
    intros i. apply (H0 i).
  - intros. simpl. 
    erewrite IHl1; auto. 
    rewrite kron_assoc. 
    show_dimensions.
    rewrite app_length.
    rewrite 2 Nat.pow_add_r.
    reflexivity.
    intros j. apply (H (S j)).
Qed.

Lemma pure_ctx_to_matrix : forall Γ f, Pure_State (ctx_to_matrix Γ f).
Proof.
  intros.
  unfold ctx_to_matrix.
  specialize (pure_big_kron 2) as PBK.
  rewrite <- (ctx_to_mat_list_length Γ f).
  eapply PBK.
  clear.
  revert f.
  induction Γ.
  intros f [|i]. simpl. apply pure0.
  simpl. apply pure0.
  destruct i,a; simpl; [apply pure_bool_to_matrix| | |]; apply IHΓ.
Qed.

(*
Fixpoint ctx_to_matrix (Γ : Ctx) (f : Var -> bool) {struct Γ} : Square (2^⟦Γ⟧) :=
  match Γ with 
  | [] => 'I_1
  | None :: Γ' => ctx_to_matrix Γ' (fun v => f (S v))
  | Some W :: Γ' => bool_to_matrix (f O) ⊗ ctx_to_matrix Γ' (fun v => f (S v))
  end.
Proposition WF_ctx_to_matrix : forall Γ f, WF_Matrix (2^⟦Γ⟧) (2^⟦Γ⟧) (ctx_to_matrix Γ f).
Proof.
  induction Γ; intros f.
  - auto with wf_db.
  - destruct a; simpl; auto with wf_db. 
Abort.
Hint Resolve WF_ctx_to_matrix : wf_db.
*)

(*
Eval simpl in (ctx_to_matrix [Some Qubit; None; None; Some Qubit; Some Qubit] 
               (fun v => if v =? 3 then true else false)).
Eval simpl in (ctx_to_matrix [Some Qubit; None; None; Some Qubit; Some Qubit] 
               (fun v => if v =? 2 then true else false)).
*)

Lemma is_valid_singleton_merge : forall W (Γ : Ctx) n, (length Γ <= n)%nat ->
                                                  is_valid (Γ ⋓ singleton n W).
Proof.
  induction Γ; intros.
  - unlock_merge. simpl. apply valid_valid. 
  - destruct n. simpl in H; omega.
    unlock_merge. simpl.
    simpl in H. 
    destruct IHΓ with (n := n). omega.
    rewrite H0.
    destruct a; simpl; apply valid_valid.
Qed.

Lemma size_ctx_app : forall (Γ1 Γ2 : Ctx), 
          size_ctx (Γ1 ++ Γ2) = (size_ctx Γ1 + size_ctx Γ2)%nat.
Proof.
  induction Γ1; trivial.
  intros.
  simpl.
  rewrite IHΓ1.
  destruct a; reflexivity.
Qed.

Lemma singleton_length : forall n W, length (singleton n W) = (n + 1)%nat.
Proof.
  induction n; trivial. 
  intros W. simpl. rewrite IHn. reflexivity.
Qed.

Ltac dim_solve := unify_pows_two; simpl; try rewrite size_ntensor; 
                  simpl; try rewrite Nat.mul_1_r; omega.

(* Ltac dim_solve := unify_pows_two; simpl; omega. *)

Ltac unify_dim_solve := 
  match goal with 
  | [|- @kron ?m ?n ?o ?p ?A ?B = @kron ?m' ?n' ?o' ?p' ?A' ?B'] =>
     replace A with A' by unify_dim_solve;
     replace B with B' by unify_dim_solve;
     replace m with m' by dim_solve;
     replace n with n' by dim_solve;
     replace o with o' by dim_solve;
     replace p with p' by dim_solve;
     reflexivity
  | [|- _ = _] => reflexivity
  end.

Ltac show_pure := 
  repeat match goal with
  | [|- Pure_State (⨂ ctx_to_mat_list ?Γ ?f)] =>
    replace (⨂ ctx_to_mat_list Γ f) with (ctx_to_matrix Γ f) by easy
  | [|- @Pure_State ?W (ctx_to_matrix ?Γ ?f) ] => 
    let H := fresh "H" in 
    specialize (pure_ctx_to_matrix Γ f) as H;
    match type of H with
    | @Pure_State ?W' (ctx_to_matrix ?Γ ?f) =>
      replace W with W' by dim_solve;
      apply H
    end; clear H
  | [|- @Pure_State ?W (@kron ?a ?b ?c ?d ?A ?B) ] => 
    let H := fresh "H" in 
    specialize (pure_state_kron a c A B) as H;
    match type of H with
    | ?H1 -> ?H2 -> @Pure_State ?W' (@kron ?a' ?b' ?c' ?d' ?A ?B) => 
        replace W with W' by dim_solve;
        replace a with a' by dim_solve; 
        replace b with b' by dim_solve;
        replace c with c' by dim_solve;
        replace d with d' by dim_solve;
        apply H
    end; clear H
  | _ => apply pure_bool_to_matrix
  | _ => apply pure0
  | _ => apply pure1
  | _ => apply pure_id1
  end.

Ltac show_mixed := 
  repeat match goal with
    [|- @Mixed_State ?W (@denote_box true ?W1 ?W2 ?c ?ρ) ] => 
    let H := fresh "H" in
    let T := fresh "T" in
    specialize (@denote_box_correct W1 W2 c) as H;
    unfold WF_Superoperator in H;
    assert (T : Typed_Box c) by (compile_typing (compile_WT); type_check);
    specialize (H T ρ);
    simpl in H;
    match type of H with
    | _ -> @Mixed_State ?W' (denote_box true ?c' ?ρ') => 
      replace ρ with ρ' by easy;
      replace W with W' by dim_solve;
      try apply H
    end;
    clear H; clear T
  end; try solve [apply Pure_S; show_pure].

Hint Extern 2 (Mixed_State _) => show_mixed : wf_db. 

Ltac rewrite_inPar := 
  match goal with
  [|- context[(@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
    (@kron ?m ?n ?o ?p ?ρ1 ?ρ2)]] =>
    let IP := fresh "IP" in 
    specialize (inPar_correct W1 W1' W2 W2' f g true ρ1 ρ2) as IP;
    simpl in IP; 
    try rewrite ctx_to_mat_list_length in *;
    try rewrite size_ntensor in IP; 
    try rewrite Nat.mul_1_r in IP;
    try fold NTensor in *;
    simpl in *;
    rewrite IP;
    clear IP
  end; try solve [type_check]; eauto with wf_db. 

(* compile_typing (compile_WT); show_mixed. *)

(* Designated successor to rewrite_inPar *)
Ltac rewrite_inPar' := 
  fold NTensor; (* This shouldn't be necessary but is? *)
  simpl in *; 
  match goal with
  [|- context[(@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
    (@kron ?m ?n ?o ?p ?ρ1 ?ρ2)]] =>
    let IP := fresh "IP" in 
    specialize (inPar_correct W1 W1' W2 W2' f g ρ1 ρ2) as IP;
    simpl in *;
    match goal with
    | [H : ?A -> ?B -> ?C -> ?D -> 
           (@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
           (@kron ?m' ?n' ?o' ?p' ?ρ1 ?ρ2) = ?RHS |- _] => 
      replace m with m'; try dim_solve;
      replace n with n'; try dim_solve;
      replace o with o'; try dim_solve;
      replace p with p'; try dim_solve;
      try rewrite H
     end;
     clear IP
  end; try solve [type_check]; eauto with wf_db. 

Ltac listify_kron := 
    unfold ctx_to_matrix;
    repeat match goal with
    | [|- context[@kron ?a ?b ?c ?d ?A (⨂ ?li)]] =>
       replace (@kron a b c d A (⨂ li)) with
           (⨂ (A :: li)) by 
          (simpl; Msimpl; rewrite ctx_to_mat_list_length; 
           try rewrite size_ntensor, Nat.mul_1_r; easy)
    end.

Lemma ctx_lookup_exists : forall v Γ f, get_context (b_var v) ⊂ Γ -> 
  ctx_to_mat_list Γ f !! position_of v Γ = Some (bool_to_matrix (f v)).  
Proof.             
  induction v; intros Γ f H.
  - destruct Γ. inversion H.
    destruct o. simpl. reflexivity.
    inversion H.
  - destruct Γ.
    simpl. inversion H.
    simpl.
    destruct o.
    simpl.
    apply IHv.
    simpl in H. inversion H. subst. simpl. easy.
    apply IHv.
    simpl in H. inversion H. subst. simpl. easy.
Qed.

(* Specifications for components of compile *)

(* very similar to share_to_spec *)
Fact CNOT_at_spec : forall (b1 b2 : bool) (n x y : nat) (li : list (Matrix 2 2)), 
  x < n -> y < n -> x <> y ->
  nth_error li x = Some (bool_to_matrix b1) ->
  nth_error li y = Some (bool_to_matrix b2) ->
  ⟦CNOT_at n x y⟧ (⨂ li) = ⨂ (update_at li y (bool_to_matrix (b1 ⊕ b2))).
Admitted.

Fact Toffoli_at_spec : forall (b1 b2 b3 : bool) (n x y z : nat) (li : list (Matrix 2 2)),
  x < n -> y < n -> z < n -> x <> y -> x <> z -> y <> z -> 
  nth_error li x = Some (bool_to_matrix b1) ->
  nth_error li y = Some (bool_to_matrix b2) ->
  nth_error li z = Some (bool_to_matrix b3) ->
 ⟦Toffoli_at n x y z⟧ (⨂ li) = ⨂ (update_at li z (bool_to_matrix ((b1 && b2) ⊕ b3))).
Admitted.

Lemma init_at_spec : forall (b : bool) (n i : nat) (l1 l2 : list (Square 2)) (A B : Square 2), 
  length l1 = i ->
  length l2 = n - i ->
  (forall j, Mixed_State (nth j l1 A)) ->
  (forall j, Mixed_State (nth j l2 B)) ->
  i < S n -> 
  ⟦init_at b n i⟧ (⨂ (l1 ++ l2)) = ⨂ (l1 ++ [bool_to_matrix b] ++ l2).
Proof.
  intros b n i. gen n.
  induction i.
  - intros n l1 l2 A B L1 L2 M1 M2 Lt.
    destruct l1; inversion L1.
    simpl in *. clear L1 M1 Lt.
    rewrite strip_one_l_in_eq.
    rewrite <- (kron_1_l _ _ (⨂ l2)) at 1; auto with wf_db. 
    rewrite Nat.sub_0_r in L2. rewrite L2 in *.
    rewrite_inPar. 
    simpl_rewrite id_circ_spec.
    simpl_rewrite init_spec.
    easy.
    subst.
    rewrite size_ntensor. simpl. rewrite Nat.mul_1_r. 
    assert(WF2 : forall j, WF_Matrix 2 2 (nth j l2 B)).
      intros j. apply WF_Mixed. apply M2.
    eapply WF_big_kron. 
    apply WF2.
    specialize (mixed_big_kron 2 l2 B M2) as M2'. 
    rewrite L2 in M2'.    
    apply WF_Mixed.
    apply M2'.
    eapply WF_big_kron.
    intros i. apply WF_Mixed. apply (M2 i).
  - intros n l1 l2 A B L1 L2 M1 M2 Lt.
    destruct n; [omega|].
    destruct l1; inversion L1.
    simpl.
    show_dimensions.
    repeat rewrite app_length. simpl. 
    replace (length l1 + length l2) with n by omega.
    rewrite H0, L2. simpl.
    hide_dimensions.
    rewrite_inPar.
    simpl_rewrite id_circ_spec.
    erewrite IHi; trivial.
    unify_dim_solve.
    intros j.
    apply (M1 (S j)).
    omega.
    simpl.
    apply WF_Mixed. apply (M1 0).
    apply WF_Mixed. apply (M1 0).
    specialize (mixed_state_kron) as M.
    specialize (M _ _ (@big_kron (S (S O)) (S (S O)) l1) 
                      (@big_kron (S (S O)) (S (S O)) l2)).
    rewrite <- Nat.pow_add_r in M.
    replace (length l1 + length l2) with n in M by omega.
    apply WF_Mixed.
    Search big_kron app.
    erewrite big_kron_append.
    apply M.
    eapply mixed_big_kron. intros j. apply (M1 (S j)).
    eapply mixed_big_kron. intros j. apply (M2 j). 
    intros j. apply WF_Mixed. apply (M1 (S j)). 
    intros j. apply WF_Mixed. apply (M2 j). 
Qed.    

(* Currently simplifies all init_at and assert_ats. 
   Proof could be simplified by making these opaque and using lemmas *)
Theorem compile_correct : forall (b : bexp) (Γ : Ctx) (f : Var -> bool) (t : bool),
  get_context b ⊂ Γ -> 
  ⟦compile b Γ⟧ ((bool_to_matrix t) ⊗ (ctx_to_matrix Γ f)) = 
  bool_to_matrix (t ⊕ ⌈b | f⌉) ⊗ ctx_to_matrix Γ f.
Proof.
  intros b.
  induction b; intros Γ f t H.
  - simpl.
    rewrite_inPar.    
    simpl_rewrite TRUE_spec.
    simpl_rewrite id_circ_spec.
    easy.
    rewrite size_ntensor, Nat.mul_1_r.
    apply WF_ctx_to_matrix.
  - simpl. 
    rewrite_inPar.
    simpl_rewrite FALSE_spec.
    simpl_rewrite id_circ_spec.
    easy. 
    rewrite size_ntensor, Nat.mul_1_r.
    apply WF_ctx_to_matrix.
  - simpl. 
    listify_kron.
    simpl_rewrite (CNOT_at_spec (f v) t (S (⟦Γ⟧)) (S (position_of v Γ)) 0); trivial;
      try omega.
    simpl.
    rewrite xorb_comm.
    reflexivity.
    apply (singleton_nth_classical Γ v) in H as [W H].
    apply position_of_lt in H.
    simpl in *; omega.
    apply ctx_lookup_exists; easy.
  - simpl in *.
    specialize inSeq_correct as IS. simpl in IS.    
    repeat (rewrite IS; compile_typing (compile_WT)).
    unfold compose_super.
    rewrite_inPar.    
    rewrite_inPar. 
    rewrite strip_one_l_in_eq.
    rewrite <- (kron_1_l _ _ (ctx_to_matrix Γ f)); auto with wf_db.
    rewrite_inPar.
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    simpl_rewrite init1_spec.
    replace (|1⟩⟨1|) with (bool_to_matrix true) by reflexivity.    
    rewrite (IHb Γ f true H). rewrite xorb_true_l. (* yay! *)
    listify_kron.
    simpl_rewrite (CNOT_at_spec (¬ ⌈b | f⌉) t (S (S (⟦Γ⟧))) 1 0); trivial; try omega. 
    simpl.
    rewrite_inPar.
    unfold ctx_to_matrix in *.
    rewrite IHb; trivial.
    simpl_rewrite id_circ_spec; auto with wf_db.
    rewrite_inPar.     
    simpl_rewrite id_circ_spec; auto with wf_db.
    rewrite strip_one_l_out_eq.
    rewrite xorb_nb_b. 
    rewrite_inPar.     
    simpl_rewrite assert1_spec; auto with wf_db.
    simpl_rewrite id_circ_spec; auto with wf_db.    
    rewrite xorb_comm.
    reflexivity.
  - simpl in *.
    specialize inSeq_correct as IS. simpl in IS.    
    repeat (rewrite IS; compile_typing (compile_WT)). clear IS.
    unfold compose_super.
    repeat rewrite_inPar.    
    repeat rewrite strip_one_l_in_eq.
    replace (ctx_to_matrix Γ f) with (Id 1 ⊗ ctx_to_matrix Γ f) by
        (Msimpl; easy).
    rewrite_inPar.    
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    simpl_rewrite init0_spec.
    apply subset_classical_merge in H as [S1 S2].
    simpl_rewrite (IHb1 Γ f false); trivial.
    replace (if ⌈b1 | f⌉ then true else false) with (⌈b1 | f⌉) by
        (destruct (⌈b1 | f⌉); easy).  
    rewrite_inPar.
    repeat rewrite strip_one_l_in_eq.
    replace (ctx_to_matrix Γ f) with (Id 1 ⊗ ctx_to_matrix Γ f) by
        (Msimpl; easy).
    rewrite_inPar.
    rewrite_inPar.
    simpl_rewrite init0_spec.
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    replace (|0⟩⟨0|) with (bool_to_matrix false) by reflexivity.
    simpl_rewrite IHb2; trivial.
    rewrite xorb_false_l.
    listify_kron.
    simpl_rewrite (Toffoli_at_spec (⌈b1 | f⌉) (⌈b2 | f⌉) t (3 + ⟦Γ⟧) 1 2 0); trivial;
      try omega.
    simpl.
    repeat rewrite_inPar.
    replace (@big_kron (S (S O)) (S (S O)) (ctx_to_mat_list Γ f)) with
        (ctx_to_matrix Γ f) by easy.
    simpl_rewrite IHb2; trivial.
    repeat simpl_rewrite strip_one_l_out_eq.
    rewrite_inPar.
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    rewrite xorb_nilpotent.
    replace (bool_to_matrix false) with (|0⟩⟨0|) by easy.
    simpl_rewrite assert0_spec.
    Msimpl.
    simpl_rewrite IHb1; trivial.
    rewrite_inPar.
    rewrite xorb_nilpotent.
    replace (bool_to_matrix false) with (|0⟩⟨0|) by easy.
    simpl_rewrite assert0_spec.
    simpl_rewrite id_circ_spec; auto with wf_db.
    Msimpl.
    rewrite xorb_comm.
    reflexivity.
  - simpl in *.
    specialize inSeq_correct as IS. simpl in IS.    
    repeat (rewrite IS; compile_typing (compile_WT)). clear IS.
    unfold compose_super.
    repeat rewrite_inPar.    
    repeat rewrite strip_one_l_in_eq.
    replace (ctx_to_matrix Γ f) with (Id 1 ⊗ ctx_to_matrix Γ f) by
        (Msimpl; easy).
    rewrite_inPar.    
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    simpl_rewrite init0_spec.
    apply subset_classical_merge in H as [S1 S2].
    simpl_rewrite (IHb1 Γ f false); trivial.
    replace (if ⌈b1 | f⌉ then true else false) with (⌈b1 | f⌉) by
        (destruct (⌈b1 | f⌉); easy).  
    listify_kron.
    simpl_rewrite (CNOT_at_spec (⌈b1 | f⌉) t (2 + ⟦Γ⟧) 1 0); trivial; try omega. 
    simpl.
    repeat rewrite_inPar.
    replace (@big_kron (S (S O)) (S (S O)) (ctx_to_mat_list Γ f)) with
        (ctx_to_matrix Γ f) by easy.
    simpl_rewrite IHb1; trivial.
    rewrite xorb_nilpotent. (* b1 cleared from ancilla for b2 *)
    simpl_rewrite IHb2; trivial.
    rewrite xorb_false_l.
    repeat simpl_rewrite strip_one_l_out_eq.
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    listify_kron.
    simpl_rewrite (CNOT_at_spec (⌈b2 | f⌉) (⌈b1 | f⌉ ⊕ t) (2 + ⟦Γ⟧) 1 0); trivial;
      try omega.
    simpl.
    rewrite_inPar.
    simpl_rewrite id_circ_spec; auto with wf_db.
    replace (@big_kron (S (S O)) (S (S O)) (ctx_to_mat_list Γ f)) with
        (ctx_to_matrix Γ f) by easy.
    simpl_rewrite IHb2; trivial.
    rewrite xorb_nilpotent. (* b2 cleared *)
    rewrite_inPar.
    simpl_rewrite strip_one_l_out_eq.
    rewrite_inPar.
    repeat simpl_rewrite id_circ_spec; auto with wf_db.
    simpl_rewrite assert0_spec.
    rewrite xorb_comm.
    rewrite (xorb_comm _ t).
    rewrite xorb_assoc.
    reflexivity.
Qed.
