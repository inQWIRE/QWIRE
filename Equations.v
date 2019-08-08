Require Import HOASCircuits.
Require Import Prelim.
Require Import DBCircuits.
Require Import Denotation.
Require Import TypeChecking.
Require Import HOASLib.
Require Import SemanticLib.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

(* Note: All of these circuits should in principle end with an arbitrary circuit -
         here I'm just outputting the mentioned (qu)bits *)

Open Scope circ_scope.  
  
(** Equality 1: X; meas = meas; NOT **)

Definition X_meas : Box Qubit Bit :=
  box_ q ⇒ meas $ _X $ q.
Lemma X_meas_WT : Typed_Box X_meas.
Proof. type_check. Qed.

Definition meas_NOT : Box Qubit Bit := 
  box_ q ⇒ BNOT $ meas $ q.

Lemma meas_NOT_WT : Typed_Box meas_NOT.
Proof. type_check. Qed.

Lemma NOT_meas_comm : X_meas ≡ meas_NOT.
Proof.
  matrix_denote.
  intros ρ b WF.
  Msimpl.
  rewrite Mmult_plus_dist_l.
  rewrite Mmult_plus_dist_r.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite (Mmult_assoc _ ⟨0∣ σx).
  repeat rewrite (Mmult_assoc _ ⟨1∣ σx).
  repeat rewrite (Mmult_assoc _ σx ∣0⟩).
  repeat rewrite (Mmult_assoc _ σx ∣1⟩).
  Msimpl.
  rewrite Mplus_comm.
  reflexivity.
Qed.

(** Equality 2: meas x; lift x; if x then U else V = alt x U V; meas-discard x **) 

Definition lift_UV {W} (U V : Unitary W) : Box (Qubit ⊗ W) W :=
  box_ qr ⇒ 
    let_ (q,r) ← output qr;
    let_ b ← meas $ q;
    lift_ x ← b;
    if x then U $ r else V $ r.
Lemma lift_UV_WT : forall W (U V : Unitary W), Typed_Box (lift_UV U V).
Proof. type_check. Qed.

Definition alternate {W} (U V : Unitary W) : Box (Qubit ⊗ W) (Qubit ⊗ W) :=
  box_ cx ⇒ 
    let_ (c,x) ← ctrl U $ cx;
    let_ c     ← _X $ c;
    let_ (c,x) ← ctrl V $ (c,x);
    (_X $ c,x).
Lemma alternate_WT : forall W (U V : Unitary W), Typed_Box (alternate U V).           
Proof. type_check. Qed.

Definition alt_UV {W} (U V : Unitary W) : Box (Qubit ⊗ W) W :=     
  box_ (q,r) ⇒ 
    let_ (q,r) ← alternate U V $ (q,r);
    let_ ()    ← discard $ meas $ q;
    output r.
Lemma alt_UV_WT : forall W (U V : Unitary W), Typed_Box (alt_UV U V).  
Proof. type_check. Qed.

(* Probably want a lemma about alternate's behavior *)
Proposition lift_alternate_eq : forall W (U V : Unitary W), lift_UV U V ≡ alt_UV U V.
Proof.
  intros W U V ρ WF safe.
  matrix_denote.  
Abort.

(** Equality 3: U; meas-discard = meas-discard **)

Definition U_meas_discard (U : Unitary Qubit) := 
  box_ q ⇒ discard $ meas $ U $ q.
Lemma U_meas_discard_WT : forall (U : Unitary Qubit), Typed_Box (U_meas_discard U).  
Proof. type_check. Qed.

Definition meas_discard := 
  box_ q ⇒ discard $ meas $ q.
Lemma meas_discard_WT : Typed_Box meas_discard.  
Proof. type_check. Qed.

Lemma U_meas_eq_meas : forall U, U_meas_discard U ≡ meas_discard.
Proof.
  intros U ρ safe WF.
  matrix_denote.
  specialize (unitary_gate_unitary U); intros [WFU UU].
  simpl in *. 
  Msimpl.
  rewrite Mmult_plus_dist_l.
  rewrite Mmult_plus_dist_r.
  solve_matrix.
  remember (denote_unitary U) as u.
  repeat rewrite Cmult_plus_dist_r.
  set (u00 := u 0%nat 0%nat). set (u01 := u 0%nat 1%nat).
  set (u10 := u 1%nat 0%nat). set (u11 := u 1%nat 1%nat).
  set (ρ00 := ρ 0%nat 0%nat). set (ρ01 := ρ 0%nat 1%nat).
  set (ρ10 := ρ 1%nat 0%nat). set (ρ11 := ρ 1%nat 1%nat).
  repeat rewrite Cplus_assoc.
  repeat rewrite (Cmult_comm _ ρ00), (Cmult_comm _ ρ01), 
                 (Cmult_comm _ ρ10), (Cmult_comm _ ρ11).
  set (c000 := ρ00 * u00 * u00 ^* ). set (c001 := ρ00 * u10 * u10 ^* ).
  set (c010 := ρ01 * u00 * u01 ^* ). set (c011 := ρ01 * u10 * u11 ^* ).
  set (c100 := ρ10 * u01 * u00 ^* ). set (c101 := ρ10 * u11 * u10 ^* ).
  set (c110 := ρ11 * u01 * u01 ^* ). set (c111 := ρ11 * u11 * u11 ^* ).
  repeat rewrite <- Cplus_assoc. rewrite (Cplus_comm c110).
  repeat rewrite <- Cplus_assoc. rewrite (Cplus_comm c010).
  repeat rewrite <- Cplus_assoc. rewrite (Cplus_comm c100).
  repeat rewrite Cplus_assoc.
  replace (c000 + c001) with ρ00.
  Focus 2.
    unfold c000, c001.
    repeat rewrite <- Cmult_assoc.
    rewrite <- Cmult_plus_dist_l.
    assert (H : ((u † × u) 0 0 = I 2 0 0)%nat) by (rewrite <- UU; easy).
    unfold Mmult, I, adjoint in H. simpl in H.
    autorewrite with C_db in H.
    rewrite Cmult_comm in H.
    rewrite (Cmult_comm ((u 1%nat 0%nat) ^* )) in H.
    unfold u00, u10.
    rewrite H.                 
    lca.
  rewrite <- 3 Cplus_assoc.
  rewrite (Cplus_assoc c111).
  replace (c111 + c110) with ρ11.
  Focus 2.
    unfold c111, c110.
    repeat rewrite <- Cmult_assoc.
    rewrite <- Cmult_plus_dist_l.
    assert (H: ((u † × u) 1 1 = I 2 1 1)%nat) by (rewrite <- UU; easy).
    unfold Mmult, I, adjoint in H. simpl in H.
    autorewrite with C_db in H.
    rewrite Cmult_comm in H.
    rewrite Cplus_comm in H.
    rewrite Cmult_comm in H.
    unfold u11, u01. 
    rewrite H.                 
    lca.
  rewrite (Cplus_comm ρ11).
  rewrite <- Cplus_assoc.
  repeat rewrite (Cplus_assoc c011).
  replace (c011 + c010) with C0.
  Focus 2.
    unfold c011, c010.
    repeat rewrite <- Cmult_assoc.
    rewrite <- Cmult_plus_dist_l.
    assert (H : ((u† × u) 1 0 = I 2 1 0)%nat)  by (rewrite <- UU; easy).
    unfold Mmult, I, adjoint in H. simpl in H.
    autorewrite with C_db in H.
    rewrite Cmult_comm in H.
    rewrite Cplus_comm in H.
    rewrite Cmult_comm in H.
    unfold u00, u01, u10, u11.
    rewrite H.                 
    lca.
  rewrite Cplus_0_l.
  rewrite <- Cplus_assoc.
  repeat rewrite (Cplus_assoc c101).
  replace (c101 + c100) with C0.
  Focus 2.
    unfold c101, c100.
    repeat rewrite <- Cmult_assoc.
    rewrite <- Cmult_plus_dist_l.
    assert (H : ((u † × u ) 0 1 = I 2 0 1)%nat) by (rewrite <- UU; easy).
    unfold Mmult, I, adjoint in H. simpl in H.
    autorewrite with C_db in H.
    rewrite Cmult_comm in H.
    rewrite Cplus_comm in H.
    rewrite Cmult_comm in H.
    unfold u00, u01, u10, u11.
    rewrite H.                 
    lca.
  rewrite Cplus_0_l.
  reflexivity.
Qed.
       
(** Equality 4: init; meas = new **)


Definition init_meas (b : bool) : Box One Bit := 
  box_ () ⇒ 
    let_ q ← unbox (init b) ();
    let_ b ← meas $ q;
    output b. 
Lemma init_meas_WT : forall b, Typed_Box (init_meas b).
Proof. destruct b; type_check. Qed.

Definition init_meas_new : forall b, init_meas b ≡ new b.
Proof.
  destruct b; simpl.
  - repeat (autounfold with den_db; intros; simpl).
    Msimpl; solve_matrix.
  - repeat (autounfold with den_db; intros; simpl).
    Msimpl; solve_matrix.
Qed.

(** Equality 5: init b; alt b U V = init b; if b then U else V **) 

Definition init_alt {W}  (b : bool) (U V : Unitary W) : Box W (Qubit ⊗ W) := 
  box_ qs ⇒ 
    let_ q   ← init b $ ();
    let_ (q,qs) ← alternate U V $ (q,qs);
    (q,qs).
Lemma init_alt_WT : forall W b (U V : Unitary W), Typed_Box (init_alt b U V).
Proof. type_check. Qed.

Definition init_if {W}  (b : bool) (U V : Unitary W) : Box W (Qubit ⊗ W) := 
  box_ qs ⇒ 
    let_ q   ←init b $ ();
    let_ qs ← (if b then U else V) $ qs;
    (q,qs).
Lemma init_if_WT : forall W b (U V : Unitary W), Typed_Box (init_if b U V).
Proof. type_check. Qed.

Lemma init_if_true_qubit : forall (U V : Unitary Qubit) ρ,
  WF_Matrix ρ -> 
  ⟦init_if true U V⟧ ρ = (∣1⟩ ⊗ I 2 )%M × (⟦U⟧ × ρ × (⟦U⟧†)) × (⟨1∣ ⊗ I 2)%M. 
Proof.
  intros U V ρ WF. simpl in *.
  matrix_denote.
  Msimpl.
  specialize (WF_Matrix_U U) as WFU. simpl in WFU.
  solve_matrix.
Qed.  
  
Lemma init_if_false_qubit : forall (U V : Unitary Qubit) ρ,
  WF_Matrix ρ -> 
  ⟦init_if false U V⟧ ρ = (∣0⟩ ⊗ I 2 )%M × (⟦V⟧ × ρ × (⟦V⟧†)) × (⟨0∣ ⊗ I 2)%M. 
Proof.
  intros U V ρ WF. simpl in *.
  matrix_denote.
  Msimpl.
  specialize (WF_Matrix_U V) as WFV. simpl in WFV.
  solve_matrix.
Qed.  

Lemma init_alt_if_qubit : forall b (U V : Unitary Qubit), init_alt b U V ≡ init_if b U V.
Proof.
  destruct b; simpl; intros U V ρ b WF.
  - matrix_denote. 
    match goal with 
    | [|- context[let (res, u) := ?exp in _]] => replace exp with (0%nat, [false; true], ⟦V⟧)%core
    end; [| dependent destruction V; easy]. 
    match goal with 
    | [|- context[let (res, u) := ?exp in _]] => replace exp with (0%nat, [false; true], ⟦U⟧)%core
    end; [| dependent destruction U; easy]. 
    specialize (WF_Matrix_U U) as WFU. 
    specialize (WF_Matrix_U V) as WFV.
    simpl in *.
    replace 4%nat with (2 * 2)%nat by easy. Msimpl.
    solve_matrix.
  - matrix_denote. 
    match goal with 
    | [|- context[let (res, u) := ?exp in _]] => replace exp with (0%nat, [false; true], ⟦V⟧)%core
    end; [| dependent destruction V; easy]. 
    match goal with 
    | [|- context[let (res, u) := ?exp in _]] => replace exp with (0%nat, [false; true], ⟦U⟧)%core
    end; [| dependent destruction U; easy]. 
    specialize (WF_Matrix_U U) as WFU. 
    specialize (WF_Matrix_U V) as WFV.
    simpl in *.
    replace 4%nat with (2 * 2)%nat by easy. Msimpl.
    solve_matrix.
Qed.

Proposition init_alt_if : forall W b (U V : Unitary W), init_alt b U V ≡ init_if b U V.
Proof.
  destruct b; simpl.
  - matrix_denote.    
Abort.

(** Equality 6: init b; X b = init ~b **) 

Definition init_X (b : bool) : Box One Qubit :=
  box_ () ⇒ _X $ init b $ ().
Lemma init_X_WT : forall b, Typed_Box (init_X b).
Proof. type_check. Qed.

Lemma init_X_init : forall b, init_X b ≡ init (negb b).
Proof.
  destruct b; simpl.
  - repeat (autounfold with den_db; intros; simpl).
    Msimpl.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
    repeat rewrite Mmult_assoc.
    Msimpl.
    reflexivity.    
  - repeat (autounfold with den_db; intros; simpl).
    Msimpl.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
    repeat rewrite Mmult_assoc.
    Msimpl.
    reflexivity.    
Qed.
  
(* Additional Equalities *)



(** Equation 7: lift x <- b; new x = id b **)


Lemma new_WT : forall b, Typed_Box (new b).
Proof. destruct b; type_check. Qed.

Definition lift_new : Box Bit Bit :=
  box_ b ⇒ 
    lift_ x ← b; 
    new x $ ().
Lemma lift_new_WT : Typed_Box lift_new.
Proof. type_check. Qed.

Hint Unfold Splus : den_db.

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Lemma lift_new_new : forall (ρ : Density 2), WF_Matrix ρ -> 
                                        Classical ρ -> 
                                        ⟦lift_new⟧ ρ = ⟦@id_circ Bit⟧ ρ.
Proof. 
  intros ρ M C.
  matrix_denote.
  Msimpl.
  solve_matrix.
  rewrite C; trivial; lia.
  rewrite C; trivial; lia.
Qed.  

(** Equation 7': meas q; lift x <- p; new x = meas q **)

Definition meas_lift_new : Box Qubit Bit :=
  box_ q ⇒ 
    let_ b ← meas $ q;
    lift_ x ← b; 
    new x $ ().
Lemma meas_lift_new_WT : Typed_Box meas_lift_new.
Proof. type_check. Qed.

Lemma meas_lift_new_new : meas_lift_new ≡ boxed_gate meas.
Proof. 
  intros ρ safe WF.
  matrix_denote.
  Msimpl.
  solve_matrix.
Qed.

(*********************************************)
(* "Automated optimization of large quantum  *)
(*    circuits with continuous parameters"   *)
(*********************************************)

(* Hadamard elimination *)

Lemma super_super : forall m n o (U : Matrix o n) (V : Matrix n m) (ρ : Square m) , 
  super U (super V ρ) = super (U × V) ρ.
Proof.
  intros m n o U V ρ.
  unfold super.
  Msimpl.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma super_eq : forall m n (U U' : Matrix m n) (ρ ρ' : Square n), 
  U = U' ->
  ρ = ρ' ->
  super U ρ = super U' ρ'.
Proof. intros; subst; easy. Qed.

Definition HSH := box_ q ⇒ _H $ _S $ _H $ q.

Definition SdHSd := box_ q ⇒ trans _S $ _H $ trans _S $ q. 

Proposition HSH_SdHSd_eq : HSH ≡ SdHSd.
Proof.
  intros ρ safe WF.
  repeat (autounfold with vector_den_db; simpl).
  repeat rewrite super_super.
  specialize (WF_Matrix_U _S) as WFS.
  specialize (WF_Matrix_U (trans _S)) as WFSd.

(*
  apply super_eq; trivial.
  Msimpl.
  solve_matrix.
  (* This doesn't quite work, since their P is only our S up to an
     "unimportant global phase" since they use R_z gates 
     (specifically, the coefficient is e^i*pi/4) 
     I wonder if density matrix form helps...
*)
*)

  Msimpl.
  unfold super.
  solve_matrix.
  - rewrite eulers_identity2.
    unfold Cexp.
    rewrite cos_neg, sin_neg.
    rewrite cos_PI2, sin_PI2.
    replace (0,-1)%core with (-Ci) by lca.
    repeat rewrite Cmult_plus_dist_r.

    (* maybe? If so, it's a mess *)
Abort.

Definition HH_CNOT_HH := box_ (q1,q2) ⇒ (_H ∥ _H) $ CNOT $ (_H ∥ _H) $ (q1, q2). 

(* Just `CNOT_at (1,0)` *)
Definition NOTC := box_ (q1,q2) ⇒ let_ (q2, q1) ← CNOT $ (q2, q1); (q1, q2).

Lemma HH_CNOT_HH_eq_NOTC : HH_CNOT_HH ≡ NOTC.
Proof.
  intros ρ safe WF.
  repeat (autounfold with vector_den_db; simpl).
  repeat rewrite super_super.
  Msimpl.
  apply super_eq; trivial.
  solve_matrix.
  all: repeat rewrite <- Cmult_assoc;
       autorewrite with C_db;
       repeat (rewrite (Cmult_assoc 2 (/2)); autorewrite with C_db);
       easy.
Qed.  

(***********************)
(* Assorted Equalities *)
(***********************)

(** HZH Equality **)

Definition HZH : Box Qubit Qubit := 
  box_ q ⇒ _H $ _Z $ _H $ q.

Lemma HZH_X : HZH ≡ _X.
Proof.
  matrix_denote.
  intros.
  Msimpl.
  repeat rewrite <- Mmult_assoc.
  rewrite (Mmult_assoc _ _ hadamard).
  rewrite (Mmult_assoc _ hadamard).
  rewrite <- (Mmult_assoc hadamard).
  replace (hadamard × σz × hadamard) with σx. easy.
  crunch_matrix.
Qed.

