Inductive Gate : Set := 
  | H | σx | σy | σz | CNot 
  | init0 | init1 | new0 | new1 | meas | discard
  | control : Gate -> Gate
  | bit_control : Gate -> Gate
  | transpose : Gate -> Gate
.

Inductive Unitary : Gate -> Set := 
  | U_H : Unitary H | U_σx : Unitary σx | U_σy : Unitary σy | U_σz : Unitary σz 
  | U_CNot : Unitary CNot 
  | U_control : forall g, Unitary g -> Unitary (control g)
  | U_bit_control : forall g, Unitary g -> Unitary (bit_control g)
  | U_transpose : forall g, Unitary g -> Unitary (transpose g)
.

(* We have GateWType guarantee that only unitary gates are controlled/transposed *)
Inductive GateWType : Gate -> WType -> WType -> Set :=
  | H_type: (GateWType H Qubit Qubit)
  | σx_type : (GateWType σx Qubit Qubit) 
  | σy_type : (GateWType σy Qubit Qubit) 
  | σz_type : (GateWType σz Qubit Qubit) 
  | CNot_type : (GateWType CNot (Qubit ⊗ Qubit) (Qubit ⊗ Qubit))
  | init0_type : (GateWType init0 One Qubit)
  | init1_type : (GateWType init1 One Qubit)
  | new0_type : (GateWType new0 One Bit)
  | new1_type : (GateWType new1 One Bit)
  | meas_type : (GateWType meas Qubit Bit)
  | discard_type : (GateWType discard Bit One)
  | control_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (control g) (Qubit⊗W) (Qubit⊗W)
  | bit_control_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (bit_control g) (Bit⊗W) (Bit⊗W)
  | transpose_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (transpose g) W W
. 

Inductive Circuit  :=
| output : Pat -> Circuit
| gate : Gate -> Pat -> Pat -> Circuit -> Circuit (* 1st pat is input, 2nd output *)
| lift : forall {w:WType}, Pat -> (interpret w -> Circuit) -> Circuit
.

Notation "p2 <- 'gate' g p1 ; C" := (gate g p1 p2) (at level 10) : circ_scope.
Delimit Scope circ_scope with circ.

(* Lift notation? *)


Inductive WF_Circuit : Ctx -> Circuit -> WType -> Set :=
| wf_output : forall ctx p w, WF_Pat ctx p w -> WF_Circuit ctx (output p) w
| wf_gate   : forall ctx ctx1 ctx2 ctx1' ctx2' g p1 p2 c w1 w2 w,
              MergeCtx ctx1 ctx ctx1'
           -> MergeCtx ctx2 ctx ctx2'
           -> GateWType g w1 w2
           -> WF_Pat ctx1 p1 w1
           -> WF_Pat ctx2 p2 w2
           -> WF_Circuit ctx2' c w
           -> WF_Circuit ctx1' (gate g p1 p2 c) w
| wf_lift   : forall ctx1 ctx2 ctx p w w' f,
              MergeCtx ctx1 ctx2 ctx
           -> WF_Pat ctx1 p w
           -> (forall (x:interpret w), WF_Circuit ctx2 (f x) w')
           -> WF_Circuit ctx (lift p f) w'
.







Fixpoint subst σ (c : Circuit) : Circuit :=
  match c with
  | output p0 => output (subst_pat σ p0)
  | gate g p1 p2 c' => gate g (subst_pat σ p1) p2 (subst σ c') 
  | lift p0 f => lift (subst_pat σ p0) (fun x => subst σ (f x))
  end.

Inductive eq_pat : Pat -> Pat -> Set :=
| eq_var : forall x, eq_pat (var x) (var x)
| eq_unit : eq_pat unit unit
| eq_pair : forall {p1 p2 p1' p2'},
            eq_pat p1 p1' -> eq_pat p2 p2' -> eq_pat (p1,p2) (p1',p2')
.
Inductive eq_option : option Pat -> option Pat -> Set :=
| eq_None : eq_option None None
| eq_Some : forall {a1 a2}, eq_pat a1 a2 -> eq_option (Some a1) (Some a2)
.
Definition consistent_subst (σ : Substitution) w W : Set := 
    {p0 : Pat & { Ω : Ctx & Datatypes.prod (eq_option (σ w) (Some p0)) 
                                           (WF_Pat Ω p0 W) }}.

Definition shift_down {a} (σ : Var -> a) (x : Var) : a := σ (x+1).


(*    forall w W, index Ω w = Some W -> consistent_subst pf w W. *)
Inductive consistent_ctx (σ : Substitution) : Ctx -> Set :=
| consistent_nil  : consistent_ctx σ []
| consistent_None : forall {Ω}, consistent_ctx (shift_down σ) Ω 
                 -> consistent_ctx σ (None :: Ω)
| consistent_Some : forall {W Ω}, 
                    consistent_subst σ 0 W
                 -> consistent_ctx (shift_down σ) Ω
                 -> consistent_ctx σ (Some W :: Ω)
.

Fixpoint subst_ctx {σ} {Ω : Ctx} (pf : consistent_ctx σ Ω) : Ctx :=
  match pf with
  | consistent_nil _ => []
  | consistent_None _ pf'   => None :: subst_ctx pf'
  | consistent_Some _ (existT _ p (existT _ Ω _)) pf' => Ω ++ subst_ctx pf'
  end.

Open Scope default_scope.
Lemma consistent_merge1 : forall σ Γ1 Γ2 Γ, MergeCtx Γ1 Γ2 Γ -> consistent_ctx σ Γ
                     -> consistent_ctx σ Γ1.
Admitted.
Lemma consistent_merge2 : forall σ Γ1 Γ2 Γ, MergeCtx Γ1 Γ2 Γ -> consistent_ctx σ Γ
                     -> consistent_ctx σ Γ2.
Admitted.
Lemma consistent_merge  : forall σ Γ1 Γ2 Γ
                          (pf : consistent_ctx σ Γ)
                          (pf1 : consistent_ctx σ Γ1)
                          (pf2 : consistent_ctx σ Γ2),
               MergeCtx Γ1 Γ2 Γ 
            -> MergeCtx (subst_ctx pf1) (subst_ctx pf2) (subst_ctx pf).
Admitted.
Close Scope default_scope.


Lemma consistent_var : forall σ Ω (pf : consistent_ctx σ Ω) x w,
      SingletonCtx x w Ω
   -> WF_Pat (subst_ctx pf) (subst_pat σ (var x)) w.
Proof.
  intros σ Ω pf x w pfS; revert σ pf. induction pfS; intros σ pf; simpl.
  - inversion pf; subst. unfold consistent_subst in H2.
    destruct H2 as [p [Ω [H4 H5]]].
    inversion H4; subst. admit.
  - inversion pf; subst.
    specialize IHpfS with (shift_down σ) H1.
    simpl in IHpfS.
    unfold shift_down in *.
    admit.
Admitted.

Lemma wf_subst_pat : forall Ω p W,
                     WF_Pat Ω p W
                  -> forall σ {pf : consistent_ctx σ Ω},
                     WF_Pat (subst_ctx pf) (subst_pat σ p) W.
Proof.
  induction 1; intros σ pf; simpl.
  - apply consistent_var; auto.
  - revert e; destruct pf; inversion 1. simpl. constructor. constructor.
  - eapply wf_pair; [ | apply IHWF_Pat1 | apply IHWF_Pat2]; auto.
    eapply consistent_merge; auto.
    Unshelve. eapply consistent_merge1; eauto.
    Unshelve. eapply consistent_merge2; eauto.
Qed.

Lemma wf_subst : forall Ω c W,
                 WF_Circuit Ω c W
              -> forall σ (pf : consistent_ctx σ Ω),
                 WF_Circuit (subst_ctx pf) (subst σ c) W.
Proof.
  induction 1 as [Ω p W | |]; intros σ pf; simpl.
  - constructor. apply wf_subst_pat. auto.
  - eapply wf_gate with (w1 := w1) (w2 := w2); auto.
    Focus 3. apply wf_subst_pat. exact w0.
    Focus 3. exact w3.
    * apply consistent_merge. exact m.
    * admit.
  - eapply wf_lift. 
    Focus 2. apply wf_subst_pat. exact w0.
    Focus 2. intro x. apply H0. apply consistent_merge. auto.
Admitted.



Inductive Boxed_Circ : WType -> WType -> Set := 
| box : forall {W1 W2 ctx} p c {pf : Concrete p W1}
               {wf_p : WF_Pat ctx p W1} {wf_c : WF_Circuit ctx c W2}, 
               Boxed_Circ W1 W2
.
(*Arguments box {w1} {w2} _ p c _ _. Check subst.*)

Definition subst_pat' {W} (p' : Pat) (p : Pat) {pf : Concrete p W} {pf' : Concrete p' W} : p' ≼ p.
Proof.
    revert p' pf'.
    induction pf; intros p' pf'.
    - constructor.
    - constructor.
    - inversion pf'. constructor.
    - inversion pf'; subst. constructor. apply IHpf1; auto. apply IHpf2; auto.
Defined.

Definition subst' {W} (p' : Pat) (p : Pat) 
                          {pf : Concrete p W} {pf' : Concrete p' W}
                          (c : Circuit) : Circuit.
  refine (subst (subst_var (subst_pat' p' p)) c ).
  exact pf. exact pf'.
Defined.

Definition unbox {W1 W2} (c : Boxed_Circ W1 W2) p' {pf' : Concrete p' W1} 
                   : Circuit.
  revert p' pf'.
  destruct c; intros p' pf'.
  eapply (@subst' W1 p' p _ _ c).
  Unshelve. auto. auto.
Defined.

Lemma wf_subst' : 

Lemma wf_unbox : forall Γ W1 W2 p (c : Boxed_Circ W1 W2) {pf : Concrete p W1},
                 WF_Pat Γ p W1 -> WF_Circuit Γ (@unbox W1 W2 c p pf) W2.
Proof.
  intros Γ W1 W2 p c pf wf_p.
  revert Γ p pf wf_p.
  destruct c; intros Γ p' pf' wf_p'.
  simpl.
  
Qed.


Fixpoint compose  (p : Pat) (c:Circuit) (c' : Circuit) : Circuit :=
  match c with
    | output p' => subst p' p c'
    | gate p2 g p1 c => gate p2 g p1 (compose p c c')
    | lift p' f => lift p' (fun x => compose p (f x) c')
  end.

Lemma wf_compose : forall ctx ctx1 ctx2 ctx1' ctx2' p c c' w w',
      MergeCtx ctx1 ctx ctx1'
   -> MergeCtx ctx2 ctx ctx2'
   -> WF_Circuit ctx1 c w
   -> WF_Pat ctx2 p w
   -> WF_Circuit ctx2' c' w'
   -> WF_Circuit ctx1' (compose p c c') w'.
Admitted.
