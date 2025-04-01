
Require Import psem_of_sem_proof
               it_sems_core relational_logic.

Require Import array type expr gen_map warray_ sem_type sem_op_typed
               values varmap expr_facts low_memory syscall_sem psem_defs.
Require Import flag_combination sem_params.

Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance indirect_c.
Section PROOF.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : forall {wsw : WithSubWord}, semCallParams}.

Variable (p:prog) (ev:extra_val_t).

Notation gd := (p_globs p).

Notation vmap_n := (Vm.t (wsw:= nosubword)).
Notation vmap_s := (Vm.t (wsw:= withsubword)).

Notation estate_n := (estate (wsw:= nosubword)).
Notation estate_s := (estate (wsw:= withsubword)).

#[local]Open Scope vm_scope.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : RelEvent E0}.
(*
#[local] Instance SC_nosubword_withsubword : sem_call_2 :=
  sc2_full (wsw1:= nosubword) (wsw2:= withsubword).

Let RPreFeq : relPreF :=
  fun fn1 fn2 fs1 fs2 =>
    fn1 = fn2 /\ fs1 = fs2.

Let RPostFeq : relPostF :=
  fun fn1 fn2 fs1 fs2 fr1 fr2 =>
    fr1 = fr2.
*)

Lemma wrequiv_sim_expr e :
  wrequiv estate_sim ((sem_pexpr true gd)^~ e) ((sem_pexpr true gd)^~ e) eq.
Proof. move=> s1 s2 v1 hsim he; have := sem_pexpr_sim hsim he; eauto. Qed.

Lemma wrequiv_sim_exprs es :
  wrequiv estate_sim ((sem_pexprs true gd)^~ es) ((sem_pexprs true gd)^~ es) eq.
Proof. move=> s1 s2 v1 hsim he; have := sem_pexprs_sim hsim he; eauto. Qed.

Lemma wrequiv_sim_lval x v :
   wrequiv estate_sim (λ s1 : estate_n, write_lval true gd x v s1)
                     (λ s2 : estate_s, write_lval true gd x v s2) estate_sim.
Proof. move=> s1 s2 s1' hsim hw; have [?[]]:= write_lval_sim hsim hw; eauto. Qed.

Lemma wrequiv_sim_lvals xs vs :
   wrequiv estate_sim (λ s1 : estate_n, write_lvals true gd s1 xs vs)
     (λ s2 : estate_s, write_lvals true gd s2 xs vs) estate_sim.
Proof. move=> s1 s2 s1' hsim hw; have [?[]]:= write_lvals_sim hsim hw; eauto. Qed.

Lemma wrequiv_sim_upd fs xs:
  wrequiv estate_sim (upd_estate true gd xs fs) (upd_estate true gd xs fs) estate_sim.
Proof. by move=> s1 s2 s1' hsim; apply wrequiv_sim_lvals; case hsim. Qed.

#[local] Hint Resolve wrequiv_sim_expr wrequiv_sim_exprs wrequiv_sim_lvals wrequiv_sim_upd wrequiv_sim_lval : core.

Notation wiequiv_f := (wequiv_f (sem_F1 := sem_fun_full (wsw:=nosubword)) (sem_F2:= sem_fun_full (wsw:=withsubword))).

Lemma psem_call :
  (forall scs1 scs2 mem1 mem2 o ves vs,
    exec_syscall (wsw:= nosubword)   scs1 mem1 o ves = ok (scs2, mem2, vs) ->
    exec_syscall (wsw:= withsubword) scs1 mem1 o ves = ok (scs2, mem2, vs)) ->

  (forall fd scs mem s,
    init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init |} = ok s ->
    exists2 s',
      init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init |} = ok s' &
      estate_sim s s') ->

  (forall fd mem, finalize (wsw:= nosubword) (f_extra fd) mem = finalize (wsw:= withsubword) (f_extra fd) mem) ->

  forall fn,
    wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
move=> hsyscall hinitstate hfinal fn.
apply wequiv_fun_ind => hrec {fn}.
move=> fn _ fs _ [<- <-] fd ->; exists fd => //.
exists estate_sim, estate_sim => s1 hinit.
have : exists2 s2 : estate_s, initialize_funcall p ev fd fs = ok s2 & estate_sim s1 s2.
+ move: hinit; rewrite /initialize_funcall.
  t_xrbindP => > -> s1' /hinitstate [s2'] /= -> hs hw.
  have [s2'' [] /=]:= write_vars_sim hs hw; eauto.
move=> [s2 h1 h2]; exists s2; split => //; last first.
+ move=> s1' s2' fs1' [hscs hmem hvm]; rewrite /finalize_funcall.
  t_xrbindP => vs.
  rewrite /get_var_is (mapM_ext (λ (x : var_i) _, get_var_sim hvm x)) hfinal hscs hmem => -> /=.
  move=> ? -> <- /=; eauto.
 set Pi := fun (i:instr) => wequiv_rec (wsw1:= nosubword) (wsw2:= withsubword)
                p p ev ev eq_spec estate_sim [::i] [::i] estate_sim.
 set Pr := fun (i:instr_r) => forall ii, Pi (MkI ii i).
 set Pc := fun (c:cmd) => wequiv_rec (wsw1:= nosubword) (wsw2:= withsubword)
                          p p ev ev eq_spec estate_sim c c estate_sim.
 move=> {fn fs hinit h1 h2 s1 s2 hfinal hinitstate}.
 apply (cmd_rect (Pr := Pr) (Pi:=Pi) (Pc:=Pc)) => // {fd}.
 + by apply wequiv_nil.
 + by move=> i c; apply wequiv_cons.
 + by move=> x tg ty e ii; apply wequiv_assgn_eq.
 + by move=> xs t o es ii; apply wequiv_opn_eq.
 + move=> xs o es ii; apply wequiv_syscall_eq => //.
   + by move=> > [].
   move=> [???] [???] ? [<- <- <-]; rewrite /fexec_syscall /=.
   by t_xrbindP => -[[??]?] /= /hsyscall -> [<-] /=; eauto.
 + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_eq => // -[].
 + move=> j d lo hi c hc ii; apply wequiv_for_eq with estate_sim => //.
   move=> i s1 s2 s1' hsim hw; have [?[]]:= write_var_sim hsim hw; eauto.
 + by move=> al c e inf c' hc hc' ii; apply wequiv_while_eq.
 move=> xs f es ii; apply wequiv_call with  (rpreF (eS:=eq_spec)) (rpostF (eS:=eq_spec)) eq => //.
 + by rewrite /mk_fstate => > [<- <- _] <-.
 + by apply hrec.
 move=> fs1 fs2 fr _ _ <-.
 by apply wrequiv_sim_upd.
Qed.

End PROOF.

Section INSTANCE.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : RelEvent E0}.

Notation wiequiv_f := (wequiv_f (sem_F1 := sem_fun_full (wsw:=nosubword)) (sem_F2:= sem_fun_full (wsw:=withsubword))).

Lemma psem_call_u (p:uprog) ev fn :
  wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply (psem_call (sCP := fun wsw => sCP_unit (wsw := wsw))) => //=.
  move=> _ ??? [<-]; eexists; eauto.
  by split => //= x; rewrite !Vm.initP.
Qed.

Lemma psem_call_s (p:sprog) ev fn :
  wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply (psem_call (sCP := fun wsw => sCP_stack (wsw := wsw))) => //=.
  clear.
  move=> fd scs mem s.
  rewrite /init_stk_state; t_xrbindP => mem' -> hw.
  have hsim : estate_sim {| escs := scs; emem := mem'; evm := Vm.init |}
                    {| escs := scs; emem := mem'; evm := Vm.init |}.
  + by split => //= ?; rewrite !Vm.initP.
  have [s' [hsim' hw']] := write_vars_sim hsim hw.
  by exists s'.
Qed.

End INSTANCE.
